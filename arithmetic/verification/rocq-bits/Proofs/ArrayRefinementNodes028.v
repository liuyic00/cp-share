(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes027.
Lemma node_28000 (s : N.State) (i : N.Inputs) :
  R.v28000 (state s) (inputs i) = Zmod.unsigned (N.v28000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28000 s i)) at 1.
  unfold R.v28000, N.v28000.
  unfold R.v16484, N.v16484.
  rewrite ?node_27999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28001 (s : N.State) (i : N.Inputs) :
  R.v28001 (state s) (inputs i) = Zmod.unsigned (N.v28001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28001 s i)) at 1.
  unfold R.v28001, N.v28001.
  rewrite ?node_27996.
  rewrite ?node_28000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28002 (s : N.State) (i : N.Inputs) :
  R.v28002 (state s) (inputs i) = Zmod.unsigned (N.v28002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28002 s i)) at 1.
  unfold R.v28002, N.v28002.
  unfold R.v6, N.v6.
  rewrite ?node_28001.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28003 (s : N.State) (i : N.Inputs) :
  R.v28003 (state s) (inputs i) = Zmod.unsigned (N.v28003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28003 s i)) at 1.
  unfold R.v28003, N.v28003.
  rewrite ?node_10819.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28004 (s : N.State) (i : N.Inputs) :
  R.v28004 (state s) (inputs i) = Zmod.unsigned (N.v28004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28004 s i)) at 1.
  unfold R.v28004, N.v28004.
  unfold R.v6, N.v6.
  rewrite ?node_10984.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28005 (s : N.State) (i : N.Inputs) :
  R.v28005 (state s) (inputs i) = Zmod.unsigned (N.v28005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28005 s i)) at 1.
  unfold R.v28005, N.v28005.
  rewrite ?node_28003.
  rewrite ?node_28004.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28006 (s : N.State) (i : N.Inputs) :
  R.v28006 (state s) (inputs i) = Zmod.unsigned (N.v28006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28006 s i)) at 1.
  unfold R.v28006, N.v28006.
  rewrite ?node_28002.
  rewrite ?node_28005.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28007 (s : N.State) (i : N.Inputs) :
  R.v28007 (state s) (inputs i) = Zmod.unsigned (N.v28007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28007 s i)) at 1.
  unfold R.v28007, N.v28007.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28008 (s : N.State) (i : N.Inputs) :
  R.v28008 (state s) (inputs i) = Zmod.unsigned (N.v28008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28008 s i)) at 1.
  unfold R.v28008, N.v28008.
  rewrite ?node_10823.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28009 (s : N.State) (i : N.Inputs) :
  R.v28009 (state s) (inputs i) = Zmod.unsigned (N.v28009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28009 s i)) at 1.
  unfold R.v28009, N.v28009.
  unfold R.v6, N.v6.
  rewrite !state_r1252_nr_5F1252.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1252_nr_5F1252 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28010 (s : N.State) (i : N.Inputs) :
  R.v28010 (state s) (inputs i) = Zmod.unsigned (N.v28010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28010 s i)) at 1.
  unfold R.v28010, N.v28010.
  unfold R.v6, N.v6.
  rewrite ?node_10819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28011 (s : N.State) (i : N.Inputs) :
  R.v28011 (state s) (inputs i) = Zmod.unsigned (N.v28011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28011 s i)) at 1.
  unfold R.v28011, N.v28011.
  rewrite ?node_28009.
  rewrite ?node_28010.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28012 (s : N.State) (i : N.Inputs) :
  R.v28012 (state s) (inputs i) = Zmod.unsigned (N.v28012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28012 s i)) at 1.
  unfold R.v28012, N.v28012.
  unfold R.v16484, N.v16484.
  rewrite ?node_28011.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28013 (s : N.State) (i : N.Inputs) :
  R.v28013 (state s) (inputs i) = Zmod.unsigned (N.v28013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28013 s i)) at 1.
  unfold R.v28013, N.v28013.
  rewrite ?node_28008.
  rewrite ?node_28012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28014 (s : N.State) (i : N.Inputs) :
  R.v28014 (state s) (inputs i) = Zmod.unsigned (N.v28014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28014 s i)) at 1.
  unfold R.v28014, N.v28014.
  unfold R.v6, N.v6.
  rewrite ?node_28013.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28015 (s : N.State) (i : N.Inputs) :
  R.v28015 (state s) (inputs i) = Zmod.unsigned (N.v28015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28015 s i)) at 1.
  unfold R.v28015, N.v28015.
  rewrite ?node_10824.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28016 (s : N.State) (i : N.Inputs) :
  R.v28016 (state s) (inputs i) = Zmod.unsigned (N.v28016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28016 s i)) at 1.
  unfold R.v28016, N.v28016.
  unfold R.v6, N.v6.
  rewrite ?node_11035.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28017 (s : N.State) (i : N.Inputs) :
  R.v28017 (state s) (inputs i) = Zmod.unsigned (N.v28017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28017 s i)) at 1.
  unfold R.v28017, N.v28017.
  rewrite ?node_28015.
  rewrite ?node_28016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28018 (s : N.State) (i : N.Inputs) :
  R.v28018 (state s) (inputs i) = Zmod.unsigned (N.v28018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28018 s i)) at 1.
  unfold R.v28018, N.v28018.
  rewrite ?node_28014.
  rewrite ?node_28017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28019 (s : N.State) (i : N.Inputs) :
  R.v28019 (state s) (inputs i) = Zmod.unsigned (N.v28019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28019 s i)) at 1.
  unfold R.v28019, N.v28019.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28020 (s : N.State) (i : N.Inputs) :
  R.v28020 (state s) (inputs i) = Zmod.unsigned (N.v28020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28020 s i)) at 1.
  unfold R.v28020, N.v28020.
  rewrite ?node_10926.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28021 (s : N.State) (i : N.Inputs) :
  R.v28021 (state s) (inputs i) = Zmod.unsigned (N.v28021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28021 s i)) at 1.
  unfold R.v28021, N.v28021.
  unfold R.v16463, N.v16463.
  rewrite !state_r1257_nr_5F1257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1257_nr_5F1257 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28022 (s : N.State) (i : N.Inputs) :
  R.v28022 (state s) (inputs i) = Zmod.unsigned (N.v28022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28022 s i)) at 1.
  unfold R.v28022, N.v28022.
  unfold R.v16463, N.v16463.
  rewrite !state_r1256_nr_5F1256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1256_nr_5F1256 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28023 (s : N.State) (i : N.Inputs) :
  R.v28023 (state s) (inputs i) = Zmod.unsigned (N.v28023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28023 s i)) at 1.
  unfold R.v28023, N.v28023.
  unfold R.v6, N.v6.
  rewrite !state_r1255_nr_5F1255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1255_nr_5F1255 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28024 (s : N.State) (i : N.Inputs) :
  R.v28024 (state s) (inputs i) = Zmod.unsigned (N.v28024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28024 s i)) at 1.
  unfold R.v28024, N.v28024.
  unfold R.v6, N.v6.
  rewrite !state_r1254_nr_5F1254.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1254_nr_5F1254 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28025 (s : N.State) (i : N.Inputs) :
  R.v28025 (state s) (inputs i) = Zmod.unsigned (N.v28025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28025 s i)) at 1.
  unfold R.v28025, N.v28025.
  rewrite ?node_28023.
  rewrite ?node_28024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28026 (s : N.State) (i : N.Inputs) :
  R.v28026 (state s) (inputs i) = Zmod.unsigned (N.v28026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28026 s i)) at 1.
  unfold R.v28026, N.v28026.
  unfold R.v16484, N.v16484.
  rewrite ?node_28025.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28027 (s : N.State) (i : N.Inputs) :
  R.v28027 (state s) (inputs i) = Zmod.unsigned (N.v28027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28027 s i)) at 1.
  unfold R.v28027, N.v28027.
  rewrite ?node_28020.
  rewrite ?node_28021.
  rewrite ?node_28022.
  rewrite ?node_28026.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28028 (s : N.State) (i : N.Inputs) :
  R.v28028 (state s) (inputs i) = Zmod.unsigned (N.v28028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28028 s i)) at 1.
  unfold R.v28028, N.v28028.
  unfold R.v6, N.v6.
  rewrite ?node_28027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28029 (s : N.State) (i : N.Inputs) :
  R.v28029 (state s) (inputs i) = Zmod.unsigned (N.v28029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28029 s i)) at 1.
  unfold R.v28029, N.v28029.
  rewrite ?node_10927.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28030 (s : N.State) (i : N.Inputs) :
  R.v28030 (state s) (inputs i) = Zmod.unsigned (N.v28030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28030 s i)) at 1.
  unfold R.v28030, N.v28030.
  unfold R.v6, N.v6.
  rewrite ?node_11087.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28031 (s : N.State) (i : N.Inputs) :
  R.v28031 (state s) (inputs i) = Zmod.unsigned (N.v28031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28031 s i)) at 1.
  unfold R.v28031, N.v28031.
  unfold R.v6, N.v6.
  rewrite ?node_11155.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28032 (s : N.State) (i : N.Inputs) :
  R.v28032 (state s) (inputs i) = Zmod.unsigned (N.v28032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28032 s i)) at 1.
  unfold R.v28032, N.v28032.
  rewrite ?node_28029.
  rewrite ?node_28030.
  rewrite ?node_28031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28033 (s : N.State) (i : N.Inputs) :
  R.v28033 (state s) (inputs i) = Zmod.unsigned (N.v28033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28033 s i)) at 1.
  unfold R.v28033, N.v28033.
  rewrite ?node_28028.
  rewrite ?node_28032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28034 (s : N.State) (i : N.Inputs) :
  R.v28034 (state s) (inputs i) = Zmod.unsigned (N.v28034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28034 s i)) at 1.
  unfold R.v28034, N.v28034.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28035 (s : N.State) (i : N.Inputs) :
  R.v28035 (state s) (inputs i) = Zmod.unsigned (N.v28035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28035 s i)) at 1.
  unfold R.v28035, N.v28035.
  unfold R.v16463, N.v16463.
  rewrite !state_r1256_nr_5F1256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1256_nr_5F1256 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28036 (s : N.State) (i : N.Inputs) :
  R.v28036 (state s) (inputs i) = Zmod.unsigned (N.v28036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28036 s i)) at 1.
  unfold R.v28036, N.v28036.
  unfold R.v6, N.v6.
  rewrite !state_r1255_nr_5F1255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1255_nr_5F1255 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28037 (s : N.State) (i : N.Inputs) :
  R.v28037 (state s) (inputs i) = Zmod.unsigned (N.v28037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28037 s i)) at 1.
  unfold R.v28037, N.v28037.
  unfold R.v6, N.v6.
  rewrite !state_r1254_nr_5F1254.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1254_nr_5F1254 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28038 (s : N.State) (i : N.Inputs) :
  R.v28038 (state s) (inputs i) = Zmod.unsigned (N.v28038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28038 s i)) at 1.
  unfold R.v28038, N.v28038.
  rewrite ?node_28036.
  rewrite ?node_28037.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28039 (s : N.State) (i : N.Inputs) :
  R.v28039 (state s) (inputs i) = Zmod.unsigned (N.v28039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28039 s i)) at 1.
  unfold R.v28039, N.v28039.
  unfold R.v16484, N.v16484.
  rewrite ?node_28038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28040 (s : N.State) (i : N.Inputs) :
  R.v28040 (state s) (inputs i) = Zmod.unsigned (N.v28040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28040 s i)) at 1.
  unfold R.v28040, N.v28040.
  rewrite ?node_28035.
  rewrite ?node_28039.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28041 (s : N.State) (i : N.Inputs) :
  R.v28041 (state s) (inputs i) = Zmod.unsigned (N.v28041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28041 s i)) at 1.
  unfold R.v28041, N.v28041.
  unfold R.v6, N.v6.
  rewrite ?node_28040.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28042 (s : N.State) (i : N.Inputs) :
  R.v28042 (state s) (inputs i) = Zmod.unsigned (N.v28042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28042 s i)) at 1.
  unfold R.v28042, N.v28042.
  rewrite ?node_10922.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28043 (s : N.State) (i : N.Inputs) :
  R.v28043 (state s) (inputs i) = Zmod.unsigned (N.v28043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28043 s i)) at 1.
  unfold R.v28043, N.v28043.
  unfold R.v6, N.v6.
  rewrite ?node_11087.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28044 (s : N.State) (i : N.Inputs) :
  R.v28044 (state s) (inputs i) = Zmod.unsigned (N.v28044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28044 s i)) at 1.
  unfold R.v28044, N.v28044.
  rewrite ?node_28042.
  rewrite ?node_28043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28045 (s : N.State) (i : N.Inputs) :
  R.v28045 (state s) (inputs i) = Zmod.unsigned (N.v28045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28045 s i)) at 1.
  unfold R.v28045, N.v28045.
  rewrite ?node_28041.
  rewrite ?node_28044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28046 (s : N.State) (i : N.Inputs) :
  R.v28046 (state s) (inputs i) = Zmod.unsigned (N.v28046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28046 s i)) at 1.
  unfold R.v28046, N.v28046.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28047 (s : N.State) (i : N.Inputs) :
  R.v28047 (state s) (inputs i) = Zmod.unsigned (N.v28047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28047 s i)) at 1.
  unfold R.v28047, N.v28047.
  rewrite ?node_10926.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28048 (s : N.State) (i : N.Inputs) :
  R.v28048 (state s) (inputs i) = Zmod.unsigned (N.v28048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28048 s i)) at 1.
  unfold R.v28048, N.v28048.
  unfold R.v6, N.v6.
  rewrite !state_r1257_nr_5F1257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1257_nr_5F1257 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28049 (s : N.State) (i : N.Inputs) :
  R.v28049 (state s) (inputs i) = Zmod.unsigned (N.v28049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28049 s i)) at 1.
  unfold R.v28049, N.v28049.
  unfold R.v6, N.v6.
  rewrite ?node_10922.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28050 (s : N.State) (i : N.Inputs) :
  R.v28050 (state s) (inputs i) = Zmod.unsigned (N.v28050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28050 s i)) at 1.
  unfold R.v28050, N.v28050.
  rewrite ?node_28048.
  rewrite ?node_28049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28051 (s : N.State) (i : N.Inputs) :
  R.v28051 (state s) (inputs i) = Zmod.unsigned (N.v28051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28051 s i)) at 1.
  unfold R.v28051, N.v28051.
  unfold R.v16484, N.v16484.
  rewrite ?node_28050.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28052 (s : N.State) (i : N.Inputs) :
  R.v28052 (state s) (inputs i) = Zmod.unsigned (N.v28052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28052 s i)) at 1.
  unfold R.v28052, N.v28052.
  rewrite ?node_28047.
  rewrite ?node_28051.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28053 (s : N.State) (i : N.Inputs) :
  R.v28053 (state s) (inputs i) = Zmod.unsigned (N.v28053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28053 s i)) at 1.
  unfold R.v28053, N.v28053.
  unfold R.v6, N.v6.
  rewrite ?node_28052.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28054 (s : N.State) (i : N.Inputs) :
  R.v28054 (state s) (inputs i) = Zmod.unsigned (N.v28054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28054 s i)) at 1.
  unfold R.v28054, N.v28054.
  rewrite ?node_10927.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28055 (s : N.State) (i : N.Inputs) :
  R.v28055 (state s) (inputs i) = Zmod.unsigned (N.v28055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28055 s i)) at 1.
  unfold R.v28055, N.v28055.
  unfold R.v6, N.v6.
  rewrite ?node_11155.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28056 (s : N.State) (i : N.Inputs) :
  R.v28056 (state s) (inputs i) = Zmod.unsigned (N.v28056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28056 s i)) at 1.
  unfold R.v28056, N.v28056.
  rewrite ?node_28054.
  rewrite ?node_28055.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28057 (s : N.State) (i : N.Inputs) :
  R.v28057 (state s) (inputs i) = Zmod.unsigned (N.v28057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28057 s i)) at 1.
  unfold R.v28057, N.v28057.
  rewrite ?node_28053.
  rewrite ?node_28056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28058 (s : N.State) (i : N.Inputs) :
  R.v28058 (state s) (inputs i) = Zmod.unsigned (N.v28058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28058 s i)) at 1.
  unfold R.v28058, N.v28058.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28059 (s : N.State) (i : N.Inputs) :
  R.v28059 (state s) (inputs i) = Zmod.unsigned (N.v28059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28059 s i)) at 1.
  unfold R.v28059, N.v28059.
  rewrite ?node_10933.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28060 (s : N.State) (i : N.Inputs) :
  R.v28060 (state s) (inputs i) = Zmod.unsigned (N.v28060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28060 s i)) at 1.
  unfold R.v28060, N.v28060.
  unfold R.v16463, N.v16463.
  rewrite !state_r1261_nr_5F1261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1261_nr_5F1261 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28061 (s : N.State) (i : N.Inputs) :
  R.v28061 (state s) (inputs i) = Zmod.unsigned (N.v28061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28061 s i)) at 1.
  unfold R.v28061, N.v28061.
  unfold R.v16463, N.v16463.
  rewrite !state_r1260_nr_5F1260.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1260_nr_5F1260 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28062 (s : N.State) (i : N.Inputs) :
  R.v28062 (state s) (inputs i) = Zmod.unsigned (N.v28062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28062 s i)) at 1.
  unfold R.v28062, N.v28062.
  unfold R.v6, N.v6.
  rewrite !state_r1259_nr_5F1259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1259_nr_5F1259 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28063 (s : N.State) (i : N.Inputs) :
  R.v28063 (state s) (inputs i) = Zmod.unsigned (N.v28063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28063 s i)) at 1.
  unfold R.v28063, N.v28063.
  unfold R.v6, N.v6.
  rewrite !state_r1258_nr_5F1258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1258_nr_5F1258 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28064 (s : N.State) (i : N.Inputs) :
  R.v28064 (state s) (inputs i) = Zmod.unsigned (N.v28064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28064 s i)) at 1.
  unfold R.v28064, N.v28064.
  rewrite ?node_28062.
  rewrite ?node_28063.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28065 (s : N.State) (i : N.Inputs) :
  R.v28065 (state s) (inputs i) = Zmod.unsigned (N.v28065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28065 s i)) at 1.
  unfold R.v28065, N.v28065.
  unfold R.v16484, N.v16484.
  rewrite ?node_28064.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28066 (s : N.State) (i : N.Inputs) :
  R.v28066 (state s) (inputs i) = Zmod.unsigned (N.v28066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28066 s i)) at 1.
  unfold R.v28066, N.v28066.
  rewrite ?node_28059.
  rewrite ?node_28060.
  rewrite ?node_28061.
  rewrite ?node_28065.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28067 (s : N.State) (i : N.Inputs) :
  R.v28067 (state s) (inputs i) = Zmod.unsigned (N.v28067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28067 s i)) at 1.
  unfold R.v28067, N.v28067.
  unfold R.v6, N.v6.
  rewrite ?node_28066.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28068 (s : N.State) (i : N.Inputs) :
  R.v28068 (state s) (inputs i) = Zmod.unsigned (N.v28068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28068 s i)) at 1.
  unfold R.v28068, N.v28068.
  rewrite ?node_10934.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28069 (s : N.State) (i : N.Inputs) :
  R.v28069 (state s) (inputs i) = Zmod.unsigned (N.v28069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28069 s i)) at 1.
  unfold R.v28069, N.v28069.
  unfold R.v6, N.v6.
  rewrite ?node_11094.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28070 (s : N.State) (i : N.Inputs) :
  R.v28070 (state s) (inputs i) = Zmod.unsigned (N.v28070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28070 s i)) at 1.
  unfold R.v28070, N.v28070.
  unfold R.v6, N.v6.
  rewrite ?node_11158.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28071 (s : N.State) (i : N.Inputs) :
  R.v28071 (state s) (inputs i) = Zmod.unsigned (N.v28071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28071 s i)) at 1.
  unfold R.v28071, N.v28071.
  rewrite ?node_28068.
  rewrite ?node_28069.
  rewrite ?node_28070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28072 (s : N.State) (i : N.Inputs) :
  R.v28072 (state s) (inputs i) = Zmod.unsigned (N.v28072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28072 s i)) at 1.
  unfold R.v28072, N.v28072.
  rewrite ?node_28067.
  rewrite ?node_28071.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28073 (s : N.State) (i : N.Inputs) :
  R.v28073 (state s) (inputs i) = Zmod.unsigned (N.v28073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28073 s i)) at 1.
  unfold R.v28073, N.v28073.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28074 (s : N.State) (i : N.Inputs) :
  R.v28074 (state s) (inputs i) = Zmod.unsigned (N.v28074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28074 s i)) at 1.
  unfold R.v28074, N.v28074.
  unfold R.v16463, N.v16463.
  rewrite !state_r1260_nr_5F1260.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1260_nr_5F1260 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28075 (s : N.State) (i : N.Inputs) :
  R.v28075 (state s) (inputs i) = Zmod.unsigned (N.v28075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28075 s i)) at 1.
  unfold R.v28075, N.v28075.
  unfold R.v6, N.v6.
  rewrite !state_r1259_nr_5F1259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1259_nr_5F1259 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28076 (s : N.State) (i : N.Inputs) :
  R.v28076 (state s) (inputs i) = Zmod.unsigned (N.v28076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28076 s i)) at 1.
  unfold R.v28076, N.v28076.
  unfold R.v6, N.v6.
  rewrite !state_r1258_nr_5F1258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1258_nr_5F1258 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28077 (s : N.State) (i : N.Inputs) :
  R.v28077 (state s) (inputs i) = Zmod.unsigned (N.v28077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28077 s i)) at 1.
  unfold R.v28077, N.v28077.
  rewrite ?node_28075.
  rewrite ?node_28076.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28078 (s : N.State) (i : N.Inputs) :
  R.v28078 (state s) (inputs i) = Zmod.unsigned (N.v28078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28078 s i)) at 1.
  unfold R.v28078, N.v28078.
  unfold R.v16484, N.v16484.
  rewrite ?node_28077.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28079 (s : N.State) (i : N.Inputs) :
  R.v28079 (state s) (inputs i) = Zmod.unsigned (N.v28079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28079 s i)) at 1.
  unfold R.v28079, N.v28079.
  rewrite ?node_28074.
  rewrite ?node_28078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28080 (s : N.State) (i : N.Inputs) :
  R.v28080 (state s) (inputs i) = Zmod.unsigned (N.v28080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28080 s i)) at 1.
  unfold R.v28080, N.v28080.
  unfold R.v6, N.v6.
  rewrite ?node_28079.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28081 (s : N.State) (i : N.Inputs) :
  R.v28081 (state s) (inputs i) = Zmod.unsigned (N.v28081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28081 s i)) at 1.
  unfold R.v28081, N.v28081.
  rewrite ?node_10929.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28082 (s : N.State) (i : N.Inputs) :
  R.v28082 (state s) (inputs i) = Zmod.unsigned (N.v28082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28082 s i)) at 1.
  unfold R.v28082, N.v28082.
  unfold R.v6, N.v6.
  rewrite ?node_11094.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28083 (s : N.State) (i : N.Inputs) :
  R.v28083 (state s) (inputs i) = Zmod.unsigned (N.v28083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28083 s i)) at 1.
  unfold R.v28083, N.v28083.
  rewrite ?node_28081.
  rewrite ?node_28082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28084 (s : N.State) (i : N.Inputs) :
  R.v28084 (state s) (inputs i) = Zmod.unsigned (N.v28084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28084 s i)) at 1.
  unfold R.v28084, N.v28084.
  rewrite ?node_28080.
  rewrite ?node_28083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28085 (s : N.State) (i : N.Inputs) :
  R.v28085 (state s) (inputs i) = Zmod.unsigned (N.v28085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28085 s i)) at 1.
  unfold R.v28085, N.v28085.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28086 (s : N.State) (i : N.Inputs) :
  R.v28086 (state s) (inputs i) = Zmod.unsigned (N.v28086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28086 s i)) at 1.
  unfold R.v28086, N.v28086.
  rewrite ?node_10933.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28087 (s : N.State) (i : N.Inputs) :
  R.v28087 (state s) (inputs i) = Zmod.unsigned (N.v28087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28087 s i)) at 1.
  unfold R.v28087, N.v28087.
  unfold R.v6, N.v6.
  rewrite !state_r1261_nr_5F1261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1261_nr_5F1261 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28088 (s : N.State) (i : N.Inputs) :
  R.v28088 (state s) (inputs i) = Zmod.unsigned (N.v28088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28088 s i)) at 1.
  unfold R.v28088, N.v28088.
  unfold R.v6, N.v6.
  rewrite ?node_10929.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28089 (s : N.State) (i : N.Inputs) :
  R.v28089 (state s) (inputs i) = Zmod.unsigned (N.v28089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28089 s i)) at 1.
  unfold R.v28089, N.v28089.
  rewrite ?node_28087.
  rewrite ?node_28088.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28090 (s : N.State) (i : N.Inputs) :
  R.v28090 (state s) (inputs i) = Zmod.unsigned (N.v28090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28090 s i)) at 1.
  unfold R.v28090, N.v28090.
  unfold R.v16484, N.v16484.
  rewrite ?node_28089.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28091 (s : N.State) (i : N.Inputs) :
  R.v28091 (state s) (inputs i) = Zmod.unsigned (N.v28091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28091 s i)) at 1.
  unfold R.v28091, N.v28091.
  rewrite ?node_28086.
  rewrite ?node_28090.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28092 (s : N.State) (i : N.Inputs) :
  R.v28092 (state s) (inputs i) = Zmod.unsigned (N.v28092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28092 s i)) at 1.
  unfold R.v28092, N.v28092.
  unfold R.v6, N.v6.
  rewrite ?node_28091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28093 (s : N.State) (i : N.Inputs) :
  R.v28093 (state s) (inputs i) = Zmod.unsigned (N.v28093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28093 s i)) at 1.
  unfold R.v28093, N.v28093.
  rewrite ?node_10934.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28094 (s : N.State) (i : N.Inputs) :
  R.v28094 (state s) (inputs i) = Zmod.unsigned (N.v28094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28094 s i)) at 1.
  unfold R.v28094, N.v28094.
  unfold R.v6, N.v6.
  rewrite ?node_11158.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28095 (s : N.State) (i : N.Inputs) :
  R.v28095 (state s) (inputs i) = Zmod.unsigned (N.v28095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28095 s i)) at 1.
  unfold R.v28095, N.v28095.
  rewrite ?node_28093.
  rewrite ?node_28094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28096 (s : N.State) (i : N.Inputs) :
  R.v28096 (state s) (inputs i) = Zmod.unsigned (N.v28096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28096 s i)) at 1.
  unfold R.v28096, N.v28096.
  rewrite ?node_28092.
  rewrite ?node_28095.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28097 (s : N.State) (i : N.Inputs) :
  R.v28097 (state s) (inputs i) = Zmod.unsigned (N.v28097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28097 s i)) at 1.
  unfold R.v28097, N.v28097.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28098 (s : N.State) (i : N.Inputs) :
  R.v28098 (state s) (inputs i) = Zmod.unsigned (N.v28098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28098 s i)) at 1.
  unfold R.v28098, N.v28098.
  rewrite ?node_10941.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28099 (s : N.State) (i : N.Inputs) :
  R.v28099 (state s) (inputs i) = Zmod.unsigned (N.v28099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28099 s i)) at 1.
  unfold R.v28099, N.v28099.
  unfold R.v16463, N.v16463.
  rewrite !state_r1265_nr_5F1265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1265_nr_5F1265 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28100 (s : N.State) (i : N.Inputs) :
  R.v28100 (state s) (inputs i) = Zmod.unsigned (N.v28100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28100 s i)) at 1.
  unfold R.v28100, N.v28100.
  unfold R.v16463, N.v16463.
  rewrite !state_r1264_nr_5F1264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1264_nr_5F1264 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28101 (s : N.State) (i : N.Inputs) :
  R.v28101 (state s) (inputs i) = Zmod.unsigned (N.v28101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28101 s i)) at 1.
  unfold R.v28101, N.v28101.
  unfold R.v6, N.v6.
  rewrite !state_r1263_nr_5F1263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1263_nr_5F1263 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28102 (s : N.State) (i : N.Inputs) :
  R.v28102 (state s) (inputs i) = Zmod.unsigned (N.v28102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28102 s i)) at 1.
  unfold R.v28102, N.v28102.
  unfold R.v6, N.v6.
  rewrite !state_r1262_nr_5F1262.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1262_nr_5F1262 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28103 (s : N.State) (i : N.Inputs) :
  R.v28103 (state s) (inputs i) = Zmod.unsigned (N.v28103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28103 s i)) at 1.
  unfold R.v28103, N.v28103.
  rewrite ?node_28101.
  rewrite ?node_28102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28104 (s : N.State) (i : N.Inputs) :
  R.v28104 (state s) (inputs i) = Zmod.unsigned (N.v28104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28104 s i)) at 1.
  unfold R.v28104, N.v28104.
  unfold R.v16484, N.v16484.
  rewrite ?node_28103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28105 (s : N.State) (i : N.Inputs) :
  R.v28105 (state s) (inputs i) = Zmod.unsigned (N.v28105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28105 s i)) at 1.
  unfold R.v28105, N.v28105.
  rewrite ?node_28098.
  rewrite ?node_28099.
  rewrite ?node_28100.
  rewrite ?node_28104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28106 (s : N.State) (i : N.Inputs) :
  R.v28106 (state s) (inputs i) = Zmod.unsigned (N.v28106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28106 s i)) at 1.
  unfold R.v28106, N.v28106.
  unfold R.v6, N.v6.
  rewrite ?node_28105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28107 (s : N.State) (i : N.Inputs) :
  R.v28107 (state s) (inputs i) = Zmod.unsigned (N.v28107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28107 s i)) at 1.
  unfold R.v28107, N.v28107.
  rewrite ?node_10942.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28108 (s : N.State) (i : N.Inputs) :
  R.v28108 (state s) (inputs i) = Zmod.unsigned (N.v28108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28108 s i)) at 1.
  unfold R.v28108, N.v28108.
  unfold R.v6, N.v6.
  rewrite ?node_11102.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28109 (s : N.State) (i : N.Inputs) :
  R.v28109 (state s) (inputs i) = Zmod.unsigned (N.v28109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28109 s i)) at 1.
  unfold R.v28109, N.v28109.
  unfold R.v6, N.v6.
  rewrite ?node_11162.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28110 (s : N.State) (i : N.Inputs) :
  R.v28110 (state s) (inputs i) = Zmod.unsigned (N.v28110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28110 s i)) at 1.
  unfold R.v28110, N.v28110.
  rewrite ?node_28107.
  rewrite ?node_28108.
  rewrite ?node_28109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28111 (s : N.State) (i : N.Inputs) :
  R.v28111 (state s) (inputs i) = Zmod.unsigned (N.v28111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28111 s i)) at 1.
  unfold R.v28111, N.v28111.
  rewrite ?node_28106.
  rewrite ?node_28110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28112 (s : N.State) (i : N.Inputs) :
  R.v28112 (state s) (inputs i) = Zmod.unsigned (N.v28112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28112 s i)) at 1.
  unfold R.v28112, N.v28112.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28113 (s : N.State) (i : N.Inputs) :
  R.v28113 (state s) (inputs i) = Zmod.unsigned (N.v28113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28113 s i)) at 1.
  unfold R.v28113, N.v28113.
  unfold R.v16463, N.v16463.
  rewrite !state_r1264_nr_5F1264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1264_nr_5F1264 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28114 (s : N.State) (i : N.Inputs) :
  R.v28114 (state s) (inputs i) = Zmod.unsigned (N.v28114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28114 s i)) at 1.
  unfold R.v28114, N.v28114.
  unfold R.v6, N.v6.
  rewrite !state_r1263_nr_5F1263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1263_nr_5F1263 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28115 (s : N.State) (i : N.Inputs) :
  R.v28115 (state s) (inputs i) = Zmod.unsigned (N.v28115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28115 s i)) at 1.
  unfold R.v28115, N.v28115.
  unfold R.v6, N.v6.
  rewrite !state_r1262_nr_5F1262.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1262_nr_5F1262 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28116 (s : N.State) (i : N.Inputs) :
  R.v28116 (state s) (inputs i) = Zmod.unsigned (N.v28116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28116 s i)) at 1.
  unfold R.v28116, N.v28116.
  rewrite ?node_28114.
  rewrite ?node_28115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28117 (s : N.State) (i : N.Inputs) :
  R.v28117 (state s) (inputs i) = Zmod.unsigned (N.v28117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28117 s i)) at 1.
  unfold R.v28117, N.v28117.
  unfold R.v16484, N.v16484.
  rewrite ?node_28116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28118 (s : N.State) (i : N.Inputs) :
  R.v28118 (state s) (inputs i) = Zmod.unsigned (N.v28118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28118 s i)) at 1.
  unfold R.v28118, N.v28118.
  rewrite ?node_28113.
  rewrite ?node_28117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28119 (s : N.State) (i : N.Inputs) :
  R.v28119 (state s) (inputs i) = Zmod.unsigned (N.v28119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28119 s i)) at 1.
  unfold R.v28119, N.v28119.
  unfold R.v6, N.v6.
  rewrite ?node_28118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28120 (s : N.State) (i : N.Inputs) :
  R.v28120 (state s) (inputs i) = Zmod.unsigned (N.v28120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28120 s i)) at 1.
  unfold R.v28120, N.v28120.
  rewrite ?node_10937.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28121 (s : N.State) (i : N.Inputs) :
  R.v28121 (state s) (inputs i) = Zmod.unsigned (N.v28121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28121 s i)) at 1.
  unfold R.v28121, N.v28121.
  unfold R.v6, N.v6.
  rewrite ?node_11102.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28122 (s : N.State) (i : N.Inputs) :
  R.v28122 (state s) (inputs i) = Zmod.unsigned (N.v28122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28122 s i)) at 1.
  unfold R.v28122, N.v28122.
  rewrite ?node_28120.
  rewrite ?node_28121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28123 (s : N.State) (i : N.Inputs) :
  R.v28123 (state s) (inputs i) = Zmod.unsigned (N.v28123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28123 s i)) at 1.
  unfold R.v28123, N.v28123.
  rewrite ?node_28119.
  rewrite ?node_28122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28124 (s : N.State) (i : N.Inputs) :
  R.v28124 (state s) (inputs i) = Zmod.unsigned (N.v28124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28124 s i)) at 1.
  unfold R.v28124, N.v28124.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28125 (s : N.State) (i : N.Inputs) :
  R.v28125 (state s) (inputs i) = Zmod.unsigned (N.v28125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28125 s i)) at 1.
  unfold R.v28125, N.v28125.
  rewrite ?node_10941.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28126 (s : N.State) (i : N.Inputs) :
  R.v28126 (state s) (inputs i) = Zmod.unsigned (N.v28126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28126 s i)) at 1.
  unfold R.v28126, N.v28126.
  unfold R.v6, N.v6.
  rewrite !state_r1265_nr_5F1265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1265_nr_5F1265 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28127 (s : N.State) (i : N.Inputs) :
  R.v28127 (state s) (inputs i) = Zmod.unsigned (N.v28127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28127 s i)) at 1.
  unfold R.v28127, N.v28127.
  unfold R.v6, N.v6.
  rewrite ?node_10937.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28128 (s : N.State) (i : N.Inputs) :
  R.v28128 (state s) (inputs i) = Zmod.unsigned (N.v28128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28128 s i)) at 1.
  unfold R.v28128, N.v28128.
  rewrite ?node_28126.
  rewrite ?node_28127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28129 (s : N.State) (i : N.Inputs) :
  R.v28129 (state s) (inputs i) = Zmod.unsigned (N.v28129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28129 s i)) at 1.
  unfold R.v28129, N.v28129.
  unfold R.v16484, N.v16484.
  rewrite ?node_28128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28130 (s : N.State) (i : N.Inputs) :
  R.v28130 (state s) (inputs i) = Zmod.unsigned (N.v28130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28130 s i)) at 1.
  unfold R.v28130, N.v28130.
  rewrite ?node_28125.
  rewrite ?node_28129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28131 (s : N.State) (i : N.Inputs) :
  R.v28131 (state s) (inputs i) = Zmod.unsigned (N.v28131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28131 s i)) at 1.
  unfold R.v28131, N.v28131.
  unfold R.v6, N.v6.
  rewrite ?node_28130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28132 (s : N.State) (i : N.Inputs) :
  R.v28132 (state s) (inputs i) = Zmod.unsigned (N.v28132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28132 s i)) at 1.
  unfold R.v28132, N.v28132.
  rewrite ?node_10942.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28133 (s : N.State) (i : N.Inputs) :
  R.v28133 (state s) (inputs i) = Zmod.unsigned (N.v28133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28133 s i)) at 1.
  unfold R.v28133, N.v28133.
  unfold R.v6, N.v6.
  rewrite ?node_11162.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28134 (s : N.State) (i : N.Inputs) :
  R.v28134 (state s) (inputs i) = Zmod.unsigned (N.v28134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28134 s i)) at 1.
  unfold R.v28134, N.v28134.
  rewrite ?node_28132.
  rewrite ?node_28133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28135 (s : N.State) (i : N.Inputs) :
  R.v28135 (state s) (inputs i) = Zmod.unsigned (N.v28135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28135 s i)) at 1.
  unfold R.v28135, N.v28135.
  rewrite ?node_28131.
  rewrite ?node_28134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28136 (s : N.State) (i : N.Inputs) :
  R.v28136 (state s) (inputs i) = Zmod.unsigned (N.v28136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28136 s i)) at 1.
  unfold R.v28136, N.v28136.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28137 (s : N.State) (i : N.Inputs) :
  R.v28137 (state s) (inputs i) = Zmod.unsigned (N.v28137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28137 s i)) at 1.
  unfold R.v28137, N.v28137.
  rewrite ?node_10949.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28138 (s : N.State) (i : N.Inputs) :
  R.v28138 (state s) (inputs i) = Zmod.unsigned (N.v28138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28138 s i)) at 1.
  unfold R.v28138, N.v28138.
  unfold R.v16463, N.v16463.
  rewrite !state_r1269_nr_5F1269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1269_nr_5F1269 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28139 (s : N.State) (i : N.Inputs) :
  R.v28139 (state s) (inputs i) = Zmod.unsigned (N.v28139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28139 s i)) at 1.
  unfold R.v28139, N.v28139.
  unfold R.v16463, N.v16463.
  rewrite !state_r1268_nr_5F1268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1268_nr_5F1268 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28140 (s : N.State) (i : N.Inputs) :
  R.v28140 (state s) (inputs i) = Zmod.unsigned (N.v28140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28140 s i)) at 1.
  unfold R.v28140, N.v28140.
  unfold R.v6, N.v6.
  rewrite !state_r1267_nr_5F1267.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1267_nr_5F1267 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28141 (s : N.State) (i : N.Inputs) :
  R.v28141 (state s) (inputs i) = Zmod.unsigned (N.v28141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28141 s i)) at 1.
  unfold R.v28141, N.v28141.
  unfold R.v6, N.v6.
  rewrite !state_r1266_nr_5F1266.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1266_nr_5F1266 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28142 (s : N.State) (i : N.Inputs) :
  R.v28142 (state s) (inputs i) = Zmod.unsigned (N.v28142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28142 s i)) at 1.
  unfold R.v28142, N.v28142.
  rewrite ?node_28140.
  rewrite ?node_28141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28143 (s : N.State) (i : N.Inputs) :
  R.v28143 (state s) (inputs i) = Zmod.unsigned (N.v28143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28143 s i)) at 1.
  unfold R.v28143, N.v28143.
  unfold R.v16484, N.v16484.
  rewrite ?node_28142.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28144 (s : N.State) (i : N.Inputs) :
  R.v28144 (state s) (inputs i) = Zmod.unsigned (N.v28144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28144 s i)) at 1.
  unfold R.v28144, N.v28144.
  rewrite ?node_28137.
  rewrite ?node_28138.
  rewrite ?node_28139.
  rewrite ?node_28143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28145 (s : N.State) (i : N.Inputs) :
  R.v28145 (state s) (inputs i) = Zmod.unsigned (N.v28145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28145 s i)) at 1.
  unfold R.v28145, N.v28145.
  unfold R.v6, N.v6.
  rewrite ?node_28144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28146 (s : N.State) (i : N.Inputs) :
  R.v28146 (state s) (inputs i) = Zmod.unsigned (N.v28146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28146 s i)) at 1.
  unfold R.v28146, N.v28146.
  rewrite ?node_10950.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28147 (s : N.State) (i : N.Inputs) :
  R.v28147 (state s) (inputs i) = Zmod.unsigned (N.v28147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28147 s i)) at 1.
  unfold R.v28147, N.v28147.
  unfold R.v6, N.v6.
  rewrite ?node_11110.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28148 (s : N.State) (i : N.Inputs) :
  R.v28148 (state s) (inputs i) = Zmod.unsigned (N.v28148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28148 s i)) at 1.
  unfold R.v28148, N.v28148.
  unfold R.v6, N.v6.
  rewrite ?node_11166.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28149 (s : N.State) (i : N.Inputs) :
  R.v28149 (state s) (inputs i) = Zmod.unsigned (N.v28149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28149 s i)) at 1.
  unfold R.v28149, N.v28149.
  rewrite ?node_28146.
  rewrite ?node_28147.
  rewrite ?node_28148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28150 (s : N.State) (i : N.Inputs) :
  R.v28150 (state s) (inputs i) = Zmod.unsigned (N.v28150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28150 s i)) at 1.
  unfold R.v28150, N.v28150.
  rewrite ?node_28145.
  rewrite ?node_28149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28151 (s : N.State) (i : N.Inputs) :
  R.v28151 (state s) (inputs i) = Zmod.unsigned (N.v28151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28151 s i)) at 1.
  unfold R.v28151, N.v28151.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28152 (s : N.State) (i : N.Inputs) :
  R.v28152 (state s) (inputs i) = Zmod.unsigned (N.v28152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28152 s i)) at 1.
  unfold R.v28152, N.v28152.
  unfold R.v16463, N.v16463.
  rewrite !state_r1268_nr_5F1268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1268_nr_5F1268 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28153 (s : N.State) (i : N.Inputs) :
  R.v28153 (state s) (inputs i) = Zmod.unsigned (N.v28153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28153 s i)) at 1.
  unfold R.v28153, N.v28153.
  unfold R.v6, N.v6.
  rewrite !state_r1267_nr_5F1267.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1267_nr_5F1267 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28154 (s : N.State) (i : N.Inputs) :
  R.v28154 (state s) (inputs i) = Zmod.unsigned (N.v28154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28154 s i)) at 1.
  unfold R.v28154, N.v28154.
  unfold R.v6, N.v6.
  rewrite !state_r1266_nr_5F1266.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1266_nr_5F1266 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28155 (s : N.State) (i : N.Inputs) :
  R.v28155 (state s) (inputs i) = Zmod.unsigned (N.v28155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28155 s i)) at 1.
  unfold R.v28155, N.v28155.
  rewrite ?node_28153.
  rewrite ?node_28154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28156 (s : N.State) (i : N.Inputs) :
  R.v28156 (state s) (inputs i) = Zmod.unsigned (N.v28156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28156 s i)) at 1.
  unfold R.v28156, N.v28156.
  unfold R.v16484, N.v16484.
  rewrite ?node_28155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28157 (s : N.State) (i : N.Inputs) :
  R.v28157 (state s) (inputs i) = Zmod.unsigned (N.v28157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28157 s i)) at 1.
  unfold R.v28157, N.v28157.
  rewrite ?node_28152.
  rewrite ?node_28156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28158 (s : N.State) (i : N.Inputs) :
  R.v28158 (state s) (inputs i) = Zmod.unsigned (N.v28158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28158 s i)) at 1.
  unfold R.v28158, N.v28158.
  unfold R.v6, N.v6.
  rewrite ?node_28157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28159 (s : N.State) (i : N.Inputs) :
  R.v28159 (state s) (inputs i) = Zmod.unsigned (N.v28159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28159 s i)) at 1.
  unfold R.v28159, N.v28159.
  rewrite ?node_10945.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28160 (s : N.State) (i : N.Inputs) :
  R.v28160 (state s) (inputs i) = Zmod.unsigned (N.v28160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28160 s i)) at 1.
  unfold R.v28160, N.v28160.
  unfold R.v6, N.v6.
  rewrite ?node_11110.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28161 (s : N.State) (i : N.Inputs) :
  R.v28161 (state s) (inputs i) = Zmod.unsigned (N.v28161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28161 s i)) at 1.
  unfold R.v28161, N.v28161.
  rewrite ?node_28159.
  rewrite ?node_28160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28162 (s : N.State) (i : N.Inputs) :
  R.v28162 (state s) (inputs i) = Zmod.unsigned (N.v28162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28162 s i)) at 1.
  unfold R.v28162, N.v28162.
  rewrite ?node_28158.
  rewrite ?node_28161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28163 (s : N.State) (i : N.Inputs) :
  R.v28163 (state s) (inputs i) = Zmod.unsigned (N.v28163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28163 s i)) at 1.
  unfold R.v28163, N.v28163.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28164 (s : N.State) (i : N.Inputs) :
  R.v28164 (state s) (inputs i) = Zmod.unsigned (N.v28164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28164 s i)) at 1.
  unfold R.v28164, N.v28164.
  rewrite ?node_10949.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28165 (s : N.State) (i : N.Inputs) :
  R.v28165 (state s) (inputs i) = Zmod.unsigned (N.v28165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28165 s i)) at 1.
  unfold R.v28165, N.v28165.
  unfold R.v6, N.v6.
  rewrite !state_r1269_nr_5F1269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1269_nr_5F1269 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28166 (s : N.State) (i : N.Inputs) :
  R.v28166 (state s) (inputs i) = Zmod.unsigned (N.v28166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28166 s i)) at 1.
  unfold R.v28166, N.v28166.
  unfold R.v6, N.v6.
  rewrite ?node_10945.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28167 (s : N.State) (i : N.Inputs) :
  R.v28167 (state s) (inputs i) = Zmod.unsigned (N.v28167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28167 s i)) at 1.
  unfold R.v28167, N.v28167.
  rewrite ?node_28165.
  rewrite ?node_28166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28168 (s : N.State) (i : N.Inputs) :
  R.v28168 (state s) (inputs i) = Zmod.unsigned (N.v28168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28168 s i)) at 1.
  unfold R.v28168, N.v28168.
  unfold R.v16484, N.v16484.
  rewrite ?node_28167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28169 (s : N.State) (i : N.Inputs) :
  R.v28169 (state s) (inputs i) = Zmod.unsigned (N.v28169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28169 s i)) at 1.
  unfold R.v28169, N.v28169.
  rewrite ?node_28164.
  rewrite ?node_28168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28170 (s : N.State) (i : N.Inputs) :
  R.v28170 (state s) (inputs i) = Zmod.unsigned (N.v28170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28170 s i)) at 1.
  unfold R.v28170, N.v28170.
  unfold R.v6, N.v6.
  rewrite ?node_28169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28171 (s : N.State) (i : N.Inputs) :
  R.v28171 (state s) (inputs i) = Zmod.unsigned (N.v28171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28171 s i)) at 1.
  unfold R.v28171, N.v28171.
  rewrite ?node_10950.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28172 (s : N.State) (i : N.Inputs) :
  R.v28172 (state s) (inputs i) = Zmod.unsigned (N.v28172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28172 s i)) at 1.
  unfold R.v28172, N.v28172.
  unfold R.v6, N.v6.
  rewrite ?node_11166.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28173 (s : N.State) (i : N.Inputs) :
  R.v28173 (state s) (inputs i) = Zmod.unsigned (N.v28173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28173 s i)) at 1.
  unfold R.v28173, N.v28173.
  rewrite ?node_28171.
  rewrite ?node_28172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28174 (s : N.State) (i : N.Inputs) :
  R.v28174 (state s) (inputs i) = Zmod.unsigned (N.v28174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28174 s i)) at 1.
  unfold R.v28174, N.v28174.
  rewrite ?node_28170.
  rewrite ?node_28173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28175 (s : N.State) (i : N.Inputs) :
  R.v28175 (state s) (inputs i) = Zmod.unsigned (N.v28175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28175 s i)) at 1.
  unfold R.v28175, N.v28175.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28176 (s : N.State) (i : N.Inputs) :
  R.v28176 (state s) (inputs i) = Zmod.unsigned (N.v28176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28176 s i)) at 1.
  unfold R.v28176, N.v28176.
  rewrite ?node_10961.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28177 (s : N.State) (i : N.Inputs) :
  R.v28177 (state s) (inputs i) = Zmod.unsigned (N.v28177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28177 s i)) at 1.
  unfold R.v28177, N.v28177.
  unfold R.v16463, N.v16463.
  rewrite !state_r1273_nr_5F1273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1273_nr_5F1273 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28178 (s : N.State) (i : N.Inputs) :
  R.v28178 (state s) (inputs i) = Zmod.unsigned (N.v28178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28178 s i)) at 1.
  unfold R.v28178, N.v28178.
  unfold R.v16463, N.v16463.
  rewrite !state_r1272_nr_5F1272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1272_nr_5F1272 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28179 (s : N.State) (i : N.Inputs) :
  R.v28179 (state s) (inputs i) = Zmod.unsigned (N.v28179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28179 s i)) at 1.
  unfold R.v28179, N.v28179.
  unfold R.v6, N.v6.
  rewrite !state_r1271_nr_5F1271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1271_nr_5F1271 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28180 (s : N.State) (i : N.Inputs) :
  R.v28180 (state s) (inputs i) = Zmod.unsigned (N.v28180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28180 s i)) at 1.
  unfold R.v28180, N.v28180.
  unfold R.v6, N.v6.
  rewrite !state_r1270_nr_5F1270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1270_nr_5F1270 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28181 (s : N.State) (i : N.Inputs) :
  R.v28181 (state s) (inputs i) = Zmod.unsigned (N.v28181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28181 s i)) at 1.
  unfold R.v28181, N.v28181.
  rewrite ?node_28179.
  rewrite ?node_28180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28182 (s : N.State) (i : N.Inputs) :
  R.v28182 (state s) (inputs i) = Zmod.unsigned (N.v28182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28182 s i)) at 1.
  unfold R.v28182, N.v28182.
  unfold R.v16484, N.v16484.
  rewrite ?node_28181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28183 (s : N.State) (i : N.Inputs) :
  R.v28183 (state s) (inputs i) = Zmod.unsigned (N.v28183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28183 s i)) at 1.
  unfold R.v28183, N.v28183.
  rewrite ?node_28176.
  rewrite ?node_28177.
  rewrite ?node_28178.
  rewrite ?node_28182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28184 (s : N.State) (i : N.Inputs) :
  R.v28184 (state s) (inputs i) = Zmod.unsigned (N.v28184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28184 s i)) at 1.
  unfold R.v28184, N.v28184.
  unfold R.v6, N.v6.
  rewrite ?node_28183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28185 (s : N.State) (i : N.Inputs) :
  R.v28185 (state s) (inputs i) = Zmod.unsigned (N.v28185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28185 s i)) at 1.
  unfold R.v28185, N.v28185.
  rewrite ?node_10962.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28186 (s : N.State) (i : N.Inputs) :
  R.v28186 (state s) (inputs i) = Zmod.unsigned (N.v28186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28186 s i)) at 1.
  unfold R.v28186, N.v28186.
  unfold R.v6, N.v6.
  rewrite ?node_11122.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28187 (s : N.State) (i : N.Inputs) :
  R.v28187 (state s) (inputs i) = Zmod.unsigned (N.v28187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28187 s i)) at 1.
  unfold R.v28187, N.v28187.
  unfold R.v6, N.v6.
  rewrite ?node_11175.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28188 (s : N.State) (i : N.Inputs) :
  R.v28188 (state s) (inputs i) = Zmod.unsigned (N.v28188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28188 s i)) at 1.
  unfold R.v28188, N.v28188.
  rewrite ?node_28185.
  rewrite ?node_28186.
  rewrite ?node_28187.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28189 (s : N.State) (i : N.Inputs) :
  R.v28189 (state s) (inputs i) = Zmod.unsigned (N.v28189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28189 s i)) at 1.
  unfold R.v28189, N.v28189.
  rewrite ?node_28184.
  rewrite ?node_28188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28190 (s : N.State) (i : N.Inputs) :
  R.v28190 (state s) (inputs i) = Zmod.unsigned (N.v28190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28190 s i)) at 1.
  unfold R.v28190, N.v28190.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28191 (s : N.State) (i : N.Inputs) :
  R.v28191 (state s) (inputs i) = Zmod.unsigned (N.v28191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28191 s i)) at 1.
  unfold R.v28191, N.v28191.
  unfold R.v16463, N.v16463.
  rewrite !state_r1272_nr_5F1272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1272_nr_5F1272 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28192 (s : N.State) (i : N.Inputs) :
  R.v28192 (state s) (inputs i) = Zmod.unsigned (N.v28192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28192 s i)) at 1.
  unfold R.v28192, N.v28192.
  unfold R.v6, N.v6.
  rewrite !state_r1271_nr_5F1271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1271_nr_5F1271 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28193 (s : N.State) (i : N.Inputs) :
  R.v28193 (state s) (inputs i) = Zmod.unsigned (N.v28193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28193 s i)) at 1.
  unfold R.v28193, N.v28193.
  unfold R.v6, N.v6.
  rewrite !state_r1270_nr_5F1270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1270_nr_5F1270 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28194 (s : N.State) (i : N.Inputs) :
  R.v28194 (state s) (inputs i) = Zmod.unsigned (N.v28194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28194 s i)) at 1.
  unfold R.v28194, N.v28194.
  rewrite ?node_28192.
  rewrite ?node_28193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28195 (s : N.State) (i : N.Inputs) :
  R.v28195 (state s) (inputs i) = Zmod.unsigned (N.v28195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28195 s i)) at 1.
  unfold R.v28195, N.v28195.
  unfold R.v16484, N.v16484.
  rewrite ?node_28194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28196 (s : N.State) (i : N.Inputs) :
  R.v28196 (state s) (inputs i) = Zmod.unsigned (N.v28196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28196 s i)) at 1.
  unfold R.v28196, N.v28196.
  rewrite ?node_28191.
  rewrite ?node_28195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28197 (s : N.State) (i : N.Inputs) :
  R.v28197 (state s) (inputs i) = Zmod.unsigned (N.v28197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28197 s i)) at 1.
  unfold R.v28197, N.v28197.
  unfold R.v6, N.v6.
  rewrite ?node_28196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28198 (s : N.State) (i : N.Inputs) :
  R.v28198 (state s) (inputs i) = Zmod.unsigned (N.v28198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28198 s i)) at 1.
  unfold R.v28198, N.v28198.
  rewrite ?node_10957.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28199 (s : N.State) (i : N.Inputs) :
  R.v28199 (state s) (inputs i) = Zmod.unsigned (N.v28199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28199 s i)) at 1.
  unfold R.v28199, N.v28199.
  unfold R.v6, N.v6.
  rewrite ?node_11122.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28200 (s : N.State) (i : N.Inputs) :
  R.v28200 (state s) (inputs i) = Zmod.unsigned (N.v28200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28200 s i)) at 1.
  unfold R.v28200, N.v28200.
  rewrite ?node_28198.
  rewrite ?node_28199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28201 (s : N.State) (i : N.Inputs) :
  R.v28201 (state s) (inputs i) = Zmod.unsigned (N.v28201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28201 s i)) at 1.
  unfold R.v28201, N.v28201.
  rewrite ?node_28197.
  rewrite ?node_28200.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28202 (s : N.State) (i : N.Inputs) :
  R.v28202 (state s) (inputs i) = Zmod.unsigned (N.v28202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28202 s i)) at 1.
  unfold R.v28202, N.v28202.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28203 (s : N.State) (i : N.Inputs) :
  R.v28203 (state s) (inputs i) = Zmod.unsigned (N.v28203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28203 s i)) at 1.
  unfold R.v28203, N.v28203.
  rewrite ?node_10961.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28204 (s : N.State) (i : N.Inputs) :
  R.v28204 (state s) (inputs i) = Zmod.unsigned (N.v28204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28204 s i)) at 1.
  unfold R.v28204, N.v28204.
  unfold R.v6, N.v6.
  rewrite !state_r1273_nr_5F1273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1273_nr_5F1273 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28205 (s : N.State) (i : N.Inputs) :
  R.v28205 (state s) (inputs i) = Zmod.unsigned (N.v28205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28205 s i)) at 1.
  unfold R.v28205, N.v28205.
  unfold R.v6, N.v6.
  rewrite ?node_10957.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28206 (s : N.State) (i : N.Inputs) :
  R.v28206 (state s) (inputs i) = Zmod.unsigned (N.v28206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28206 s i)) at 1.
  unfold R.v28206, N.v28206.
  rewrite ?node_28204.
  rewrite ?node_28205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28207 (s : N.State) (i : N.Inputs) :
  R.v28207 (state s) (inputs i) = Zmod.unsigned (N.v28207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28207 s i)) at 1.
  unfold R.v28207, N.v28207.
  unfold R.v16484, N.v16484.
  rewrite ?node_28206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28208 (s : N.State) (i : N.Inputs) :
  R.v28208 (state s) (inputs i) = Zmod.unsigned (N.v28208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28208 s i)) at 1.
  unfold R.v28208, N.v28208.
  rewrite ?node_28203.
  rewrite ?node_28207.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28209 (s : N.State) (i : N.Inputs) :
  R.v28209 (state s) (inputs i) = Zmod.unsigned (N.v28209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28209 s i)) at 1.
  unfold R.v28209, N.v28209.
  unfold R.v6, N.v6.
  rewrite ?node_28208.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28210 (s : N.State) (i : N.Inputs) :
  R.v28210 (state s) (inputs i) = Zmod.unsigned (N.v28210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28210 s i)) at 1.
  unfold R.v28210, N.v28210.
  rewrite ?node_10962.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28211 (s : N.State) (i : N.Inputs) :
  R.v28211 (state s) (inputs i) = Zmod.unsigned (N.v28211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28211 s i)) at 1.
  unfold R.v28211, N.v28211.
  unfold R.v6, N.v6.
  rewrite ?node_11175.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28212 (s : N.State) (i : N.Inputs) :
  R.v28212 (state s) (inputs i) = Zmod.unsigned (N.v28212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28212 s i)) at 1.
  unfold R.v28212, N.v28212.
  rewrite ?node_28210.
  rewrite ?node_28211.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28213 (s : N.State) (i : N.Inputs) :
  R.v28213 (state s) (inputs i) = Zmod.unsigned (N.v28213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28213 s i)) at 1.
  unfold R.v28213, N.v28213.
  rewrite ?node_28209.
  rewrite ?node_28212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28214 (s : N.State) (i : N.Inputs) :
  R.v28214 (state s) (inputs i) = Zmod.unsigned (N.v28214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28214 s i)) at 1.
  unfold R.v28214, N.v28214.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28215 (s : N.State) (i : N.Inputs) :
  R.v28215 (state s) (inputs i) = Zmod.unsigned (N.v28215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28215 s i)) at 1.
  unfold R.v28215, N.v28215.
  rewrite ?node_10968.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28216 (s : N.State) (i : N.Inputs) :
  R.v28216 (state s) (inputs i) = Zmod.unsigned (N.v28216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28216 s i)) at 1.
  unfold R.v28216, N.v28216.
  unfold R.v16463, N.v16463.
  rewrite !state_r1277_nr_5F1277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1277_nr_5F1277 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28217 (s : N.State) (i : N.Inputs) :
  R.v28217 (state s) (inputs i) = Zmod.unsigned (N.v28217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28217 s i)) at 1.
  unfold R.v28217, N.v28217.
  unfold R.v16463, N.v16463.
  rewrite !state_r1276_nr_5F1276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1276_nr_5F1276 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28218 (s : N.State) (i : N.Inputs) :
  R.v28218 (state s) (inputs i) = Zmod.unsigned (N.v28218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28218 s i)) at 1.
  unfold R.v28218, N.v28218.
  unfold R.v6, N.v6.
  rewrite !state_r1275_nr_5F1275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1275_nr_5F1275 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28219 (s : N.State) (i : N.Inputs) :
  R.v28219 (state s) (inputs i) = Zmod.unsigned (N.v28219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28219 s i)) at 1.
  unfold R.v28219, N.v28219.
  unfold R.v6, N.v6.
  rewrite !state_r1274_nr_5F1274.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1274_nr_5F1274 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28220 (s : N.State) (i : N.Inputs) :
  R.v28220 (state s) (inputs i) = Zmod.unsigned (N.v28220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28220 s i)) at 1.
  unfold R.v28220, N.v28220.
  rewrite ?node_28218.
  rewrite ?node_28219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28221 (s : N.State) (i : N.Inputs) :
  R.v28221 (state s) (inputs i) = Zmod.unsigned (N.v28221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28221 s i)) at 1.
  unfold R.v28221, N.v28221.
  unfold R.v16484, N.v16484.
  rewrite ?node_28220.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28222 (s : N.State) (i : N.Inputs) :
  R.v28222 (state s) (inputs i) = Zmod.unsigned (N.v28222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28222 s i)) at 1.
  unfold R.v28222, N.v28222.
  rewrite ?node_28215.
  rewrite ?node_28216.
  rewrite ?node_28217.
  rewrite ?node_28221.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28223 (s : N.State) (i : N.Inputs) :
  R.v28223 (state s) (inputs i) = Zmod.unsigned (N.v28223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28223 s i)) at 1.
  unfold R.v28223, N.v28223.
  unfold R.v6, N.v6.
  rewrite ?node_28222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28224 (s : N.State) (i : N.Inputs) :
  R.v28224 (state s) (inputs i) = Zmod.unsigned (N.v28224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28224 s i)) at 1.
  unfold R.v28224, N.v28224.
  rewrite ?node_10969.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28225 (s : N.State) (i : N.Inputs) :
  R.v28225 (state s) (inputs i) = Zmod.unsigned (N.v28225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28225 s i)) at 1.
  unfold R.v28225, N.v28225.
  unfold R.v6, N.v6.
  rewrite ?node_11129.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28226 (s : N.State) (i : N.Inputs) :
  R.v28226 (state s) (inputs i) = Zmod.unsigned (N.v28226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28226 s i)) at 1.
  unfold R.v28226, N.v28226.
  unfold R.v6, N.v6.
  rewrite ?node_11178.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28227 (s : N.State) (i : N.Inputs) :
  R.v28227 (state s) (inputs i) = Zmod.unsigned (N.v28227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28227 s i)) at 1.
  unfold R.v28227, N.v28227.
  rewrite ?node_28224.
  rewrite ?node_28225.
  rewrite ?node_28226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28228 (s : N.State) (i : N.Inputs) :
  R.v28228 (state s) (inputs i) = Zmod.unsigned (N.v28228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28228 s i)) at 1.
  unfold R.v28228, N.v28228.
  rewrite ?node_28223.
  rewrite ?node_28227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28229 (s : N.State) (i : N.Inputs) :
  R.v28229 (state s) (inputs i) = Zmod.unsigned (N.v28229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28229 s i)) at 1.
  unfold R.v28229, N.v28229.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28230 (s : N.State) (i : N.Inputs) :
  R.v28230 (state s) (inputs i) = Zmod.unsigned (N.v28230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28230 s i)) at 1.
  unfold R.v28230, N.v28230.
  unfold R.v16463, N.v16463.
  rewrite !state_r1276_nr_5F1276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1276_nr_5F1276 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28231 (s : N.State) (i : N.Inputs) :
  R.v28231 (state s) (inputs i) = Zmod.unsigned (N.v28231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28231 s i)) at 1.
  unfold R.v28231, N.v28231.
  unfold R.v6, N.v6.
  rewrite !state_r1275_nr_5F1275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1275_nr_5F1275 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28232 (s : N.State) (i : N.Inputs) :
  R.v28232 (state s) (inputs i) = Zmod.unsigned (N.v28232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28232 s i)) at 1.
  unfold R.v28232, N.v28232.
  unfold R.v6, N.v6.
  rewrite !state_r1274_nr_5F1274.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1274_nr_5F1274 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28233 (s : N.State) (i : N.Inputs) :
  R.v28233 (state s) (inputs i) = Zmod.unsigned (N.v28233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28233 s i)) at 1.
  unfold R.v28233, N.v28233.
  rewrite ?node_28231.
  rewrite ?node_28232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28234 (s : N.State) (i : N.Inputs) :
  R.v28234 (state s) (inputs i) = Zmod.unsigned (N.v28234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28234 s i)) at 1.
  unfold R.v28234, N.v28234.
  unfold R.v16484, N.v16484.
  rewrite ?node_28233.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28235 (s : N.State) (i : N.Inputs) :
  R.v28235 (state s) (inputs i) = Zmod.unsigned (N.v28235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28235 s i)) at 1.
  unfold R.v28235, N.v28235.
  rewrite ?node_28230.
  rewrite ?node_28234.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28236 (s : N.State) (i : N.Inputs) :
  R.v28236 (state s) (inputs i) = Zmod.unsigned (N.v28236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28236 s i)) at 1.
  unfold R.v28236, N.v28236.
  unfold R.v6, N.v6.
  rewrite ?node_28235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28237 (s : N.State) (i : N.Inputs) :
  R.v28237 (state s) (inputs i) = Zmod.unsigned (N.v28237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28237 s i)) at 1.
  unfold R.v28237, N.v28237.
  rewrite ?node_10964.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28238 (s : N.State) (i : N.Inputs) :
  R.v28238 (state s) (inputs i) = Zmod.unsigned (N.v28238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28238 s i)) at 1.
  unfold R.v28238, N.v28238.
  unfold R.v6, N.v6.
  rewrite ?node_11129.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28239 (s : N.State) (i : N.Inputs) :
  R.v28239 (state s) (inputs i) = Zmod.unsigned (N.v28239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28239 s i)) at 1.
  unfold R.v28239, N.v28239.
  rewrite ?node_28237.
  rewrite ?node_28238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28240 (s : N.State) (i : N.Inputs) :
  R.v28240 (state s) (inputs i) = Zmod.unsigned (N.v28240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28240 s i)) at 1.
  unfold R.v28240, N.v28240.
  rewrite ?node_28236.
  rewrite ?node_28239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28241 (s : N.State) (i : N.Inputs) :
  R.v28241 (state s) (inputs i) = Zmod.unsigned (N.v28241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28241 s i)) at 1.
  unfold R.v28241, N.v28241.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28242 (s : N.State) (i : N.Inputs) :
  R.v28242 (state s) (inputs i) = Zmod.unsigned (N.v28242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28242 s i)) at 1.
  unfold R.v28242, N.v28242.
  rewrite ?node_10968.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28243 (s : N.State) (i : N.Inputs) :
  R.v28243 (state s) (inputs i) = Zmod.unsigned (N.v28243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28243 s i)) at 1.
  unfold R.v28243, N.v28243.
  unfold R.v6, N.v6.
  rewrite !state_r1277_nr_5F1277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1277_nr_5F1277 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28244 (s : N.State) (i : N.Inputs) :
  R.v28244 (state s) (inputs i) = Zmod.unsigned (N.v28244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28244 s i)) at 1.
  unfold R.v28244, N.v28244.
  unfold R.v6, N.v6.
  rewrite ?node_10964.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28245 (s : N.State) (i : N.Inputs) :
  R.v28245 (state s) (inputs i) = Zmod.unsigned (N.v28245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28245 s i)) at 1.
  unfold R.v28245, N.v28245.
  rewrite ?node_28243.
  rewrite ?node_28244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28246 (s : N.State) (i : N.Inputs) :
  R.v28246 (state s) (inputs i) = Zmod.unsigned (N.v28246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28246 s i)) at 1.
  unfold R.v28246, N.v28246.
  unfold R.v16484, N.v16484.
  rewrite ?node_28245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28247 (s : N.State) (i : N.Inputs) :
  R.v28247 (state s) (inputs i) = Zmod.unsigned (N.v28247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28247 s i)) at 1.
  unfold R.v28247, N.v28247.
  rewrite ?node_28242.
  rewrite ?node_28246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28248 (s : N.State) (i : N.Inputs) :
  R.v28248 (state s) (inputs i) = Zmod.unsigned (N.v28248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28248 s i)) at 1.
  unfold R.v28248, N.v28248.
  unfold R.v6, N.v6.
  rewrite ?node_28247.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28249 (s : N.State) (i : N.Inputs) :
  R.v28249 (state s) (inputs i) = Zmod.unsigned (N.v28249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28249 s i)) at 1.
  unfold R.v28249, N.v28249.
  rewrite ?node_10969.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28250 (s : N.State) (i : N.Inputs) :
  R.v28250 (state s) (inputs i) = Zmod.unsigned (N.v28250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28250 s i)) at 1.
  unfold R.v28250, N.v28250.
  unfold R.v6, N.v6.
  rewrite ?node_11178.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28251 (s : N.State) (i : N.Inputs) :
  R.v28251 (state s) (inputs i) = Zmod.unsigned (N.v28251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28251 s i)) at 1.
  unfold R.v28251, N.v28251.
  rewrite ?node_28249.
  rewrite ?node_28250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28252 (s : N.State) (i : N.Inputs) :
  R.v28252 (state s) (inputs i) = Zmod.unsigned (N.v28252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28252 s i)) at 1.
  unfold R.v28252, N.v28252.
  rewrite ?node_28248.
  rewrite ?node_28251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28253 (s : N.State) (i : N.Inputs) :
  R.v28253 (state s) (inputs i) = Zmod.unsigned (N.v28253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28253 s i)) at 1.
  unfold R.v28253, N.v28253.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28254 (s : N.State) (i : N.Inputs) :
  R.v28254 (state s) (inputs i) = Zmod.unsigned (N.v28254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28254 s i)) at 1.
  unfold R.v28254, N.v28254.
  rewrite ?node_10976.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28255 (s : N.State) (i : N.Inputs) :
  R.v28255 (state s) (inputs i) = Zmod.unsigned (N.v28255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28255 s i)) at 1.
  unfold R.v28255, N.v28255.
  unfold R.v16463, N.v16463.
  rewrite !state_r1281_nr_5F1281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1281_nr_5F1281 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28256 (s : N.State) (i : N.Inputs) :
  R.v28256 (state s) (inputs i) = Zmod.unsigned (N.v28256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28256 s i)) at 1.
  unfold R.v28256, N.v28256.
  unfold R.v16463, N.v16463.
  rewrite !state_r1280_nr_5F1280.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1280_nr_5F1280 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28257 (s : N.State) (i : N.Inputs) :
  R.v28257 (state s) (inputs i) = Zmod.unsigned (N.v28257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28257 s i)) at 1.
  unfold R.v28257, N.v28257.
  unfold R.v6, N.v6.
  rewrite !state_r1279_nr_5F1279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1279_nr_5F1279 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28258 (s : N.State) (i : N.Inputs) :
  R.v28258 (state s) (inputs i) = Zmod.unsigned (N.v28258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28258 s i)) at 1.
  unfold R.v28258, N.v28258.
  unfold R.v6, N.v6.
  rewrite !state_r1278_nr_5F1278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1278_nr_5F1278 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28259 (s : N.State) (i : N.Inputs) :
  R.v28259 (state s) (inputs i) = Zmod.unsigned (N.v28259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28259 s i)) at 1.
  unfold R.v28259, N.v28259.
  rewrite ?node_28257.
  rewrite ?node_28258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28260 (s : N.State) (i : N.Inputs) :
  R.v28260 (state s) (inputs i) = Zmod.unsigned (N.v28260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28260 s i)) at 1.
  unfold R.v28260, N.v28260.
  unfold R.v16484, N.v16484.
  rewrite ?node_28259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28261 (s : N.State) (i : N.Inputs) :
  R.v28261 (state s) (inputs i) = Zmod.unsigned (N.v28261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28261 s i)) at 1.
  unfold R.v28261, N.v28261.
  rewrite ?node_28254.
  rewrite ?node_28255.
  rewrite ?node_28256.
  rewrite ?node_28260.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28262 (s : N.State) (i : N.Inputs) :
  R.v28262 (state s) (inputs i) = Zmod.unsigned (N.v28262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28262 s i)) at 1.
  unfold R.v28262, N.v28262.
  unfold R.v6, N.v6.
  rewrite ?node_28261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28263 (s : N.State) (i : N.Inputs) :
  R.v28263 (state s) (inputs i) = Zmod.unsigned (N.v28263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28263 s i)) at 1.
  unfold R.v28263, N.v28263.
  rewrite ?node_10977.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28264 (s : N.State) (i : N.Inputs) :
  R.v28264 (state s) (inputs i) = Zmod.unsigned (N.v28264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28264 s i)) at 1.
  unfold R.v28264, N.v28264.
  unfold R.v6, N.v6.
  rewrite ?node_11137.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28265 (s : N.State) (i : N.Inputs) :
  R.v28265 (state s) (inputs i) = Zmod.unsigned (N.v28265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28265 s i)) at 1.
  unfold R.v28265, N.v28265.
  unfold R.v6, N.v6.
  rewrite ?node_11182.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28266 (s : N.State) (i : N.Inputs) :
  R.v28266 (state s) (inputs i) = Zmod.unsigned (N.v28266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28266 s i)) at 1.
  unfold R.v28266, N.v28266.
  rewrite ?node_28263.
  rewrite ?node_28264.
  rewrite ?node_28265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28267 (s : N.State) (i : N.Inputs) :
  R.v28267 (state s) (inputs i) = Zmod.unsigned (N.v28267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28267 s i)) at 1.
  unfold R.v28267, N.v28267.
  rewrite ?node_28262.
  rewrite ?node_28266.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28268 (s : N.State) (i : N.Inputs) :
  R.v28268 (state s) (inputs i) = Zmod.unsigned (N.v28268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28268 s i)) at 1.
  unfold R.v28268, N.v28268.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28269 (s : N.State) (i : N.Inputs) :
  R.v28269 (state s) (inputs i) = Zmod.unsigned (N.v28269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28269 s i)) at 1.
  unfold R.v28269, N.v28269.
  unfold R.v16463, N.v16463.
  rewrite !state_r1280_nr_5F1280.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1280_nr_5F1280 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28270 (s : N.State) (i : N.Inputs) :
  R.v28270 (state s) (inputs i) = Zmod.unsigned (N.v28270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28270 s i)) at 1.
  unfold R.v28270, N.v28270.
  unfold R.v6, N.v6.
  rewrite !state_r1279_nr_5F1279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1279_nr_5F1279 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28271 (s : N.State) (i : N.Inputs) :
  R.v28271 (state s) (inputs i) = Zmod.unsigned (N.v28271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28271 s i)) at 1.
  unfold R.v28271, N.v28271.
  unfold R.v6, N.v6.
  rewrite !state_r1278_nr_5F1278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1278_nr_5F1278 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28272 (s : N.State) (i : N.Inputs) :
  R.v28272 (state s) (inputs i) = Zmod.unsigned (N.v28272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28272 s i)) at 1.
  unfold R.v28272, N.v28272.
  rewrite ?node_28270.
  rewrite ?node_28271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28273 (s : N.State) (i : N.Inputs) :
  R.v28273 (state s) (inputs i) = Zmod.unsigned (N.v28273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28273 s i)) at 1.
  unfold R.v28273, N.v28273.
  unfold R.v16484, N.v16484.
  rewrite ?node_28272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28274 (s : N.State) (i : N.Inputs) :
  R.v28274 (state s) (inputs i) = Zmod.unsigned (N.v28274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28274 s i)) at 1.
  unfold R.v28274, N.v28274.
  rewrite ?node_28269.
  rewrite ?node_28273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28275 (s : N.State) (i : N.Inputs) :
  R.v28275 (state s) (inputs i) = Zmod.unsigned (N.v28275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28275 s i)) at 1.
  unfold R.v28275, N.v28275.
  unfold R.v6, N.v6.
  rewrite ?node_28274.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28276 (s : N.State) (i : N.Inputs) :
  R.v28276 (state s) (inputs i) = Zmod.unsigned (N.v28276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28276 s i)) at 1.
  unfold R.v28276, N.v28276.
  rewrite ?node_10972.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28277 (s : N.State) (i : N.Inputs) :
  R.v28277 (state s) (inputs i) = Zmod.unsigned (N.v28277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28277 s i)) at 1.
  unfold R.v28277, N.v28277.
  unfold R.v6, N.v6.
  rewrite ?node_11137.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28278 (s : N.State) (i : N.Inputs) :
  R.v28278 (state s) (inputs i) = Zmod.unsigned (N.v28278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28278 s i)) at 1.
  unfold R.v28278, N.v28278.
  rewrite ?node_28276.
  rewrite ?node_28277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28279 (s : N.State) (i : N.Inputs) :
  R.v28279 (state s) (inputs i) = Zmod.unsigned (N.v28279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28279 s i)) at 1.
  unfold R.v28279, N.v28279.
  rewrite ?node_28275.
  rewrite ?node_28278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28280 (s : N.State) (i : N.Inputs) :
  R.v28280 (state s) (inputs i) = Zmod.unsigned (N.v28280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28280 s i)) at 1.
  unfold R.v28280, N.v28280.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28281 (s : N.State) (i : N.Inputs) :
  R.v28281 (state s) (inputs i) = Zmod.unsigned (N.v28281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28281 s i)) at 1.
  unfold R.v28281, N.v28281.
  rewrite ?node_10976.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28282 (s : N.State) (i : N.Inputs) :
  R.v28282 (state s) (inputs i) = Zmod.unsigned (N.v28282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28282 s i)) at 1.
  unfold R.v28282, N.v28282.
  unfold R.v6, N.v6.
  rewrite !state_r1281_nr_5F1281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1281_nr_5F1281 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28283 (s : N.State) (i : N.Inputs) :
  R.v28283 (state s) (inputs i) = Zmod.unsigned (N.v28283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28283 s i)) at 1.
  unfold R.v28283, N.v28283.
  unfold R.v6, N.v6.
  rewrite ?node_10972.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28284 (s : N.State) (i : N.Inputs) :
  R.v28284 (state s) (inputs i) = Zmod.unsigned (N.v28284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28284 s i)) at 1.
  unfold R.v28284, N.v28284.
  rewrite ?node_28282.
  rewrite ?node_28283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28285 (s : N.State) (i : N.Inputs) :
  R.v28285 (state s) (inputs i) = Zmod.unsigned (N.v28285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28285 s i)) at 1.
  unfold R.v28285, N.v28285.
  unfold R.v16484, N.v16484.
  rewrite ?node_28284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28286 (s : N.State) (i : N.Inputs) :
  R.v28286 (state s) (inputs i) = Zmod.unsigned (N.v28286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28286 s i)) at 1.
  unfold R.v28286, N.v28286.
  rewrite ?node_28281.
  rewrite ?node_28285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28287 (s : N.State) (i : N.Inputs) :
  R.v28287 (state s) (inputs i) = Zmod.unsigned (N.v28287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28287 s i)) at 1.
  unfold R.v28287, N.v28287.
  unfold R.v6, N.v6.
  rewrite ?node_28286.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28288 (s : N.State) (i : N.Inputs) :
  R.v28288 (state s) (inputs i) = Zmod.unsigned (N.v28288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28288 s i)) at 1.
  unfold R.v28288, N.v28288.
  rewrite ?node_10977.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28289 (s : N.State) (i : N.Inputs) :
  R.v28289 (state s) (inputs i) = Zmod.unsigned (N.v28289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28289 s i)) at 1.
  unfold R.v28289, N.v28289.
  unfold R.v6, N.v6.
  rewrite ?node_11182.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28290 (s : N.State) (i : N.Inputs) :
  R.v28290 (state s) (inputs i) = Zmod.unsigned (N.v28290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28290 s i)) at 1.
  unfold R.v28290, N.v28290.
  rewrite ?node_28288.
  rewrite ?node_28289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28291 (s : N.State) (i : N.Inputs) :
  R.v28291 (state s) (inputs i) = Zmod.unsigned (N.v28291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28291 s i)) at 1.
  unfold R.v28291, N.v28291.
  rewrite ?node_28287.
  rewrite ?node_28290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28292 (s : N.State) (i : N.Inputs) :
  R.v28292 (state s) (inputs i) = Zmod.unsigned (N.v28292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28292 s i)) at 1.
  unfold R.v28292, N.v28292.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28293 (s : N.State) (i : N.Inputs) :
  R.v28293 (state s) (inputs i) = Zmod.unsigned (N.v28293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28293 s i)) at 1.
  unfold R.v28293, N.v28293.
  rewrite ?node_10984.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28294 (s : N.State) (i : N.Inputs) :
  R.v28294 (state s) (inputs i) = Zmod.unsigned (N.v28294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28294 s i)) at 1.
  unfold R.v28294, N.v28294.
  unfold R.v16463, N.v16463.
  rewrite !state_r1285_nr_5F1285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1285_nr_5F1285 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28295 (s : N.State) (i : N.Inputs) :
  R.v28295 (state s) (inputs i) = Zmod.unsigned (N.v28295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28295 s i)) at 1.
  unfold R.v28295, N.v28295.
  unfold R.v16463, N.v16463.
  rewrite !state_r1284_nr_5F1284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1284_nr_5F1284 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28296 (s : N.State) (i : N.Inputs) :
  R.v28296 (state s) (inputs i) = Zmod.unsigned (N.v28296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28296 s i)) at 1.
  unfold R.v28296, N.v28296.
  unfold R.v6, N.v6.
  rewrite !state_r1283_nr_5F1283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1283_nr_5F1283 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28297 (s : N.State) (i : N.Inputs) :
  R.v28297 (state s) (inputs i) = Zmod.unsigned (N.v28297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28297 s i)) at 1.
  unfold R.v28297, N.v28297.
  unfold R.v6, N.v6.
  rewrite !state_r1282_nr_5F1282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1282_nr_5F1282 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28298 (s : N.State) (i : N.Inputs) :
  R.v28298 (state s) (inputs i) = Zmod.unsigned (N.v28298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28298 s i)) at 1.
  unfold R.v28298, N.v28298.
  rewrite ?node_28296.
  rewrite ?node_28297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28299 (s : N.State) (i : N.Inputs) :
  R.v28299 (state s) (inputs i) = Zmod.unsigned (N.v28299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28299 s i)) at 1.
  unfold R.v28299, N.v28299.
  unfold R.v16484, N.v16484.
  rewrite ?node_28298.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28300 (s : N.State) (i : N.Inputs) :
  R.v28300 (state s) (inputs i) = Zmod.unsigned (N.v28300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28300 s i)) at 1.
  unfold R.v28300, N.v28300.
  rewrite ?node_28293.
  rewrite ?node_28294.
  rewrite ?node_28295.
  rewrite ?node_28299.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28301 (s : N.State) (i : N.Inputs) :
  R.v28301 (state s) (inputs i) = Zmod.unsigned (N.v28301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28301 s i)) at 1.
  unfold R.v28301, N.v28301.
  unfold R.v6, N.v6.
  rewrite ?node_28300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28302 (s : N.State) (i : N.Inputs) :
  R.v28302 (state s) (inputs i) = Zmod.unsigned (N.v28302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28302 s i)) at 1.
  unfold R.v28302, N.v28302.
  rewrite ?node_10985.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28303 (s : N.State) (i : N.Inputs) :
  R.v28303 (state s) (inputs i) = Zmod.unsigned (N.v28303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28303 s i)) at 1.
  unfold R.v28303, N.v28303.
  unfold R.v6, N.v6.
  rewrite ?node_11145.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28304 (s : N.State) (i : N.Inputs) :
  R.v28304 (state s) (inputs i) = Zmod.unsigned (N.v28304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28304 s i)) at 1.
  unfold R.v28304, N.v28304.
  unfold R.v6, N.v6.
  rewrite ?node_11186.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28305 (s : N.State) (i : N.Inputs) :
  R.v28305 (state s) (inputs i) = Zmod.unsigned (N.v28305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28305 s i)) at 1.
  unfold R.v28305, N.v28305.
  rewrite ?node_28302.
  rewrite ?node_28303.
  rewrite ?node_28304.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28306 (s : N.State) (i : N.Inputs) :
  R.v28306 (state s) (inputs i) = Zmod.unsigned (N.v28306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28306 s i)) at 1.
  unfold R.v28306, N.v28306.
  rewrite ?node_28301.
  rewrite ?node_28305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28307 (s : N.State) (i : N.Inputs) :
  R.v28307 (state s) (inputs i) = Zmod.unsigned (N.v28307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28307 s i)) at 1.
  unfold R.v28307, N.v28307.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28308 (s : N.State) (i : N.Inputs) :
  R.v28308 (state s) (inputs i) = Zmod.unsigned (N.v28308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28308 s i)) at 1.
  unfold R.v28308, N.v28308.
  unfold R.v16463, N.v16463.
  rewrite !state_r1284_nr_5F1284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1284_nr_5F1284 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28309 (s : N.State) (i : N.Inputs) :
  R.v28309 (state s) (inputs i) = Zmod.unsigned (N.v28309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28309 s i)) at 1.
  unfold R.v28309, N.v28309.
  unfold R.v6, N.v6.
  rewrite !state_r1283_nr_5F1283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1283_nr_5F1283 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28310 (s : N.State) (i : N.Inputs) :
  R.v28310 (state s) (inputs i) = Zmod.unsigned (N.v28310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28310 s i)) at 1.
  unfold R.v28310, N.v28310.
  unfold R.v6, N.v6.
  rewrite !state_r1282_nr_5F1282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1282_nr_5F1282 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28311 (s : N.State) (i : N.Inputs) :
  R.v28311 (state s) (inputs i) = Zmod.unsigned (N.v28311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28311 s i)) at 1.
  unfold R.v28311, N.v28311.
  rewrite ?node_28309.
  rewrite ?node_28310.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28312 (s : N.State) (i : N.Inputs) :
  R.v28312 (state s) (inputs i) = Zmod.unsigned (N.v28312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28312 s i)) at 1.
  unfold R.v28312, N.v28312.
  unfold R.v16484, N.v16484.
  rewrite ?node_28311.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28313 (s : N.State) (i : N.Inputs) :
  R.v28313 (state s) (inputs i) = Zmod.unsigned (N.v28313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28313 s i)) at 1.
  unfold R.v28313, N.v28313.
  rewrite ?node_28308.
  rewrite ?node_28312.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28314 (s : N.State) (i : N.Inputs) :
  R.v28314 (state s) (inputs i) = Zmod.unsigned (N.v28314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28314 s i)) at 1.
  unfold R.v28314, N.v28314.
  unfold R.v6, N.v6.
  rewrite ?node_28313.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28315 (s : N.State) (i : N.Inputs) :
  R.v28315 (state s) (inputs i) = Zmod.unsigned (N.v28315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28315 s i)) at 1.
  unfold R.v28315, N.v28315.
  rewrite ?node_10980.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28316 (s : N.State) (i : N.Inputs) :
  R.v28316 (state s) (inputs i) = Zmod.unsigned (N.v28316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28316 s i)) at 1.
  unfold R.v28316, N.v28316.
  unfold R.v6, N.v6.
  rewrite ?node_11145.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28317 (s : N.State) (i : N.Inputs) :
  R.v28317 (state s) (inputs i) = Zmod.unsigned (N.v28317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28317 s i)) at 1.
  unfold R.v28317, N.v28317.
  rewrite ?node_28315.
  rewrite ?node_28316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28318 (s : N.State) (i : N.Inputs) :
  R.v28318 (state s) (inputs i) = Zmod.unsigned (N.v28318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28318 s i)) at 1.
  unfold R.v28318, N.v28318.
  rewrite ?node_28314.
  rewrite ?node_28317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28319 (s : N.State) (i : N.Inputs) :
  R.v28319 (state s) (inputs i) = Zmod.unsigned (N.v28319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28319 s i)) at 1.
  unfold R.v28319, N.v28319.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28320 (s : N.State) (i : N.Inputs) :
  R.v28320 (state s) (inputs i) = Zmod.unsigned (N.v28320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28320 s i)) at 1.
  unfold R.v28320, N.v28320.
  rewrite ?node_10984.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28321 (s : N.State) (i : N.Inputs) :
  R.v28321 (state s) (inputs i) = Zmod.unsigned (N.v28321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28321 s i)) at 1.
  unfold R.v28321, N.v28321.
  unfold R.v6, N.v6.
  rewrite !state_r1285_nr_5F1285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1285_nr_5F1285 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28322 (s : N.State) (i : N.Inputs) :
  R.v28322 (state s) (inputs i) = Zmod.unsigned (N.v28322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28322 s i)) at 1.
  unfold R.v28322, N.v28322.
  unfold R.v6, N.v6.
  rewrite ?node_10980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28323 (s : N.State) (i : N.Inputs) :
  R.v28323 (state s) (inputs i) = Zmod.unsigned (N.v28323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28323 s i)) at 1.
  unfold R.v28323, N.v28323.
  rewrite ?node_28321.
  rewrite ?node_28322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28324 (s : N.State) (i : N.Inputs) :
  R.v28324 (state s) (inputs i) = Zmod.unsigned (N.v28324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28324 s i)) at 1.
  unfold R.v28324, N.v28324.
  unfold R.v16484, N.v16484.
  rewrite ?node_28323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28325 (s : N.State) (i : N.Inputs) :
  R.v28325 (state s) (inputs i) = Zmod.unsigned (N.v28325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28325 s i)) at 1.
  unfold R.v28325, N.v28325.
  rewrite ?node_28320.
  rewrite ?node_28324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28326 (s : N.State) (i : N.Inputs) :
  R.v28326 (state s) (inputs i) = Zmod.unsigned (N.v28326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28326 s i)) at 1.
  unfold R.v28326, N.v28326.
  unfold R.v6, N.v6.
  rewrite ?node_28325.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28327 (s : N.State) (i : N.Inputs) :
  R.v28327 (state s) (inputs i) = Zmod.unsigned (N.v28327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28327 s i)) at 1.
  unfold R.v28327, N.v28327.
  rewrite ?node_10985.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28328 (s : N.State) (i : N.Inputs) :
  R.v28328 (state s) (inputs i) = Zmod.unsigned (N.v28328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28328 s i)) at 1.
  unfold R.v28328, N.v28328.
  unfold R.v6, N.v6.
  rewrite ?node_11186.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28329 (s : N.State) (i : N.Inputs) :
  R.v28329 (state s) (inputs i) = Zmod.unsigned (N.v28329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28329 s i)) at 1.
  unfold R.v28329, N.v28329.
  rewrite ?node_28327.
  rewrite ?node_28328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28330 (s : N.State) (i : N.Inputs) :
  R.v28330 (state s) (inputs i) = Zmod.unsigned (N.v28330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28330 s i)) at 1.
  unfold R.v28330, N.v28330.
  rewrite ?node_28326.
  rewrite ?node_28329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28331 (s : N.State) (i : N.Inputs) :
  R.v28331 (state s) (inputs i) = Zmod.unsigned (N.v28331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28331 s i)) at 1.
  unfold R.v28331, N.v28331.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28332 (s : N.State) (i : N.Inputs) :
  R.v28332 (state s) (inputs i) = Zmod.unsigned (N.v28332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28332 s i)) at 1.
  unfold R.v28332, N.v28332.
  rewrite ?node_11087.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28333 (s : N.State) (i : N.Inputs) :
  R.v28333 (state s) (inputs i) = Zmod.unsigned (N.v28333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28333 s i)) at 1.
  unfold R.v28333, N.v28333.
  unfold R.v16463, N.v16463.
  rewrite !state_r1289_nr_5F1290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1289_nr_5F1290 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28334 (s : N.State) (i : N.Inputs) :
  R.v28334 (state s) (inputs i) = Zmod.unsigned (N.v28334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28334 s i)) at 1.
  unfold R.v28334, N.v28334.
  unfold R.v16463, N.v16463.
  rewrite !state_r1288_nr_5F1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1288_nr_5F1289 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28335 (s : N.State) (i : N.Inputs) :
  R.v28335 (state s) (inputs i) = Zmod.unsigned (N.v28335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28335 s i)) at 1.
  unfold R.v28335, N.v28335.
  unfold R.v6, N.v6.
  rewrite !state_r1287_nr_5F1288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1287_nr_5F1288 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28336 (s : N.State) (i : N.Inputs) :
  R.v28336 (state s) (inputs i) = Zmod.unsigned (N.v28336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28336 s i)) at 1.
  unfold R.v28336, N.v28336.
  unfold R.v19, N.v19.
  rewrite ?node_28335.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28337 (s : N.State) (i : N.Inputs) :
  R.v28337 (state s) (inputs i) = Zmod.unsigned (N.v28337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28337 s i)) at 1.
  unfold R.v28337, N.v28337.
  unfold R.v16484, N.v16484.
  rewrite ?node_28336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28338 (s : N.State) (i : N.Inputs) :
  R.v28338 (state s) (inputs i) = Zmod.unsigned (N.v28338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28338 s i)) at 1.
  unfold R.v28338, N.v28338.
  rewrite ?node_28332.
  rewrite ?node_28333.
  rewrite ?node_28334.
  rewrite ?node_28337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28339 (s : N.State) (i : N.Inputs) :
  R.v28339 (state s) (inputs i) = Zmod.unsigned (N.v28339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28339 s i)) at 1.
  unfold R.v28339, N.v28339.
  unfold R.v6, N.v6.
  rewrite ?node_28338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28340 (s : N.State) (i : N.Inputs) :
  R.v28340 (state s) (inputs i) = Zmod.unsigned (N.v28340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28340 s i)) at 1.
  unfold R.v28340, N.v28340.
  rewrite ?node_11088.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28341 (s : N.State) (i : N.Inputs) :
  R.v28341 (state s) (inputs i) = Zmod.unsigned (N.v28341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28341 s i)) at 1.
  unfold R.v28341, N.v28341.
  unfold R.v6, N.v6.
  rewrite ?node_11246.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28342 (s : N.State) (i : N.Inputs) :
  R.v28342 (state s) (inputs i) = Zmod.unsigned (N.v28342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28342 s i)) at 1.
  unfold R.v28342, N.v28342.
  unfold R.v6, N.v6.
  rewrite ?node_11312.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28343 (s : N.State) (i : N.Inputs) :
  R.v28343 (state s) (inputs i) = Zmod.unsigned (N.v28343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28343 s i)) at 1.
  unfold R.v28343, N.v28343.
  rewrite ?node_28340.
  rewrite ?node_28341.
  rewrite ?node_28342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28344 (s : N.State) (i : N.Inputs) :
  R.v28344 (state s) (inputs i) = Zmod.unsigned (N.v28344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28344 s i)) at 1.
  unfold R.v28344, N.v28344.
  rewrite ?node_28339.
  rewrite ?node_28343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28345 (s : N.State) (i : N.Inputs) :
  R.v28345 (state s) (inputs i) = Zmod.unsigned (N.v28345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28345 s i)) at 1.
  unfold R.v28345, N.v28345.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28346 (s : N.State) (i : N.Inputs) :
  R.v28346 (state s) (inputs i) = Zmod.unsigned (N.v28346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28346 s i)) at 1.
  unfold R.v28346, N.v28346.
  unfold R.v16463, N.v16463.
  rewrite !state_r1288_nr_5F1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1288_nr_5F1289 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28347 (s : N.State) (i : N.Inputs) :
  R.v28347 (state s) (inputs i) = Zmod.unsigned (N.v28347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28347 s i)) at 1.
  unfold R.v28347, N.v28347.
  unfold R.v6, N.v6.
  rewrite !state_r1287_nr_5F1288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1287_nr_5F1288 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28348 (s : N.State) (i : N.Inputs) :
  R.v28348 (state s) (inputs i) = Zmod.unsigned (N.v28348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28348 s i)) at 1.
  unfold R.v28348, N.v28348.
  unfold R.v19, N.v19.
  rewrite ?node_28347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28349 (s : N.State) (i : N.Inputs) :
  R.v28349 (state s) (inputs i) = Zmod.unsigned (N.v28349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28349 s i)) at 1.
  unfold R.v28349, N.v28349.
  unfold R.v16484, N.v16484.
  rewrite ?node_28348.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28350 (s : N.State) (i : N.Inputs) :
  R.v28350 (state s) (inputs i) = Zmod.unsigned (N.v28350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28350 s i)) at 1.
  unfold R.v28350, N.v28350.
  rewrite ?node_28346.
  rewrite ?node_28349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28351 (s : N.State) (i : N.Inputs) :
  R.v28351 (state s) (inputs i) = Zmod.unsigned (N.v28351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28351 s i)) at 1.
  unfold R.v28351, N.v28351.
  unfold R.v6, N.v6.
  rewrite ?node_28350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28352 (s : N.State) (i : N.Inputs) :
  R.v28352 (state s) (inputs i) = Zmod.unsigned (N.v28352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28352 s i)) at 1.
  unfold R.v28352, N.v28352.
  rewrite ?node_11083.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28353 (s : N.State) (i : N.Inputs) :
  R.v28353 (state s) (inputs i) = Zmod.unsigned (N.v28353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28353 s i)) at 1.
  unfold R.v28353, N.v28353.
  unfold R.v6, N.v6.
  rewrite ?node_11246.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28354 (s : N.State) (i : N.Inputs) :
  R.v28354 (state s) (inputs i) = Zmod.unsigned (N.v28354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28354 s i)) at 1.
  unfold R.v28354, N.v28354.
  rewrite ?node_28352.
  rewrite ?node_28353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28355 (s : N.State) (i : N.Inputs) :
  R.v28355 (state s) (inputs i) = Zmod.unsigned (N.v28355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28355 s i)) at 1.
  unfold R.v28355, N.v28355.
  rewrite ?node_28351.
  rewrite ?node_28354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28356 (s : N.State) (i : N.Inputs) :
  R.v28356 (state s) (inputs i) = Zmod.unsigned (N.v28356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28356 s i)) at 1.
  unfold R.v28356, N.v28356.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28357 (s : N.State) (i : N.Inputs) :
  R.v28357 (state s) (inputs i) = Zmod.unsigned (N.v28357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28357 s i)) at 1.
  unfold R.v28357, N.v28357.
  rewrite ?node_11087.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28358 (s : N.State) (i : N.Inputs) :
  R.v28358 (state s) (inputs i) = Zmod.unsigned (N.v28358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28358 s i)) at 1.
  unfold R.v28358, N.v28358.
  unfold R.v6, N.v6.
  rewrite !state_r1289_nr_5F1290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1289_nr_5F1290 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28359 (s : N.State) (i : N.Inputs) :
  R.v28359 (state s) (inputs i) = Zmod.unsigned (N.v28359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28359 s i)) at 1.
  unfold R.v28359, N.v28359.
  unfold R.v6, N.v6.
  rewrite ?node_11083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28360 (s : N.State) (i : N.Inputs) :
  R.v28360 (state s) (inputs i) = Zmod.unsigned (N.v28360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28360 s i)) at 1.
  unfold R.v28360, N.v28360.
  rewrite ?node_28358.
  rewrite ?node_28359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28361 (s : N.State) (i : N.Inputs) :
  R.v28361 (state s) (inputs i) = Zmod.unsigned (N.v28361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28361 s i)) at 1.
  unfold R.v28361, N.v28361.
  unfold R.v16484, N.v16484.
  rewrite ?node_28360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28362 (s : N.State) (i : N.Inputs) :
  R.v28362 (state s) (inputs i) = Zmod.unsigned (N.v28362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28362 s i)) at 1.
  unfold R.v28362, N.v28362.
  rewrite ?node_28357.
  rewrite ?node_28361.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28363 (s : N.State) (i : N.Inputs) :
  R.v28363 (state s) (inputs i) = Zmod.unsigned (N.v28363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28363 s i)) at 1.
  unfold R.v28363, N.v28363.
  unfold R.v6, N.v6.
  rewrite ?node_28362.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28364 (s : N.State) (i : N.Inputs) :
  R.v28364 (state s) (inputs i) = Zmod.unsigned (N.v28364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28364 s i)) at 1.
  unfold R.v28364, N.v28364.
  rewrite ?node_11088.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28365 (s : N.State) (i : N.Inputs) :
  R.v28365 (state s) (inputs i) = Zmod.unsigned (N.v28365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28365 s i)) at 1.
  unfold R.v28365, N.v28365.
  unfold R.v6, N.v6.
  rewrite ?node_11312.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28366 (s : N.State) (i : N.Inputs) :
  R.v28366 (state s) (inputs i) = Zmod.unsigned (N.v28366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28366 s i)) at 1.
  unfold R.v28366, N.v28366.
  rewrite ?node_28364.
  rewrite ?node_28365.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28367 (s : N.State) (i : N.Inputs) :
  R.v28367 (state s) (inputs i) = Zmod.unsigned (N.v28367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28367 s i)) at 1.
  unfold R.v28367, N.v28367.
  rewrite ?node_28363.
  rewrite ?node_28366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28368 (s : N.State) (i : N.Inputs) :
  R.v28368 (state s) (inputs i) = Zmod.unsigned (N.v28368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28368 s i)) at 1.
  unfold R.v28368, N.v28368.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28369 (s : N.State) (i : N.Inputs) :
  R.v28369 (state s) (inputs i) = Zmod.unsigned (N.v28369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28369 s i)) at 1.
  unfold R.v28369, N.v28369.
  rewrite ?node_11094.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28370 (s : N.State) (i : N.Inputs) :
  R.v28370 (state s) (inputs i) = Zmod.unsigned (N.v28370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28370 s i)) at 1.
  unfold R.v28370, N.v28370.
  unfold R.v16463, N.v16463.
  rewrite !state_r1293_nr_5F1294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1293_nr_5F1294 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28371 (s : N.State) (i : N.Inputs) :
  R.v28371 (state s) (inputs i) = Zmod.unsigned (N.v28371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28371 s i)) at 1.
  unfold R.v28371, N.v28371.
  unfold R.v16463, N.v16463.
  rewrite !state_r1292_nr_5F1293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1292_nr_5F1293 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28372 (s : N.State) (i : N.Inputs) :
  R.v28372 (state s) (inputs i) = Zmod.unsigned (N.v28372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28372 s i)) at 1.
  unfold R.v28372, N.v28372.
  unfold R.v6, N.v6.
  rewrite !state_r1291_nr_5F1292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1291_nr_5F1292 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28373 (s : N.State) (i : N.Inputs) :
  R.v28373 (state s) (inputs i) = Zmod.unsigned (N.v28373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28373 s i)) at 1.
  unfold R.v28373, N.v28373.
  unfold R.v6, N.v6.
  rewrite !state_r1290_nr_5F1291.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1290_nr_5F1291 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28374 (s : N.State) (i : N.Inputs) :
  R.v28374 (state s) (inputs i) = Zmod.unsigned (N.v28374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28374 s i)) at 1.
  unfold R.v28374, N.v28374.
  rewrite ?node_28372.
  rewrite ?node_28373.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28375 (s : N.State) (i : N.Inputs) :
  R.v28375 (state s) (inputs i) = Zmod.unsigned (N.v28375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28375 s i)) at 1.
  unfold R.v28375, N.v28375.
  unfold R.v16484, N.v16484.
  rewrite ?node_28374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28376 (s : N.State) (i : N.Inputs) :
  R.v28376 (state s) (inputs i) = Zmod.unsigned (N.v28376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28376 s i)) at 1.
  unfold R.v28376, N.v28376.
  rewrite ?node_28369.
  rewrite ?node_28370.
  rewrite ?node_28371.
  rewrite ?node_28375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28377 (s : N.State) (i : N.Inputs) :
  R.v28377 (state s) (inputs i) = Zmod.unsigned (N.v28377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28377 s i)) at 1.
  unfold R.v28377, N.v28377.
  unfold R.v6, N.v6.
  rewrite ?node_28376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28378 (s : N.State) (i : N.Inputs) :
  R.v28378 (state s) (inputs i) = Zmod.unsigned (N.v28378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28378 s i)) at 1.
  unfold R.v28378, N.v28378.
  rewrite ?node_11095.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28379 (s : N.State) (i : N.Inputs) :
  R.v28379 (state s) (inputs i) = Zmod.unsigned (N.v28379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28379 s i)) at 1.
  unfold R.v28379, N.v28379.
  unfold R.v6, N.v6.
  rewrite ?node_11253.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28380 (s : N.State) (i : N.Inputs) :
  R.v28380 (state s) (inputs i) = Zmod.unsigned (N.v28380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28380 s i)) at 1.
  unfold R.v28380, N.v28380.
  unfold R.v6, N.v6.
  rewrite ?node_11316.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28381 (s : N.State) (i : N.Inputs) :
  R.v28381 (state s) (inputs i) = Zmod.unsigned (N.v28381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28381 s i)) at 1.
  unfold R.v28381, N.v28381.
  rewrite ?node_28378.
  rewrite ?node_28379.
  rewrite ?node_28380.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28382 (s : N.State) (i : N.Inputs) :
  R.v28382 (state s) (inputs i) = Zmod.unsigned (N.v28382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28382 s i)) at 1.
  unfold R.v28382, N.v28382.
  rewrite ?node_28377.
  rewrite ?node_28381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28383 (s : N.State) (i : N.Inputs) :
  R.v28383 (state s) (inputs i) = Zmod.unsigned (N.v28383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28383 s i)) at 1.
  unfold R.v28383, N.v28383.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28384 (s : N.State) (i : N.Inputs) :
  R.v28384 (state s) (inputs i) = Zmod.unsigned (N.v28384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28384 s i)) at 1.
  unfold R.v28384, N.v28384.
  unfold R.v16463, N.v16463.
  rewrite !state_r1292_nr_5F1293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1292_nr_5F1293 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28385 (s : N.State) (i : N.Inputs) :
  R.v28385 (state s) (inputs i) = Zmod.unsigned (N.v28385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28385 s i)) at 1.
  unfold R.v28385, N.v28385.
  unfold R.v6, N.v6.
  rewrite !state_r1291_nr_5F1292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1291_nr_5F1292 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28386 (s : N.State) (i : N.Inputs) :
  R.v28386 (state s) (inputs i) = Zmod.unsigned (N.v28386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28386 s i)) at 1.
  unfold R.v28386, N.v28386.
  unfold R.v6, N.v6.
  rewrite !state_r1290_nr_5F1291.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1290_nr_5F1291 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28387 (s : N.State) (i : N.Inputs) :
  R.v28387 (state s) (inputs i) = Zmod.unsigned (N.v28387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28387 s i)) at 1.
  unfold R.v28387, N.v28387.
  rewrite ?node_28385.
  rewrite ?node_28386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28388 (s : N.State) (i : N.Inputs) :
  R.v28388 (state s) (inputs i) = Zmod.unsigned (N.v28388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28388 s i)) at 1.
  unfold R.v28388, N.v28388.
  unfold R.v16484, N.v16484.
  rewrite ?node_28387.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28389 (s : N.State) (i : N.Inputs) :
  R.v28389 (state s) (inputs i) = Zmod.unsigned (N.v28389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28389 s i)) at 1.
  unfold R.v28389, N.v28389.
  rewrite ?node_28384.
  rewrite ?node_28388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28390 (s : N.State) (i : N.Inputs) :
  R.v28390 (state s) (inputs i) = Zmod.unsigned (N.v28390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28390 s i)) at 1.
  unfold R.v28390, N.v28390.
  unfold R.v6, N.v6.
  rewrite ?node_28389.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28391 (s : N.State) (i : N.Inputs) :
  R.v28391 (state s) (inputs i) = Zmod.unsigned (N.v28391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28391 s i)) at 1.
  unfold R.v28391, N.v28391.
  rewrite ?node_11090.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28392 (s : N.State) (i : N.Inputs) :
  R.v28392 (state s) (inputs i) = Zmod.unsigned (N.v28392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28392 s i)) at 1.
  unfold R.v28392, N.v28392.
  unfold R.v6, N.v6.
  rewrite ?node_11253.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28393 (s : N.State) (i : N.Inputs) :
  R.v28393 (state s) (inputs i) = Zmod.unsigned (N.v28393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28393 s i)) at 1.
  unfold R.v28393, N.v28393.
  rewrite ?node_28391.
  rewrite ?node_28392.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28394 (s : N.State) (i : N.Inputs) :
  R.v28394 (state s) (inputs i) = Zmod.unsigned (N.v28394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28394 s i)) at 1.
  unfold R.v28394, N.v28394.
  rewrite ?node_28390.
  rewrite ?node_28393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28395 (s : N.State) (i : N.Inputs) :
  R.v28395 (state s) (inputs i) = Zmod.unsigned (N.v28395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28395 s i)) at 1.
  unfold R.v28395, N.v28395.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28396 (s : N.State) (i : N.Inputs) :
  R.v28396 (state s) (inputs i) = Zmod.unsigned (N.v28396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28396 s i)) at 1.
  unfold R.v28396, N.v28396.
  rewrite ?node_11094.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28397 (s : N.State) (i : N.Inputs) :
  R.v28397 (state s) (inputs i) = Zmod.unsigned (N.v28397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28397 s i)) at 1.
  unfold R.v28397, N.v28397.
  unfold R.v6, N.v6.
  rewrite !state_r1293_nr_5F1294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1293_nr_5F1294 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28398 (s : N.State) (i : N.Inputs) :
  R.v28398 (state s) (inputs i) = Zmod.unsigned (N.v28398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28398 s i)) at 1.
  unfold R.v28398, N.v28398.
  unfold R.v6, N.v6.
  rewrite ?node_11090.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28399 (s : N.State) (i : N.Inputs) :
  R.v28399 (state s) (inputs i) = Zmod.unsigned (N.v28399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28399 s i)) at 1.
  unfold R.v28399, N.v28399.
  rewrite ?node_28397.
  rewrite ?node_28398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28400 (s : N.State) (i : N.Inputs) :
  R.v28400 (state s) (inputs i) = Zmod.unsigned (N.v28400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28400 s i)) at 1.
  unfold R.v28400, N.v28400.
  unfold R.v16484, N.v16484.
  rewrite ?node_28399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28401 (s : N.State) (i : N.Inputs) :
  R.v28401 (state s) (inputs i) = Zmod.unsigned (N.v28401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28401 s i)) at 1.
  unfold R.v28401, N.v28401.
  rewrite ?node_28396.
  rewrite ?node_28400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28402 (s : N.State) (i : N.Inputs) :
  R.v28402 (state s) (inputs i) = Zmod.unsigned (N.v28402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28402 s i)) at 1.
  unfold R.v28402, N.v28402.
  unfold R.v6, N.v6.
  rewrite ?node_28401.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28403 (s : N.State) (i : N.Inputs) :
  R.v28403 (state s) (inputs i) = Zmod.unsigned (N.v28403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28403 s i)) at 1.
  unfold R.v28403, N.v28403.
  rewrite ?node_11095.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28404 (s : N.State) (i : N.Inputs) :
  R.v28404 (state s) (inputs i) = Zmod.unsigned (N.v28404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28404 s i)) at 1.
  unfold R.v28404, N.v28404.
  unfold R.v6, N.v6.
  rewrite ?node_11316.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28405 (s : N.State) (i : N.Inputs) :
  R.v28405 (state s) (inputs i) = Zmod.unsigned (N.v28405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28405 s i)) at 1.
  unfold R.v28405, N.v28405.
  rewrite ?node_28403.
  rewrite ?node_28404.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28406 (s : N.State) (i : N.Inputs) :
  R.v28406 (state s) (inputs i) = Zmod.unsigned (N.v28406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28406 s i)) at 1.
  unfold R.v28406, N.v28406.
  rewrite ?node_28402.
  rewrite ?node_28405.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28407 (s : N.State) (i : N.Inputs) :
  R.v28407 (state s) (inputs i) = Zmod.unsigned (N.v28407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28407 s i)) at 1.
  unfold R.v28407, N.v28407.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28408 (s : N.State) (i : N.Inputs) :
  R.v28408 (state s) (inputs i) = Zmod.unsigned (N.v28408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28408 s i)) at 1.
  unfold R.v28408, N.v28408.
  rewrite ?node_11102.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28409 (s : N.State) (i : N.Inputs) :
  R.v28409 (state s) (inputs i) = Zmod.unsigned (N.v28409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28409 s i)) at 1.
  unfold R.v28409, N.v28409.
  unfold R.v16463, N.v16463.
  rewrite !state_r1297_nr_5F1298.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1297_nr_5F1298 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28410 (s : N.State) (i : N.Inputs) :
  R.v28410 (state s) (inputs i) = Zmod.unsigned (N.v28410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28410 s i)) at 1.
  unfold R.v28410, N.v28410.
  unfold R.v16463, N.v16463.
  rewrite !state_r1296_nr_5F1297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1296_nr_5F1297 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28411 (s : N.State) (i : N.Inputs) :
  R.v28411 (state s) (inputs i) = Zmod.unsigned (N.v28411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28411 s i)) at 1.
  unfold R.v28411, N.v28411.
  unfold R.v6, N.v6.
  rewrite !state_r1295_nr_5F1296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1295_nr_5F1296 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28412 (s : N.State) (i : N.Inputs) :
  R.v28412 (state s) (inputs i) = Zmod.unsigned (N.v28412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28412 s i)) at 1.
  unfold R.v28412, N.v28412.
  unfold R.v6, N.v6.
  rewrite !state_r1294_nr_5F1295.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1294_nr_5F1295 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28413 (s : N.State) (i : N.Inputs) :
  R.v28413 (state s) (inputs i) = Zmod.unsigned (N.v28413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28413 s i)) at 1.
  unfold R.v28413, N.v28413.
  rewrite ?node_28411.
  rewrite ?node_28412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28414 (s : N.State) (i : N.Inputs) :
  R.v28414 (state s) (inputs i) = Zmod.unsigned (N.v28414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28414 s i)) at 1.
  unfold R.v28414, N.v28414.
  unfold R.v16484, N.v16484.
  rewrite ?node_28413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28415 (s : N.State) (i : N.Inputs) :
  R.v28415 (state s) (inputs i) = Zmod.unsigned (N.v28415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28415 s i)) at 1.
  unfold R.v28415, N.v28415.
  rewrite ?node_28408.
  rewrite ?node_28409.
  rewrite ?node_28410.
  rewrite ?node_28414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28416 (s : N.State) (i : N.Inputs) :
  R.v28416 (state s) (inputs i) = Zmod.unsigned (N.v28416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28416 s i)) at 1.
  unfold R.v28416, N.v28416.
  unfold R.v6, N.v6.
  rewrite ?node_28415.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28417 (s : N.State) (i : N.Inputs) :
  R.v28417 (state s) (inputs i) = Zmod.unsigned (N.v28417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28417 s i)) at 1.
  unfold R.v28417, N.v28417.
  rewrite ?node_11103.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28418 (s : N.State) (i : N.Inputs) :
  R.v28418 (state s) (inputs i) = Zmod.unsigned (N.v28418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28418 s i)) at 1.
  unfold R.v28418, N.v28418.
  unfold R.v6, N.v6.
  rewrite ?node_11261.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28419 (s : N.State) (i : N.Inputs) :
  R.v28419 (state s) (inputs i) = Zmod.unsigned (N.v28419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28419 s i)) at 1.
  unfold R.v28419, N.v28419.
  unfold R.v6, N.v6.
  rewrite ?node_11320.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28420 (s : N.State) (i : N.Inputs) :
  R.v28420 (state s) (inputs i) = Zmod.unsigned (N.v28420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28420 s i)) at 1.
  unfold R.v28420, N.v28420.
  rewrite ?node_28417.
  rewrite ?node_28418.
  rewrite ?node_28419.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28421 (s : N.State) (i : N.Inputs) :
  R.v28421 (state s) (inputs i) = Zmod.unsigned (N.v28421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28421 s i)) at 1.
  unfold R.v28421, N.v28421.
  rewrite ?node_28416.
  rewrite ?node_28420.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28422 (s : N.State) (i : N.Inputs) :
  R.v28422 (state s) (inputs i) = Zmod.unsigned (N.v28422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28422 s i)) at 1.
  unfold R.v28422, N.v28422.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28423 (s : N.State) (i : N.Inputs) :
  R.v28423 (state s) (inputs i) = Zmod.unsigned (N.v28423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28423 s i)) at 1.
  unfold R.v28423, N.v28423.
  unfold R.v16463, N.v16463.
  rewrite !state_r1296_nr_5F1297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1296_nr_5F1297 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28424 (s : N.State) (i : N.Inputs) :
  R.v28424 (state s) (inputs i) = Zmod.unsigned (N.v28424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28424 s i)) at 1.
  unfold R.v28424, N.v28424.
  unfold R.v6, N.v6.
  rewrite !state_r1295_nr_5F1296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1295_nr_5F1296 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28425 (s : N.State) (i : N.Inputs) :
  R.v28425 (state s) (inputs i) = Zmod.unsigned (N.v28425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28425 s i)) at 1.
  unfold R.v28425, N.v28425.
  unfold R.v6, N.v6.
  rewrite !state_r1294_nr_5F1295.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1294_nr_5F1295 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28426 (s : N.State) (i : N.Inputs) :
  R.v28426 (state s) (inputs i) = Zmod.unsigned (N.v28426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28426 s i)) at 1.
  unfold R.v28426, N.v28426.
  rewrite ?node_28424.
  rewrite ?node_28425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28427 (s : N.State) (i : N.Inputs) :
  R.v28427 (state s) (inputs i) = Zmod.unsigned (N.v28427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28427 s i)) at 1.
  unfold R.v28427, N.v28427.
  unfold R.v16484, N.v16484.
  rewrite ?node_28426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28428 (s : N.State) (i : N.Inputs) :
  R.v28428 (state s) (inputs i) = Zmod.unsigned (N.v28428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28428 s i)) at 1.
  unfold R.v28428, N.v28428.
  rewrite ?node_28423.
  rewrite ?node_28427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28429 (s : N.State) (i : N.Inputs) :
  R.v28429 (state s) (inputs i) = Zmod.unsigned (N.v28429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28429 s i)) at 1.
  unfold R.v28429, N.v28429.
  unfold R.v6, N.v6.
  rewrite ?node_28428.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28430 (s : N.State) (i : N.Inputs) :
  R.v28430 (state s) (inputs i) = Zmod.unsigned (N.v28430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28430 s i)) at 1.
  unfold R.v28430, N.v28430.
  rewrite ?node_11098.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28431 (s : N.State) (i : N.Inputs) :
  R.v28431 (state s) (inputs i) = Zmod.unsigned (N.v28431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28431 s i)) at 1.
  unfold R.v28431, N.v28431.
  unfold R.v6, N.v6.
  rewrite ?node_11261.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28432 (s : N.State) (i : N.Inputs) :
  R.v28432 (state s) (inputs i) = Zmod.unsigned (N.v28432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28432 s i)) at 1.
  unfold R.v28432, N.v28432.
  rewrite ?node_28430.
  rewrite ?node_28431.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28433 (s : N.State) (i : N.Inputs) :
  R.v28433 (state s) (inputs i) = Zmod.unsigned (N.v28433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28433 s i)) at 1.
  unfold R.v28433, N.v28433.
  rewrite ?node_28429.
  rewrite ?node_28432.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28434 (s : N.State) (i : N.Inputs) :
  R.v28434 (state s) (inputs i) = Zmod.unsigned (N.v28434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28434 s i)) at 1.
  unfold R.v28434, N.v28434.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28435 (s : N.State) (i : N.Inputs) :
  R.v28435 (state s) (inputs i) = Zmod.unsigned (N.v28435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28435 s i)) at 1.
  unfold R.v28435, N.v28435.
  rewrite ?node_11102.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28436 (s : N.State) (i : N.Inputs) :
  R.v28436 (state s) (inputs i) = Zmod.unsigned (N.v28436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28436 s i)) at 1.
  unfold R.v28436, N.v28436.
  unfold R.v6, N.v6.
  rewrite !state_r1297_nr_5F1298.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1297_nr_5F1298 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28437 (s : N.State) (i : N.Inputs) :
  R.v28437 (state s) (inputs i) = Zmod.unsigned (N.v28437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28437 s i)) at 1.
  unfold R.v28437, N.v28437.
  unfold R.v6, N.v6.
  rewrite ?node_11098.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28438 (s : N.State) (i : N.Inputs) :
  R.v28438 (state s) (inputs i) = Zmod.unsigned (N.v28438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28438 s i)) at 1.
  unfold R.v28438, N.v28438.
  rewrite ?node_28436.
  rewrite ?node_28437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28439 (s : N.State) (i : N.Inputs) :
  R.v28439 (state s) (inputs i) = Zmod.unsigned (N.v28439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28439 s i)) at 1.
  unfold R.v28439, N.v28439.
  unfold R.v16484, N.v16484.
  rewrite ?node_28438.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28440 (s : N.State) (i : N.Inputs) :
  R.v28440 (state s) (inputs i) = Zmod.unsigned (N.v28440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28440 s i)) at 1.
  unfold R.v28440, N.v28440.
  rewrite ?node_28435.
  rewrite ?node_28439.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28441 (s : N.State) (i : N.Inputs) :
  R.v28441 (state s) (inputs i) = Zmod.unsigned (N.v28441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28441 s i)) at 1.
  unfold R.v28441, N.v28441.
  unfold R.v6, N.v6.
  rewrite ?node_28440.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28442 (s : N.State) (i : N.Inputs) :
  R.v28442 (state s) (inputs i) = Zmod.unsigned (N.v28442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28442 s i)) at 1.
  unfold R.v28442, N.v28442.
  rewrite ?node_11103.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28443 (s : N.State) (i : N.Inputs) :
  R.v28443 (state s) (inputs i) = Zmod.unsigned (N.v28443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28443 s i)) at 1.
  unfold R.v28443, N.v28443.
  unfold R.v6, N.v6.
  rewrite ?node_11320.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28444 (s : N.State) (i : N.Inputs) :
  R.v28444 (state s) (inputs i) = Zmod.unsigned (N.v28444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28444 s i)) at 1.
  unfold R.v28444, N.v28444.
  rewrite ?node_28442.
  rewrite ?node_28443.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28445 (s : N.State) (i : N.Inputs) :
  R.v28445 (state s) (inputs i) = Zmod.unsigned (N.v28445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28445 s i)) at 1.
  unfold R.v28445, N.v28445.
  rewrite ?node_28441.
  rewrite ?node_28444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28446 (s : N.State) (i : N.Inputs) :
  R.v28446 (state s) (inputs i) = Zmod.unsigned (N.v28446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28446 s i)) at 1.
  unfold R.v28446, N.v28446.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28447 (s : N.State) (i : N.Inputs) :
  R.v28447 (state s) (inputs i) = Zmod.unsigned (N.v28447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28447 s i)) at 1.
  unfold R.v28447, N.v28447.
  rewrite ?node_11110.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28448 (s : N.State) (i : N.Inputs) :
  R.v28448 (state s) (inputs i) = Zmod.unsigned (N.v28448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28448 s i)) at 1.
  unfold R.v28448, N.v28448.
  unfold R.v16463, N.v16463.
  rewrite !state_r1301_nr_5F1302.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1301_nr_5F1302 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28449 (s : N.State) (i : N.Inputs) :
  R.v28449 (state s) (inputs i) = Zmod.unsigned (N.v28449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28449 s i)) at 1.
  unfold R.v28449, N.v28449.
  unfold R.v16463, N.v16463.
  rewrite !state_r1300_nr_5F1301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1300_nr_5F1301 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28450 (s : N.State) (i : N.Inputs) :
  R.v28450 (state s) (inputs i) = Zmod.unsigned (N.v28450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28450 s i)) at 1.
  unfold R.v28450, N.v28450.
  unfold R.v6, N.v6.
  rewrite !state_r1299_nr_5F1300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1299_nr_5F1300 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28451 (s : N.State) (i : N.Inputs) :
  R.v28451 (state s) (inputs i) = Zmod.unsigned (N.v28451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28451 s i)) at 1.
  unfold R.v28451, N.v28451.
  unfold R.v6, N.v6.
  rewrite !state_r1298_nr_5F1299.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1298_nr_5F1299 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28452 (s : N.State) (i : N.Inputs) :
  R.v28452 (state s) (inputs i) = Zmod.unsigned (N.v28452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28452 s i)) at 1.
  unfold R.v28452, N.v28452.
  rewrite ?node_28450.
  rewrite ?node_28451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28453 (s : N.State) (i : N.Inputs) :
  R.v28453 (state s) (inputs i) = Zmod.unsigned (N.v28453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28453 s i)) at 1.
  unfold R.v28453, N.v28453.
  unfold R.v16484, N.v16484.
  rewrite ?node_28452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28454 (s : N.State) (i : N.Inputs) :
  R.v28454 (state s) (inputs i) = Zmod.unsigned (N.v28454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28454 s i)) at 1.
  unfold R.v28454, N.v28454.
  rewrite ?node_28447.
  rewrite ?node_28448.
  rewrite ?node_28449.
  rewrite ?node_28453.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28455 (s : N.State) (i : N.Inputs) :
  R.v28455 (state s) (inputs i) = Zmod.unsigned (N.v28455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28455 s i)) at 1.
  unfold R.v28455, N.v28455.
  unfold R.v6, N.v6.
  rewrite ?node_28454.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28456 (s : N.State) (i : N.Inputs) :
  R.v28456 (state s) (inputs i) = Zmod.unsigned (N.v28456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28456 s i)) at 1.
  unfold R.v28456, N.v28456.
  rewrite ?node_11111.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28457 (s : N.State) (i : N.Inputs) :
  R.v28457 (state s) (inputs i) = Zmod.unsigned (N.v28457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28457 s i)) at 1.
  unfold R.v28457, N.v28457.
  unfold R.v6, N.v6.
  rewrite ?node_11269.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28458 (s : N.State) (i : N.Inputs) :
  R.v28458 (state s) (inputs i) = Zmod.unsigned (N.v28458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28458 s i)) at 1.
  unfold R.v28458, N.v28458.
  unfold R.v6, N.v6.
  rewrite ?node_11329.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28459 (s : N.State) (i : N.Inputs) :
  R.v28459 (state s) (inputs i) = Zmod.unsigned (N.v28459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28459 s i)) at 1.
  unfold R.v28459, N.v28459.
  rewrite ?node_28456.
  rewrite ?node_28457.
  rewrite ?node_28458.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28460 (s : N.State) (i : N.Inputs) :
  R.v28460 (state s) (inputs i) = Zmod.unsigned (N.v28460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28460 s i)) at 1.
  unfold R.v28460, N.v28460.
  rewrite ?node_28455.
  rewrite ?node_28459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28461 (s : N.State) (i : N.Inputs) :
  R.v28461 (state s) (inputs i) = Zmod.unsigned (N.v28461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28461 s i)) at 1.
  unfold R.v28461, N.v28461.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28462 (s : N.State) (i : N.Inputs) :
  R.v28462 (state s) (inputs i) = Zmod.unsigned (N.v28462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28462 s i)) at 1.
  unfold R.v28462, N.v28462.
  unfold R.v16463, N.v16463.
  rewrite !state_r1300_nr_5F1301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1300_nr_5F1301 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28463 (s : N.State) (i : N.Inputs) :
  R.v28463 (state s) (inputs i) = Zmod.unsigned (N.v28463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28463 s i)) at 1.
  unfold R.v28463, N.v28463.
  unfold R.v6, N.v6.
  rewrite !state_r1299_nr_5F1300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1299_nr_5F1300 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28464 (s : N.State) (i : N.Inputs) :
  R.v28464 (state s) (inputs i) = Zmod.unsigned (N.v28464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28464 s i)) at 1.
  unfold R.v28464, N.v28464.
  unfold R.v6, N.v6.
  rewrite !state_r1298_nr_5F1299.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1298_nr_5F1299 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28465 (s : N.State) (i : N.Inputs) :
  R.v28465 (state s) (inputs i) = Zmod.unsigned (N.v28465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28465 s i)) at 1.
  unfold R.v28465, N.v28465.
  rewrite ?node_28463.
  rewrite ?node_28464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28466 (s : N.State) (i : N.Inputs) :
  R.v28466 (state s) (inputs i) = Zmod.unsigned (N.v28466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28466 s i)) at 1.
  unfold R.v28466, N.v28466.
  unfold R.v16484, N.v16484.
  rewrite ?node_28465.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28467 (s : N.State) (i : N.Inputs) :
  R.v28467 (state s) (inputs i) = Zmod.unsigned (N.v28467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28467 s i)) at 1.
  unfold R.v28467, N.v28467.
  rewrite ?node_28462.
  rewrite ?node_28466.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28468 (s : N.State) (i : N.Inputs) :
  R.v28468 (state s) (inputs i) = Zmod.unsigned (N.v28468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28468 s i)) at 1.
  unfold R.v28468, N.v28468.
  unfold R.v6, N.v6.
  rewrite ?node_28467.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28469 (s : N.State) (i : N.Inputs) :
  R.v28469 (state s) (inputs i) = Zmod.unsigned (N.v28469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28469 s i)) at 1.
  unfold R.v28469, N.v28469.
  rewrite ?node_11106.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28470 (s : N.State) (i : N.Inputs) :
  R.v28470 (state s) (inputs i) = Zmod.unsigned (N.v28470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28470 s i)) at 1.
  unfold R.v28470, N.v28470.
  unfold R.v6, N.v6.
  rewrite ?node_11269.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28471 (s : N.State) (i : N.Inputs) :
  R.v28471 (state s) (inputs i) = Zmod.unsigned (N.v28471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28471 s i)) at 1.
  unfold R.v28471, N.v28471.
  rewrite ?node_28469.
  rewrite ?node_28470.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28472 (s : N.State) (i : N.Inputs) :
  R.v28472 (state s) (inputs i) = Zmod.unsigned (N.v28472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28472 s i)) at 1.
  unfold R.v28472, N.v28472.
  rewrite ?node_28468.
  rewrite ?node_28471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28473 (s : N.State) (i : N.Inputs) :
  R.v28473 (state s) (inputs i) = Zmod.unsigned (N.v28473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28473 s i)) at 1.
  unfold R.v28473, N.v28473.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28474 (s : N.State) (i : N.Inputs) :
  R.v28474 (state s) (inputs i) = Zmod.unsigned (N.v28474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28474 s i)) at 1.
  unfold R.v28474, N.v28474.
  rewrite ?node_11110.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28475 (s : N.State) (i : N.Inputs) :
  R.v28475 (state s) (inputs i) = Zmod.unsigned (N.v28475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28475 s i)) at 1.
  unfold R.v28475, N.v28475.
  unfold R.v6, N.v6.
  rewrite !state_r1301_nr_5F1302.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1301_nr_5F1302 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28476 (s : N.State) (i : N.Inputs) :
  R.v28476 (state s) (inputs i) = Zmod.unsigned (N.v28476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28476 s i)) at 1.
  unfold R.v28476, N.v28476.
  unfold R.v6, N.v6.
  rewrite ?node_11106.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28477 (s : N.State) (i : N.Inputs) :
  R.v28477 (state s) (inputs i) = Zmod.unsigned (N.v28477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28477 s i)) at 1.
  unfold R.v28477, N.v28477.
  rewrite ?node_28475.
  rewrite ?node_28476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28478 (s : N.State) (i : N.Inputs) :
  R.v28478 (state s) (inputs i) = Zmod.unsigned (N.v28478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28478 s i)) at 1.
  unfold R.v28478, N.v28478.
  unfold R.v16484, N.v16484.
  rewrite ?node_28477.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28479 (s : N.State) (i : N.Inputs) :
  R.v28479 (state s) (inputs i) = Zmod.unsigned (N.v28479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28479 s i)) at 1.
  unfold R.v28479, N.v28479.
  rewrite ?node_28474.
  rewrite ?node_28478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28480 (s : N.State) (i : N.Inputs) :
  R.v28480 (state s) (inputs i) = Zmod.unsigned (N.v28480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28480 s i)) at 1.
  unfold R.v28480, N.v28480.
  unfold R.v6, N.v6.
  rewrite ?node_28479.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28481 (s : N.State) (i : N.Inputs) :
  R.v28481 (state s) (inputs i) = Zmod.unsigned (N.v28481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28481 s i)) at 1.
  unfold R.v28481, N.v28481.
  rewrite ?node_11111.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28482 (s : N.State) (i : N.Inputs) :
  R.v28482 (state s) (inputs i) = Zmod.unsigned (N.v28482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28482 s i)) at 1.
  unfold R.v28482, N.v28482.
  unfold R.v6, N.v6.
  rewrite ?node_11329.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28483 (s : N.State) (i : N.Inputs) :
  R.v28483 (state s) (inputs i) = Zmod.unsigned (N.v28483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28483 s i)) at 1.
  unfold R.v28483, N.v28483.
  rewrite ?node_28481.
  rewrite ?node_28482.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28484 (s : N.State) (i : N.Inputs) :
  R.v28484 (state s) (inputs i) = Zmod.unsigned (N.v28484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28484 s i)) at 1.
  unfold R.v28484, N.v28484.
  rewrite ?node_28480.
  rewrite ?node_28483.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28485 (s : N.State) (i : N.Inputs) :
  R.v28485 (state s) (inputs i) = Zmod.unsigned (N.v28485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28485 s i)) at 1.
  unfold R.v28485, N.v28485.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28486 (s : N.State) (i : N.Inputs) :
  R.v28486 (state s) (inputs i) = Zmod.unsigned (N.v28486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28486 s i)) at 1.
  unfold R.v28486, N.v28486.
  rewrite ?node_11122.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28487 (s : N.State) (i : N.Inputs) :
  R.v28487 (state s) (inputs i) = Zmod.unsigned (N.v28487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28487 s i)) at 1.
  unfold R.v28487, N.v28487.
  unfold R.v16463, N.v16463.
  rewrite !state_r1305_nr_5F1306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1305_nr_5F1306 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28488 (s : N.State) (i : N.Inputs) :
  R.v28488 (state s) (inputs i) = Zmod.unsigned (N.v28488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28488 s i)) at 1.
  unfold R.v28488, N.v28488.
  unfold R.v16463, N.v16463.
  rewrite !state_r1304_nr_5F1305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1304_nr_5F1305 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28489 (s : N.State) (i : N.Inputs) :
  R.v28489 (state s) (inputs i) = Zmod.unsigned (N.v28489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28489 s i)) at 1.
  unfold R.v28489, N.v28489.
  unfold R.v6, N.v6.
  rewrite !state_r1303_nr_5F1304.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1303_nr_5F1304 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28490 (s : N.State) (i : N.Inputs) :
  R.v28490 (state s) (inputs i) = Zmod.unsigned (N.v28490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28490 s i)) at 1.
  unfold R.v28490, N.v28490.
  unfold R.v6, N.v6.
  rewrite !state_r1302_nr_5F1303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1302_nr_5F1303 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28491 (s : N.State) (i : N.Inputs) :
  R.v28491 (state s) (inputs i) = Zmod.unsigned (N.v28491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28491 s i)) at 1.
  unfold R.v28491, N.v28491.
  rewrite ?node_28489.
  rewrite ?node_28490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28492 (s : N.State) (i : N.Inputs) :
  R.v28492 (state s) (inputs i) = Zmod.unsigned (N.v28492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28492 s i)) at 1.
  unfold R.v28492, N.v28492.
  unfold R.v16484, N.v16484.
  rewrite ?node_28491.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28493 (s : N.State) (i : N.Inputs) :
  R.v28493 (state s) (inputs i) = Zmod.unsigned (N.v28493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28493 s i)) at 1.
  unfold R.v28493, N.v28493.
  rewrite ?node_28486.
  rewrite ?node_28487.
  rewrite ?node_28488.
  rewrite ?node_28492.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28494 (s : N.State) (i : N.Inputs) :
  R.v28494 (state s) (inputs i) = Zmod.unsigned (N.v28494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28494 s i)) at 1.
  unfold R.v28494, N.v28494.
  unfold R.v6, N.v6.
  rewrite ?node_28493.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28495 (s : N.State) (i : N.Inputs) :
  R.v28495 (state s) (inputs i) = Zmod.unsigned (N.v28495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28495 s i)) at 1.
  unfold R.v28495, N.v28495.
  rewrite ?node_11123.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28496 (s : N.State) (i : N.Inputs) :
  R.v28496 (state s) (inputs i) = Zmod.unsigned (N.v28496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28496 s i)) at 1.
  unfold R.v28496, N.v28496.
  unfold R.v6, N.v6.
  rewrite ?node_11281.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28497 (s : N.State) (i : N.Inputs) :
  R.v28497 (state s) (inputs i) = Zmod.unsigned (N.v28497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28497 s i)) at 1.
  unfold R.v28497, N.v28497.
  unfold R.v6, N.v6.
  rewrite ?node_11332.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28498 (s : N.State) (i : N.Inputs) :
  R.v28498 (state s) (inputs i) = Zmod.unsigned (N.v28498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28498 s i)) at 1.
  unfold R.v28498, N.v28498.
  rewrite ?node_28495.
  rewrite ?node_28496.
  rewrite ?node_28497.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28499 (s : N.State) (i : N.Inputs) :
  R.v28499 (state s) (inputs i) = Zmod.unsigned (N.v28499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28499 s i)) at 1.
  unfold R.v28499, N.v28499.
  rewrite ?node_28494.
  rewrite ?node_28498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28500 (s : N.State) (i : N.Inputs) :
  R.v28500 (state s) (inputs i) = Zmod.unsigned (N.v28500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28500 s i)) at 1.
  unfold R.v28500, N.v28500.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28501 (s : N.State) (i : N.Inputs) :
  R.v28501 (state s) (inputs i) = Zmod.unsigned (N.v28501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28501 s i)) at 1.
  unfold R.v28501, N.v28501.
  unfold R.v16463, N.v16463.
  rewrite !state_r1304_nr_5F1305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1304_nr_5F1305 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28502 (s : N.State) (i : N.Inputs) :
  R.v28502 (state s) (inputs i) = Zmod.unsigned (N.v28502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28502 s i)) at 1.
  unfold R.v28502, N.v28502.
  unfold R.v6, N.v6.
  rewrite !state_r1303_nr_5F1304.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1303_nr_5F1304 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28503 (s : N.State) (i : N.Inputs) :
  R.v28503 (state s) (inputs i) = Zmod.unsigned (N.v28503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28503 s i)) at 1.
  unfold R.v28503, N.v28503.
  unfold R.v6, N.v6.
  rewrite !state_r1302_nr_5F1303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1302_nr_5F1303 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28504 (s : N.State) (i : N.Inputs) :
  R.v28504 (state s) (inputs i) = Zmod.unsigned (N.v28504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28504 s i)) at 1.
  unfold R.v28504, N.v28504.
  rewrite ?node_28502.
  rewrite ?node_28503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28505 (s : N.State) (i : N.Inputs) :
  R.v28505 (state s) (inputs i) = Zmod.unsigned (N.v28505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28505 s i)) at 1.
  unfold R.v28505, N.v28505.
  unfold R.v16484, N.v16484.
  rewrite ?node_28504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28506 (s : N.State) (i : N.Inputs) :
  R.v28506 (state s) (inputs i) = Zmod.unsigned (N.v28506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28506 s i)) at 1.
  unfold R.v28506, N.v28506.
  rewrite ?node_28501.
  rewrite ?node_28505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28507 (s : N.State) (i : N.Inputs) :
  R.v28507 (state s) (inputs i) = Zmod.unsigned (N.v28507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28507 s i)) at 1.
  unfold R.v28507, N.v28507.
  unfold R.v6, N.v6.
  rewrite ?node_28506.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28508 (s : N.State) (i : N.Inputs) :
  R.v28508 (state s) (inputs i) = Zmod.unsigned (N.v28508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28508 s i)) at 1.
  unfold R.v28508, N.v28508.
  rewrite ?node_11118.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28509 (s : N.State) (i : N.Inputs) :
  R.v28509 (state s) (inputs i) = Zmod.unsigned (N.v28509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28509 s i)) at 1.
  unfold R.v28509, N.v28509.
  unfold R.v6, N.v6.
  rewrite ?node_11281.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28510 (s : N.State) (i : N.Inputs) :
  R.v28510 (state s) (inputs i) = Zmod.unsigned (N.v28510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28510 s i)) at 1.
  unfold R.v28510, N.v28510.
  rewrite ?node_28508.
  rewrite ?node_28509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28511 (s : N.State) (i : N.Inputs) :
  R.v28511 (state s) (inputs i) = Zmod.unsigned (N.v28511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28511 s i)) at 1.
  unfold R.v28511, N.v28511.
  rewrite ?node_28507.
  rewrite ?node_28510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28512 (s : N.State) (i : N.Inputs) :
  R.v28512 (state s) (inputs i) = Zmod.unsigned (N.v28512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28512 s i)) at 1.
  unfold R.v28512, N.v28512.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28513 (s : N.State) (i : N.Inputs) :
  R.v28513 (state s) (inputs i) = Zmod.unsigned (N.v28513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28513 s i)) at 1.
  unfold R.v28513, N.v28513.
  rewrite ?node_11122.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28514 (s : N.State) (i : N.Inputs) :
  R.v28514 (state s) (inputs i) = Zmod.unsigned (N.v28514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28514 s i)) at 1.
  unfold R.v28514, N.v28514.
  unfold R.v6, N.v6.
  rewrite !state_r1305_nr_5F1306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1305_nr_5F1306 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28515 (s : N.State) (i : N.Inputs) :
  R.v28515 (state s) (inputs i) = Zmod.unsigned (N.v28515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28515 s i)) at 1.
  unfold R.v28515, N.v28515.
  unfold R.v6, N.v6.
  rewrite ?node_11118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28516 (s : N.State) (i : N.Inputs) :
  R.v28516 (state s) (inputs i) = Zmod.unsigned (N.v28516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28516 s i)) at 1.
  unfold R.v28516, N.v28516.
  rewrite ?node_28514.
  rewrite ?node_28515.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28517 (s : N.State) (i : N.Inputs) :
  R.v28517 (state s) (inputs i) = Zmod.unsigned (N.v28517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28517 s i)) at 1.
  unfold R.v28517, N.v28517.
  unfold R.v16484, N.v16484.
  rewrite ?node_28516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28518 (s : N.State) (i : N.Inputs) :
  R.v28518 (state s) (inputs i) = Zmod.unsigned (N.v28518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28518 s i)) at 1.
  unfold R.v28518, N.v28518.
  rewrite ?node_28513.
  rewrite ?node_28517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28519 (s : N.State) (i : N.Inputs) :
  R.v28519 (state s) (inputs i) = Zmod.unsigned (N.v28519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28519 s i)) at 1.
  unfold R.v28519, N.v28519.
  unfold R.v6, N.v6.
  rewrite ?node_28518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28520 (s : N.State) (i : N.Inputs) :
  R.v28520 (state s) (inputs i) = Zmod.unsigned (N.v28520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28520 s i)) at 1.
  unfold R.v28520, N.v28520.
  rewrite ?node_11123.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28521 (s : N.State) (i : N.Inputs) :
  R.v28521 (state s) (inputs i) = Zmod.unsigned (N.v28521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28521 s i)) at 1.
  unfold R.v28521, N.v28521.
  unfold R.v6, N.v6.
  rewrite ?node_11332.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28522 (s : N.State) (i : N.Inputs) :
  R.v28522 (state s) (inputs i) = Zmod.unsigned (N.v28522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28522 s i)) at 1.
  unfold R.v28522, N.v28522.
  rewrite ?node_28520.
  rewrite ?node_28521.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28523 (s : N.State) (i : N.Inputs) :
  R.v28523 (state s) (inputs i) = Zmod.unsigned (N.v28523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28523 s i)) at 1.
  unfold R.v28523, N.v28523.
  rewrite ?node_28519.
  rewrite ?node_28522.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28524 (s : N.State) (i : N.Inputs) :
  R.v28524 (state s) (inputs i) = Zmod.unsigned (N.v28524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28524 s i)) at 1.
  unfold R.v28524, N.v28524.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28525 (s : N.State) (i : N.Inputs) :
  R.v28525 (state s) (inputs i) = Zmod.unsigned (N.v28525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28525 s i)) at 1.
  unfold R.v28525, N.v28525.
  rewrite ?node_11129.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28526 (s : N.State) (i : N.Inputs) :
  R.v28526 (state s) (inputs i) = Zmod.unsigned (N.v28526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28526 s i)) at 1.
  unfold R.v28526, N.v28526.
  unfold R.v16463, N.v16463.
  rewrite !state_r1309_nr_5F1310.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1309_nr_5F1310 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28527 (s : N.State) (i : N.Inputs) :
  R.v28527 (state s) (inputs i) = Zmod.unsigned (N.v28527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28527 s i)) at 1.
  unfold R.v28527, N.v28527.
  unfold R.v16463, N.v16463.
  rewrite !state_r1308_nr_5F1309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1308_nr_5F1309 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28528 (s : N.State) (i : N.Inputs) :
  R.v28528 (state s) (inputs i) = Zmod.unsigned (N.v28528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28528 s i)) at 1.
  unfold R.v28528, N.v28528.
  unfold R.v6, N.v6.
  rewrite !state_r1307_nr_5F1308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1307_nr_5F1308 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28529 (s : N.State) (i : N.Inputs) :
  R.v28529 (state s) (inputs i) = Zmod.unsigned (N.v28529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28529 s i)) at 1.
  unfold R.v28529, N.v28529.
  unfold R.v6, N.v6.
  rewrite !state_r1306_nr_5F1307.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1306_nr_5F1307 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28530 (s : N.State) (i : N.Inputs) :
  R.v28530 (state s) (inputs i) = Zmod.unsigned (N.v28530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28530 s i)) at 1.
  unfold R.v28530, N.v28530.
  rewrite ?node_28528.
  rewrite ?node_28529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28531 (s : N.State) (i : N.Inputs) :
  R.v28531 (state s) (inputs i) = Zmod.unsigned (N.v28531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28531 s i)) at 1.
  unfold R.v28531, N.v28531.
  unfold R.v16484, N.v16484.
  rewrite ?node_28530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28532 (s : N.State) (i : N.Inputs) :
  R.v28532 (state s) (inputs i) = Zmod.unsigned (N.v28532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28532 s i)) at 1.
  unfold R.v28532, N.v28532.
  rewrite ?node_28525.
  rewrite ?node_28526.
  rewrite ?node_28527.
  rewrite ?node_28531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28533 (s : N.State) (i : N.Inputs) :
  R.v28533 (state s) (inputs i) = Zmod.unsigned (N.v28533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28533 s i)) at 1.
  unfold R.v28533, N.v28533.
  unfold R.v6, N.v6.
  rewrite ?node_28532.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28534 (s : N.State) (i : N.Inputs) :
  R.v28534 (state s) (inputs i) = Zmod.unsigned (N.v28534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28534 s i)) at 1.
  unfold R.v28534, N.v28534.
  rewrite ?node_11130.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28535 (s : N.State) (i : N.Inputs) :
  R.v28535 (state s) (inputs i) = Zmod.unsigned (N.v28535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28535 s i)) at 1.
  unfold R.v28535, N.v28535.
  unfold R.v6, N.v6.
  rewrite ?node_11288.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28536 (s : N.State) (i : N.Inputs) :
  R.v28536 (state s) (inputs i) = Zmod.unsigned (N.v28536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28536 s i)) at 1.
  unfold R.v28536, N.v28536.
  unfold R.v6, N.v6.
  rewrite ?node_11336.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28537 (s : N.State) (i : N.Inputs) :
  R.v28537 (state s) (inputs i) = Zmod.unsigned (N.v28537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28537 s i)) at 1.
  unfold R.v28537, N.v28537.
  rewrite ?node_28534.
  rewrite ?node_28535.
  rewrite ?node_28536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28538 (s : N.State) (i : N.Inputs) :
  R.v28538 (state s) (inputs i) = Zmod.unsigned (N.v28538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28538 s i)) at 1.
  unfold R.v28538, N.v28538.
  rewrite ?node_28533.
  rewrite ?node_28537.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28539 (s : N.State) (i : N.Inputs) :
  R.v28539 (state s) (inputs i) = Zmod.unsigned (N.v28539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28539 s i)) at 1.
  unfold R.v28539, N.v28539.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28540 (s : N.State) (i : N.Inputs) :
  R.v28540 (state s) (inputs i) = Zmod.unsigned (N.v28540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28540 s i)) at 1.
  unfold R.v28540, N.v28540.
  unfold R.v16463, N.v16463.
  rewrite !state_r1308_nr_5F1309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1308_nr_5F1309 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28541 (s : N.State) (i : N.Inputs) :
  R.v28541 (state s) (inputs i) = Zmod.unsigned (N.v28541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28541 s i)) at 1.
  unfold R.v28541, N.v28541.
  unfold R.v6, N.v6.
  rewrite !state_r1307_nr_5F1308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1307_nr_5F1308 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28542 (s : N.State) (i : N.Inputs) :
  R.v28542 (state s) (inputs i) = Zmod.unsigned (N.v28542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28542 s i)) at 1.
  unfold R.v28542, N.v28542.
  unfold R.v6, N.v6.
  rewrite !state_r1306_nr_5F1307.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1306_nr_5F1307 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28543 (s : N.State) (i : N.Inputs) :
  R.v28543 (state s) (inputs i) = Zmod.unsigned (N.v28543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28543 s i)) at 1.
  unfold R.v28543, N.v28543.
  rewrite ?node_28541.
  rewrite ?node_28542.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28544 (s : N.State) (i : N.Inputs) :
  R.v28544 (state s) (inputs i) = Zmod.unsigned (N.v28544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28544 s i)) at 1.
  unfold R.v28544, N.v28544.
  unfold R.v16484, N.v16484.
  rewrite ?node_28543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28545 (s : N.State) (i : N.Inputs) :
  R.v28545 (state s) (inputs i) = Zmod.unsigned (N.v28545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28545 s i)) at 1.
  unfold R.v28545, N.v28545.
  rewrite ?node_28540.
  rewrite ?node_28544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28546 (s : N.State) (i : N.Inputs) :
  R.v28546 (state s) (inputs i) = Zmod.unsigned (N.v28546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28546 s i)) at 1.
  unfold R.v28546, N.v28546.
  unfold R.v6, N.v6.
  rewrite ?node_28545.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28547 (s : N.State) (i : N.Inputs) :
  R.v28547 (state s) (inputs i) = Zmod.unsigned (N.v28547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28547 s i)) at 1.
  unfold R.v28547, N.v28547.
  rewrite ?node_11125.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28548 (s : N.State) (i : N.Inputs) :
  R.v28548 (state s) (inputs i) = Zmod.unsigned (N.v28548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28548 s i)) at 1.
  unfold R.v28548, N.v28548.
  unfold R.v6, N.v6.
  rewrite ?node_11288.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28549 (s : N.State) (i : N.Inputs) :
  R.v28549 (state s) (inputs i) = Zmod.unsigned (N.v28549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28549 s i)) at 1.
  unfold R.v28549, N.v28549.
  rewrite ?node_28547.
  rewrite ?node_28548.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28550 (s : N.State) (i : N.Inputs) :
  R.v28550 (state s) (inputs i) = Zmod.unsigned (N.v28550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28550 s i)) at 1.
  unfold R.v28550, N.v28550.
  rewrite ?node_28546.
  rewrite ?node_28549.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28551 (s : N.State) (i : N.Inputs) :
  R.v28551 (state s) (inputs i) = Zmod.unsigned (N.v28551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28551 s i)) at 1.
  unfold R.v28551, N.v28551.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28552 (s : N.State) (i : N.Inputs) :
  R.v28552 (state s) (inputs i) = Zmod.unsigned (N.v28552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28552 s i)) at 1.
  unfold R.v28552, N.v28552.
  rewrite ?node_11129.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28553 (s : N.State) (i : N.Inputs) :
  R.v28553 (state s) (inputs i) = Zmod.unsigned (N.v28553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28553 s i)) at 1.
  unfold R.v28553, N.v28553.
  unfold R.v6, N.v6.
  rewrite !state_r1309_nr_5F1310.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1309_nr_5F1310 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28554 (s : N.State) (i : N.Inputs) :
  R.v28554 (state s) (inputs i) = Zmod.unsigned (N.v28554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28554 s i)) at 1.
  unfold R.v28554, N.v28554.
  unfold R.v6, N.v6.
  rewrite ?node_11125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28555 (s : N.State) (i : N.Inputs) :
  R.v28555 (state s) (inputs i) = Zmod.unsigned (N.v28555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28555 s i)) at 1.
  unfold R.v28555, N.v28555.
  rewrite ?node_28553.
  rewrite ?node_28554.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28556 (s : N.State) (i : N.Inputs) :
  R.v28556 (state s) (inputs i) = Zmod.unsigned (N.v28556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28556 s i)) at 1.
  unfold R.v28556, N.v28556.
  unfold R.v16484, N.v16484.
  rewrite ?node_28555.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28557 (s : N.State) (i : N.Inputs) :
  R.v28557 (state s) (inputs i) = Zmod.unsigned (N.v28557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28557 s i)) at 1.
  unfold R.v28557, N.v28557.
  rewrite ?node_28552.
  rewrite ?node_28556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28558 (s : N.State) (i : N.Inputs) :
  R.v28558 (state s) (inputs i) = Zmod.unsigned (N.v28558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28558 s i)) at 1.
  unfold R.v28558, N.v28558.
  unfold R.v6, N.v6.
  rewrite ?node_28557.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28559 (s : N.State) (i : N.Inputs) :
  R.v28559 (state s) (inputs i) = Zmod.unsigned (N.v28559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28559 s i)) at 1.
  unfold R.v28559, N.v28559.
  rewrite ?node_11130.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28560 (s : N.State) (i : N.Inputs) :
  R.v28560 (state s) (inputs i) = Zmod.unsigned (N.v28560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28560 s i)) at 1.
  unfold R.v28560, N.v28560.
  unfold R.v6, N.v6.
  rewrite ?node_11336.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28561 (s : N.State) (i : N.Inputs) :
  R.v28561 (state s) (inputs i) = Zmod.unsigned (N.v28561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28561 s i)) at 1.
  unfold R.v28561, N.v28561.
  rewrite ?node_28559.
  rewrite ?node_28560.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28562 (s : N.State) (i : N.Inputs) :
  R.v28562 (state s) (inputs i) = Zmod.unsigned (N.v28562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28562 s i)) at 1.
  unfold R.v28562, N.v28562.
  rewrite ?node_28558.
  rewrite ?node_28561.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28563 (s : N.State) (i : N.Inputs) :
  R.v28563 (state s) (inputs i) = Zmod.unsigned (N.v28563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28563 s i)) at 1.
  unfold R.v28563, N.v28563.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28564 (s : N.State) (i : N.Inputs) :
  R.v28564 (state s) (inputs i) = Zmod.unsigned (N.v28564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28564 s i)) at 1.
  unfold R.v28564, N.v28564.
  rewrite ?node_11137.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28565 (s : N.State) (i : N.Inputs) :
  R.v28565 (state s) (inputs i) = Zmod.unsigned (N.v28565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28565 s i)) at 1.
  unfold R.v28565, N.v28565.
  unfold R.v16463, N.v16463.
  rewrite !state_r1313_nr_5F1314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1313_nr_5F1314 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28566 (s : N.State) (i : N.Inputs) :
  R.v28566 (state s) (inputs i) = Zmod.unsigned (N.v28566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28566 s i)) at 1.
  unfold R.v28566, N.v28566.
  unfold R.v16463, N.v16463.
  rewrite !state_r1312_nr_5F1313.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1312_nr_5F1313 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28567 (s : N.State) (i : N.Inputs) :
  R.v28567 (state s) (inputs i) = Zmod.unsigned (N.v28567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28567 s i)) at 1.
  unfold R.v28567, N.v28567.
  unfold R.v6, N.v6.
  rewrite !state_r1311_nr_5F1312.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1311_nr_5F1312 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28568 (s : N.State) (i : N.Inputs) :
  R.v28568 (state s) (inputs i) = Zmod.unsigned (N.v28568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28568 s i)) at 1.
  unfold R.v28568, N.v28568.
  unfold R.v6, N.v6.
  rewrite !state_r1310_nr_5F1311.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1310_nr_5F1311 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28569 (s : N.State) (i : N.Inputs) :
  R.v28569 (state s) (inputs i) = Zmod.unsigned (N.v28569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28569 s i)) at 1.
  unfold R.v28569, N.v28569.
  rewrite ?node_28567.
  rewrite ?node_28568.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28570 (s : N.State) (i : N.Inputs) :
  R.v28570 (state s) (inputs i) = Zmod.unsigned (N.v28570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28570 s i)) at 1.
  unfold R.v28570, N.v28570.
  unfold R.v16484, N.v16484.
  rewrite ?node_28569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28571 (s : N.State) (i : N.Inputs) :
  R.v28571 (state s) (inputs i) = Zmod.unsigned (N.v28571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28571 s i)) at 1.
  unfold R.v28571, N.v28571.
  rewrite ?node_28564.
  rewrite ?node_28565.
  rewrite ?node_28566.
  rewrite ?node_28570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28572 (s : N.State) (i : N.Inputs) :
  R.v28572 (state s) (inputs i) = Zmod.unsigned (N.v28572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28572 s i)) at 1.
  unfold R.v28572, N.v28572.
  unfold R.v6, N.v6.
  rewrite ?node_28571.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28573 (s : N.State) (i : N.Inputs) :
  R.v28573 (state s) (inputs i) = Zmod.unsigned (N.v28573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28573 s i)) at 1.
  unfold R.v28573, N.v28573.
  rewrite ?node_11138.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28574 (s : N.State) (i : N.Inputs) :
  R.v28574 (state s) (inputs i) = Zmod.unsigned (N.v28574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28574 s i)) at 1.
  unfold R.v28574, N.v28574.
  unfold R.v6, N.v6.
  rewrite ?node_11296.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28575 (s : N.State) (i : N.Inputs) :
  R.v28575 (state s) (inputs i) = Zmod.unsigned (N.v28575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28575 s i)) at 1.
  unfold R.v28575, N.v28575.
  unfold R.v6, N.v6.
  rewrite ?node_11340.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28576 (s : N.State) (i : N.Inputs) :
  R.v28576 (state s) (inputs i) = Zmod.unsigned (N.v28576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28576 s i)) at 1.
  unfold R.v28576, N.v28576.
  rewrite ?node_28573.
  rewrite ?node_28574.
  rewrite ?node_28575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28577 (s : N.State) (i : N.Inputs) :
  R.v28577 (state s) (inputs i) = Zmod.unsigned (N.v28577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28577 s i)) at 1.
  unfold R.v28577, N.v28577.
  rewrite ?node_28572.
  rewrite ?node_28576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28578 (s : N.State) (i : N.Inputs) :
  R.v28578 (state s) (inputs i) = Zmod.unsigned (N.v28578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28578 s i)) at 1.
  unfold R.v28578, N.v28578.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28579 (s : N.State) (i : N.Inputs) :
  R.v28579 (state s) (inputs i) = Zmod.unsigned (N.v28579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28579 s i)) at 1.
  unfold R.v28579, N.v28579.
  unfold R.v16463, N.v16463.
  rewrite !state_r1312_nr_5F1313.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1312_nr_5F1313 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28580 (s : N.State) (i : N.Inputs) :
  R.v28580 (state s) (inputs i) = Zmod.unsigned (N.v28580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28580 s i)) at 1.
  unfold R.v28580, N.v28580.
  unfold R.v6, N.v6.
  rewrite !state_r1311_nr_5F1312.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1311_nr_5F1312 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28581 (s : N.State) (i : N.Inputs) :
  R.v28581 (state s) (inputs i) = Zmod.unsigned (N.v28581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28581 s i)) at 1.
  unfold R.v28581, N.v28581.
  unfold R.v6, N.v6.
  rewrite !state_r1310_nr_5F1311.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1310_nr_5F1311 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28582 (s : N.State) (i : N.Inputs) :
  R.v28582 (state s) (inputs i) = Zmod.unsigned (N.v28582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28582 s i)) at 1.
  unfold R.v28582, N.v28582.
  rewrite ?node_28580.
  rewrite ?node_28581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28583 (s : N.State) (i : N.Inputs) :
  R.v28583 (state s) (inputs i) = Zmod.unsigned (N.v28583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28583 s i)) at 1.
  unfold R.v28583, N.v28583.
  unfold R.v16484, N.v16484.
  rewrite ?node_28582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28584 (s : N.State) (i : N.Inputs) :
  R.v28584 (state s) (inputs i) = Zmod.unsigned (N.v28584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28584 s i)) at 1.
  unfold R.v28584, N.v28584.
  rewrite ?node_28579.
  rewrite ?node_28583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28585 (s : N.State) (i : N.Inputs) :
  R.v28585 (state s) (inputs i) = Zmod.unsigned (N.v28585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28585 s i)) at 1.
  unfold R.v28585, N.v28585.
  unfold R.v6, N.v6.
  rewrite ?node_28584.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28586 (s : N.State) (i : N.Inputs) :
  R.v28586 (state s) (inputs i) = Zmod.unsigned (N.v28586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28586 s i)) at 1.
  unfold R.v28586, N.v28586.
  rewrite ?node_11133.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28587 (s : N.State) (i : N.Inputs) :
  R.v28587 (state s) (inputs i) = Zmod.unsigned (N.v28587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28587 s i)) at 1.
  unfold R.v28587, N.v28587.
  unfold R.v6, N.v6.
  rewrite ?node_11296.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28588 (s : N.State) (i : N.Inputs) :
  R.v28588 (state s) (inputs i) = Zmod.unsigned (N.v28588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28588 s i)) at 1.
  unfold R.v28588, N.v28588.
  rewrite ?node_28586.
  rewrite ?node_28587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28589 (s : N.State) (i : N.Inputs) :
  R.v28589 (state s) (inputs i) = Zmod.unsigned (N.v28589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28589 s i)) at 1.
  unfold R.v28589, N.v28589.
  rewrite ?node_28585.
  rewrite ?node_28588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28590 (s : N.State) (i : N.Inputs) :
  R.v28590 (state s) (inputs i) = Zmod.unsigned (N.v28590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28590 s i)) at 1.
  unfold R.v28590, N.v28590.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28591 (s : N.State) (i : N.Inputs) :
  R.v28591 (state s) (inputs i) = Zmod.unsigned (N.v28591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28591 s i)) at 1.
  unfold R.v28591, N.v28591.
  rewrite ?node_11137.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28592 (s : N.State) (i : N.Inputs) :
  R.v28592 (state s) (inputs i) = Zmod.unsigned (N.v28592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28592 s i)) at 1.
  unfold R.v28592, N.v28592.
  unfold R.v6, N.v6.
  rewrite !state_r1313_nr_5F1314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1313_nr_5F1314 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28593 (s : N.State) (i : N.Inputs) :
  R.v28593 (state s) (inputs i) = Zmod.unsigned (N.v28593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28593 s i)) at 1.
  unfold R.v28593, N.v28593.
  unfold R.v6, N.v6.
  rewrite ?node_11133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28594 (s : N.State) (i : N.Inputs) :
  R.v28594 (state s) (inputs i) = Zmod.unsigned (N.v28594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28594 s i)) at 1.
  unfold R.v28594, N.v28594.
  rewrite ?node_28592.
  rewrite ?node_28593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28595 (s : N.State) (i : N.Inputs) :
  R.v28595 (state s) (inputs i) = Zmod.unsigned (N.v28595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28595 s i)) at 1.
  unfold R.v28595, N.v28595.
  unfold R.v16484, N.v16484.
  rewrite ?node_28594.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28596 (s : N.State) (i : N.Inputs) :
  R.v28596 (state s) (inputs i) = Zmod.unsigned (N.v28596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28596 s i)) at 1.
  unfold R.v28596, N.v28596.
  rewrite ?node_28591.
  rewrite ?node_28595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28597 (s : N.State) (i : N.Inputs) :
  R.v28597 (state s) (inputs i) = Zmod.unsigned (N.v28597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28597 s i)) at 1.
  unfold R.v28597, N.v28597.
  unfold R.v6, N.v6.
  rewrite ?node_28596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28598 (s : N.State) (i : N.Inputs) :
  R.v28598 (state s) (inputs i) = Zmod.unsigned (N.v28598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28598 s i)) at 1.
  unfold R.v28598, N.v28598.
  rewrite ?node_11138.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28599 (s : N.State) (i : N.Inputs) :
  R.v28599 (state s) (inputs i) = Zmod.unsigned (N.v28599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28599 s i)) at 1.
  unfold R.v28599, N.v28599.
  unfold R.v6, N.v6.
  rewrite ?node_11340.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28600 (s : N.State) (i : N.Inputs) :
  R.v28600 (state s) (inputs i) = Zmod.unsigned (N.v28600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28600 s i)) at 1.
  unfold R.v28600, N.v28600.
  rewrite ?node_28598.
  rewrite ?node_28599.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28601 (s : N.State) (i : N.Inputs) :
  R.v28601 (state s) (inputs i) = Zmod.unsigned (N.v28601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28601 s i)) at 1.
  unfold R.v28601, N.v28601.
  rewrite ?node_28597.
  rewrite ?node_28600.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28602 (s : N.State) (i : N.Inputs) :
  R.v28602 (state s) (inputs i) = Zmod.unsigned (N.v28602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28602 s i)) at 1.
  unfold R.v28602, N.v28602.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28603 (s : N.State) (i : N.Inputs) :
  R.v28603 (state s) (inputs i) = Zmod.unsigned (N.v28603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28603 s i)) at 1.
  unfold R.v28603, N.v28603.
  rewrite ?node_11145.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28604 (s : N.State) (i : N.Inputs) :
  R.v28604 (state s) (inputs i) = Zmod.unsigned (N.v28604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28604 s i)) at 1.
  unfold R.v28604, N.v28604.
  unfold R.v16463, N.v16463.
  rewrite !state_r1317_nr_5F1318.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1317_nr_5F1318 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28605 (s : N.State) (i : N.Inputs) :
  R.v28605 (state s) (inputs i) = Zmod.unsigned (N.v28605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28605 s i)) at 1.
  unfold R.v28605, N.v28605.
  unfold R.v16463, N.v16463.
  rewrite !state_r1316_nr_5F1317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1316_nr_5F1317 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28606 (s : N.State) (i : N.Inputs) :
  R.v28606 (state s) (inputs i) = Zmod.unsigned (N.v28606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28606 s i)) at 1.
  unfold R.v28606, N.v28606.
  unfold R.v6, N.v6.
  rewrite !state_r1315_nr_5F1316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1315_nr_5F1316 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28607 (s : N.State) (i : N.Inputs) :
  R.v28607 (state s) (inputs i) = Zmod.unsigned (N.v28607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28607 s i)) at 1.
  unfold R.v28607, N.v28607.
  unfold R.v6, N.v6.
  rewrite !state_r1314_nr_5F1315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1314_nr_5F1315 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28608 (s : N.State) (i : N.Inputs) :
  R.v28608 (state s) (inputs i) = Zmod.unsigned (N.v28608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28608 s i)) at 1.
  unfold R.v28608, N.v28608.
  rewrite ?node_28606.
  rewrite ?node_28607.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28609 (s : N.State) (i : N.Inputs) :
  R.v28609 (state s) (inputs i) = Zmod.unsigned (N.v28609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28609 s i)) at 1.
  unfold R.v28609, N.v28609.
  unfold R.v16484, N.v16484.
  rewrite ?node_28608.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28610 (s : N.State) (i : N.Inputs) :
  R.v28610 (state s) (inputs i) = Zmod.unsigned (N.v28610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28610 s i)) at 1.
  unfold R.v28610, N.v28610.
  rewrite ?node_28603.
  rewrite ?node_28604.
  rewrite ?node_28605.
  rewrite ?node_28609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28611 (s : N.State) (i : N.Inputs) :
  R.v28611 (state s) (inputs i) = Zmod.unsigned (N.v28611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28611 s i)) at 1.
  unfold R.v28611, N.v28611.
  unfold R.v6, N.v6.
  rewrite ?node_28610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28612 (s : N.State) (i : N.Inputs) :
  R.v28612 (state s) (inputs i) = Zmod.unsigned (N.v28612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28612 s i)) at 1.
  unfold R.v28612, N.v28612.
  rewrite ?node_11146.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28613 (s : N.State) (i : N.Inputs) :
  R.v28613 (state s) (inputs i) = Zmod.unsigned (N.v28613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28613 s i)) at 1.
  unfold R.v28613, N.v28613.
  unfold R.v6, N.v6.
  rewrite ?node_11309.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28614 (s : N.State) (i : N.Inputs) :
  R.v28614 (state s) (inputs i) = Zmod.unsigned (N.v28614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28614 s i)) at 1.
  unfold R.v28614, N.v28614.
  unfold R.v6, N.v6.
  rewrite ?node_11353.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28615 (s : N.State) (i : N.Inputs) :
  R.v28615 (state s) (inputs i) = Zmod.unsigned (N.v28615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28615 s i)) at 1.
  unfold R.v28615, N.v28615.
  rewrite ?node_28612.
  rewrite ?node_28613.
  rewrite ?node_28614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28616 (s : N.State) (i : N.Inputs) :
  R.v28616 (state s) (inputs i) = Zmod.unsigned (N.v28616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28616 s i)) at 1.
  unfold R.v28616, N.v28616.
  rewrite ?node_28611.
  rewrite ?node_28615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28617 (s : N.State) (i : N.Inputs) :
  R.v28617 (state s) (inputs i) = Zmod.unsigned (N.v28617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28617 s i)) at 1.
  unfold R.v28617, N.v28617.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28618 (s : N.State) (i : N.Inputs) :
  R.v28618 (state s) (inputs i) = Zmod.unsigned (N.v28618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28618 s i)) at 1.
  unfold R.v28618, N.v28618.
  unfold R.v16463, N.v16463.
  rewrite !state_r1316_nr_5F1317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1316_nr_5F1317 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28619 (s : N.State) (i : N.Inputs) :
  R.v28619 (state s) (inputs i) = Zmod.unsigned (N.v28619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28619 s i)) at 1.
  unfold R.v28619, N.v28619.
  unfold R.v6, N.v6.
  rewrite !state_r1315_nr_5F1316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1315_nr_5F1316 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28620 (s : N.State) (i : N.Inputs) :
  R.v28620 (state s) (inputs i) = Zmod.unsigned (N.v28620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28620 s i)) at 1.
  unfold R.v28620, N.v28620.
  unfold R.v6, N.v6.
  rewrite !state_r1314_nr_5F1315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1314_nr_5F1315 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28621 (s : N.State) (i : N.Inputs) :
  R.v28621 (state s) (inputs i) = Zmod.unsigned (N.v28621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28621 s i)) at 1.
  unfold R.v28621, N.v28621.
  rewrite ?node_28619.
  rewrite ?node_28620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28622 (s : N.State) (i : N.Inputs) :
  R.v28622 (state s) (inputs i) = Zmod.unsigned (N.v28622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28622 s i)) at 1.
  unfold R.v28622, N.v28622.
  unfold R.v16484, N.v16484.
  rewrite ?node_28621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28623 (s : N.State) (i : N.Inputs) :
  R.v28623 (state s) (inputs i) = Zmod.unsigned (N.v28623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28623 s i)) at 1.
  unfold R.v28623, N.v28623.
  rewrite ?node_28618.
  rewrite ?node_28622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28624 (s : N.State) (i : N.Inputs) :
  R.v28624 (state s) (inputs i) = Zmod.unsigned (N.v28624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28624 s i)) at 1.
  unfold R.v28624, N.v28624.
  unfold R.v6, N.v6.
  rewrite ?node_28623.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28625 (s : N.State) (i : N.Inputs) :
  R.v28625 (state s) (inputs i) = Zmod.unsigned (N.v28625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28625 s i)) at 1.
  unfold R.v28625, N.v28625.
  rewrite ?node_11141.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28626 (s : N.State) (i : N.Inputs) :
  R.v28626 (state s) (inputs i) = Zmod.unsigned (N.v28626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28626 s i)) at 1.
  unfold R.v28626, N.v28626.
  unfold R.v6, N.v6.
  rewrite ?node_11309.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28627 (s : N.State) (i : N.Inputs) :
  R.v28627 (state s) (inputs i) = Zmod.unsigned (N.v28627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28627 s i)) at 1.
  unfold R.v28627, N.v28627.
  rewrite ?node_28625.
  rewrite ?node_28626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28628 (s : N.State) (i : N.Inputs) :
  R.v28628 (state s) (inputs i) = Zmod.unsigned (N.v28628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28628 s i)) at 1.
  unfold R.v28628, N.v28628.
  rewrite ?node_28624.
  rewrite ?node_28627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28629 (s : N.State) (i : N.Inputs) :
  R.v28629 (state s) (inputs i) = Zmod.unsigned (N.v28629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28629 s i)) at 1.
  unfold R.v28629, N.v28629.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28630 (s : N.State) (i : N.Inputs) :
  R.v28630 (state s) (inputs i) = Zmod.unsigned (N.v28630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28630 s i)) at 1.
  unfold R.v28630, N.v28630.
  rewrite ?node_11145.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28631 (s : N.State) (i : N.Inputs) :
  R.v28631 (state s) (inputs i) = Zmod.unsigned (N.v28631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28631 s i)) at 1.
  unfold R.v28631, N.v28631.
  unfold R.v6, N.v6.
  rewrite !state_r1317_nr_5F1318.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1317_nr_5F1318 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28632 (s : N.State) (i : N.Inputs) :
  R.v28632 (state s) (inputs i) = Zmod.unsigned (N.v28632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28632 s i)) at 1.
  unfold R.v28632, N.v28632.
  unfold R.v6, N.v6.
  rewrite ?node_11141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28633 (s : N.State) (i : N.Inputs) :
  R.v28633 (state s) (inputs i) = Zmod.unsigned (N.v28633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28633 s i)) at 1.
  unfold R.v28633, N.v28633.
  rewrite ?node_28631.
  rewrite ?node_28632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28634 (s : N.State) (i : N.Inputs) :
  R.v28634 (state s) (inputs i) = Zmod.unsigned (N.v28634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28634 s i)) at 1.
  unfold R.v28634, N.v28634.
  unfold R.v16484, N.v16484.
  rewrite ?node_28633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28635 (s : N.State) (i : N.Inputs) :
  R.v28635 (state s) (inputs i) = Zmod.unsigned (N.v28635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28635 s i)) at 1.
  unfold R.v28635, N.v28635.
  rewrite ?node_28630.
  rewrite ?node_28634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28636 (s : N.State) (i : N.Inputs) :
  R.v28636 (state s) (inputs i) = Zmod.unsigned (N.v28636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28636 s i)) at 1.
  unfold R.v28636, N.v28636.
  unfold R.v6, N.v6.
  rewrite ?node_28635.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28637 (s : N.State) (i : N.Inputs) :
  R.v28637 (state s) (inputs i) = Zmod.unsigned (N.v28637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28637 s i)) at 1.
  unfold R.v28637, N.v28637.
  rewrite ?node_11146.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28638 (s : N.State) (i : N.Inputs) :
  R.v28638 (state s) (inputs i) = Zmod.unsigned (N.v28638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28638 s i)) at 1.
  unfold R.v28638, N.v28638.
  unfold R.v6, N.v6.
  rewrite ?node_11353.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28639 (s : N.State) (i : N.Inputs) :
  R.v28639 (state s) (inputs i) = Zmod.unsigned (N.v28639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28639 s i)) at 1.
  unfold R.v28639, N.v28639.
  rewrite ?node_28637.
  rewrite ?node_28638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28640 (s : N.State) (i : N.Inputs) :
  R.v28640 (state s) (inputs i) = Zmod.unsigned (N.v28640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28640 s i)) at 1.
  unfold R.v28640, N.v28640.
  rewrite ?node_28636.
  rewrite ?node_28639.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28641 (s : N.State) (i : N.Inputs) :
  R.v28641 (state s) (inputs i) = Zmod.unsigned (N.v28641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28641 s i)) at 1.
  unfold R.v28641, N.v28641.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28642 (s : N.State) (i : N.Inputs) :
  R.v28642 (state s) (inputs i) = Zmod.unsigned (N.v28642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28642 s i)) at 1.
  unfold R.v28642, N.v28642.
  rewrite ?node_11246.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28643 (s : N.State) (i : N.Inputs) :
  R.v28643 (state s) (inputs i) = Zmod.unsigned (N.v28643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28643 s i)) at 1.
  unfold R.v28643, N.v28643.
  unfold R.v16463, N.v16463.
  rewrite !state_r1321_nr_5F1322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1321_nr_5F1322 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28644 (s : N.State) (i : N.Inputs) :
  R.v28644 (state s) (inputs i) = Zmod.unsigned (N.v28644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28644 s i)) at 1.
  unfold R.v28644, N.v28644.
  unfold R.v16463, N.v16463.
  rewrite !state_r1320_nr_5F1321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1320_nr_5F1321 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28645 (s : N.State) (i : N.Inputs) :
  R.v28645 (state s) (inputs i) = Zmod.unsigned (N.v28645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28645 s i)) at 1.
  unfold R.v28645, N.v28645.
  unfold R.v6, N.v6.
  rewrite !state_r1319_nr_5F1320.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1319_nr_5F1320 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28646 (s : N.State) (i : N.Inputs) :
  R.v28646 (state s) (inputs i) = Zmod.unsigned (N.v28646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28646 s i)) at 1.
  unfold R.v28646, N.v28646.
  unfold R.v6, N.v6.
  rewrite !state_r1318_nr_5F1319.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1318_nr_5F1319 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28647 (s : N.State) (i : N.Inputs) :
  R.v28647 (state s) (inputs i) = Zmod.unsigned (N.v28647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28647 s i)) at 1.
  unfold R.v28647, N.v28647.
  rewrite ?node_28645.
  rewrite ?node_28646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28648 (s : N.State) (i : N.Inputs) :
  R.v28648 (state s) (inputs i) = Zmod.unsigned (N.v28648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28648 s i)) at 1.
  unfold R.v28648, N.v28648.
  unfold R.v16484, N.v16484.
  rewrite ?node_28647.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28649 (s : N.State) (i : N.Inputs) :
  R.v28649 (state s) (inputs i) = Zmod.unsigned (N.v28649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28649 s i)) at 1.
  unfold R.v28649, N.v28649.
  rewrite ?node_28642.
  rewrite ?node_28643.
  rewrite ?node_28644.
  rewrite ?node_28648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28650 (s : N.State) (i : N.Inputs) :
  R.v28650 (state s) (inputs i) = Zmod.unsigned (N.v28650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28650 s i)) at 1.
  unfold R.v28650, N.v28650.
  unfold R.v6, N.v6.
  rewrite ?node_28649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28651 (s : N.State) (i : N.Inputs) :
  R.v28651 (state s) (inputs i) = Zmod.unsigned (N.v28651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28651 s i)) at 1.
  unfold R.v28651, N.v28651.
  rewrite ?node_11247.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28652 (s : N.State) (i : N.Inputs) :
  R.v28652 (state s) (inputs i) = Zmod.unsigned (N.v28652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28652 s i)) at 1.
  unfold R.v28652, N.v28652.
  unfold R.v6, N.v6.
  rewrite ?node_11401.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28653 (s : N.State) (i : N.Inputs) :
  R.v28653 (state s) (inputs i) = Zmod.unsigned (N.v28653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28653 s i)) at 1.
  unfold R.v28653, N.v28653.
  unfold R.v6, N.v6.
  rewrite ?node_11464.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28654 (s : N.State) (i : N.Inputs) :
  R.v28654 (state s) (inputs i) = Zmod.unsigned (N.v28654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28654 s i)) at 1.
  unfold R.v28654, N.v28654.
  rewrite ?node_28651.
  rewrite ?node_28652.
  rewrite ?node_28653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28655 (s : N.State) (i : N.Inputs) :
  R.v28655 (state s) (inputs i) = Zmod.unsigned (N.v28655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28655 s i)) at 1.
  unfold R.v28655, N.v28655.
  rewrite ?node_28650.
  rewrite ?node_28654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28656 (s : N.State) (i : N.Inputs) :
  R.v28656 (state s) (inputs i) = Zmod.unsigned (N.v28656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28656 s i)) at 1.
  unfold R.v28656, N.v28656.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28657 (s : N.State) (i : N.Inputs) :
  R.v28657 (state s) (inputs i) = Zmod.unsigned (N.v28657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28657 s i)) at 1.
  unfold R.v28657, N.v28657.
  unfold R.v16463, N.v16463.
  rewrite !state_r1320_nr_5F1321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1320_nr_5F1321 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28658 (s : N.State) (i : N.Inputs) :
  R.v28658 (state s) (inputs i) = Zmod.unsigned (N.v28658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28658 s i)) at 1.
  unfold R.v28658, N.v28658.
  unfold R.v6, N.v6.
  rewrite !state_r1319_nr_5F1320.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1319_nr_5F1320 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28659 (s : N.State) (i : N.Inputs) :
  R.v28659 (state s) (inputs i) = Zmod.unsigned (N.v28659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28659 s i)) at 1.
  unfold R.v28659, N.v28659.
  unfold R.v6, N.v6.
  rewrite !state_r1318_nr_5F1319.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1318_nr_5F1319 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28660 (s : N.State) (i : N.Inputs) :
  R.v28660 (state s) (inputs i) = Zmod.unsigned (N.v28660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28660 s i)) at 1.
  unfold R.v28660, N.v28660.
  rewrite ?node_28658.
  rewrite ?node_28659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28661 (s : N.State) (i : N.Inputs) :
  R.v28661 (state s) (inputs i) = Zmod.unsigned (N.v28661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28661 s i)) at 1.
  unfold R.v28661, N.v28661.
  unfold R.v16484, N.v16484.
  rewrite ?node_28660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28662 (s : N.State) (i : N.Inputs) :
  R.v28662 (state s) (inputs i) = Zmod.unsigned (N.v28662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28662 s i)) at 1.
  unfold R.v28662, N.v28662.
  rewrite ?node_28657.
  rewrite ?node_28661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28663 (s : N.State) (i : N.Inputs) :
  R.v28663 (state s) (inputs i) = Zmod.unsigned (N.v28663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28663 s i)) at 1.
  unfold R.v28663, N.v28663.
  unfold R.v6, N.v6.
  rewrite ?node_28662.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28664 (s : N.State) (i : N.Inputs) :
  R.v28664 (state s) (inputs i) = Zmod.unsigned (N.v28664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28664 s i)) at 1.
  unfold R.v28664, N.v28664.
  rewrite ?node_11243.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28665 (s : N.State) (i : N.Inputs) :
  R.v28665 (state s) (inputs i) = Zmod.unsigned (N.v28665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28665 s i)) at 1.
  unfold R.v28665, N.v28665.
  unfold R.v6, N.v6.
  rewrite ?node_11401.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28666 (s : N.State) (i : N.Inputs) :
  R.v28666 (state s) (inputs i) = Zmod.unsigned (N.v28666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28666 s i)) at 1.
  unfold R.v28666, N.v28666.
  rewrite ?node_28664.
  rewrite ?node_28665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28667 (s : N.State) (i : N.Inputs) :
  R.v28667 (state s) (inputs i) = Zmod.unsigned (N.v28667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28667 s i)) at 1.
  unfold R.v28667, N.v28667.
  rewrite ?node_28663.
  rewrite ?node_28666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28668 (s : N.State) (i : N.Inputs) :
  R.v28668 (state s) (inputs i) = Zmod.unsigned (N.v28668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28668 s i)) at 1.
  unfold R.v28668, N.v28668.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28669 (s : N.State) (i : N.Inputs) :
  R.v28669 (state s) (inputs i) = Zmod.unsigned (N.v28669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28669 s i)) at 1.
  unfold R.v28669, N.v28669.
  rewrite ?node_11246.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28670 (s : N.State) (i : N.Inputs) :
  R.v28670 (state s) (inputs i) = Zmod.unsigned (N.v28670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28670 s i)) at 1.
  unfold R.v28670, N.v28670.
  unfold R.v6, N.v6.
  rewrite !state_r1321_nr_5F1322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1321_nr_5F1322 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28671 (s : N.State) (i : N.Inputs) :
  R.v28671 (state s) (inputs i) = Zmod.unsigned (N.v28671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28671 s i)) at 1.
  unfold R.v28671, N.v28671.
  unfold R.v6, N.v6.
  rewrite ?node_11243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28672 (s : N.State) (i : N.Inputs) :
  R.v28672 (state s) (inputs i) = Zmod.unsigned (N.v28672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28672 s i)) at 1.
  unfold R.v28672, N.v28672.
  rewrite ?node_28670.
  rewrite ?node_28671.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28673 (s : N.State) (i : N.Inputs) :
  R.v28673 (state s) (inputs i) = Zmod.unsigned (N.v28673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28673 s i)) at 1.
  unfold R.v28673, N.v28673.
  unfold R.v16484, N.v16484.
  rewrite ?node_28672.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28674 (s : N.State) (i : N.Inputs) :
  R.v28674 (state s) (inputs i) = Zmod.unsigned (N.v28674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28674 s i)) at 1.
  unfold R.v28674, N.v28674.
  rewrite ?node_28669.
  rewrite ?node_28673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28675 (s : N.State) (i : N.Inputs) :
  R.v28675 (state s) (inputs i) = Zmod.unsigned (N.v28675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28675 s i)) at 1.
  unfold R.v28675, N.v28675.
  unfold R.v6, N.v6.
  rewrite ?node_28674.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28676 (s : N.State) (i : N.Inputs) :
  R.v28676 (state s) (inputs i) = Zmod.unsigned (N.v28676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28676 s i)) at 1.
  unfold R.v28676, N.v28676.
  rewrite ?node_11247.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28677 (s : N.State) (i : N.Inputs) :
  R.v28677 (state s) (inputs i) = Zmod.unsigned (N.v28677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28677 s i)) at 1.
  unfold R.v28677, N.v28677.
  unfold R.v6, N.v6.
  rewrite ?node_11464.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28678 (s : N.State) (i : N.Inputs) :
  R.v28678 (state s) (inputs i) = Zmod.unsigned (N.v28678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28678 s i)) at 1.
  unfold R.v28678, N.v28678.
  rewrite ?node_28676.
  rewrite ?node_28677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28679 (s : N.State) (i : N.Inputs) :
  R.v28679 (state s) (inputs i) = Zmod.unsigned (N.v28679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28679 s i)) at 1.
  unfold R.v28679, N.v28679.
  rewrite ?node_28675.
  rewrite ?node_28678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28680 (s : N.State) (i : N.Inputs) :
  R.v28680 (state s) (inputs i) = Zmod.unsigned (N.v28680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28680 s i)) at 1.
  unfold R.v28680, N.v28680.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28681 (s : N.State) (i : N.Inputs) :
  R.v28681 (state s) (inputs i) = Zmod.unsigned (N.v28681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28681 s i)) at 1.
  unfold R.v28681, N.v28681.
  rewrite ?node_11253.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28682 (s : N.State) (i : N.Inputs) :
  R.v28682 (state s) (inputs i) = Zmod.unsigned (N.v28682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28682 s i)) at 1.
  unfold R.v28682, N.v28682.
  unfold R.v16463, N.v16463.
  rewrite !state_r1325_nr_5F1326.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1325_nr_5F1326 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28683 (s : N.State) (i : N.Inputs) :
  R.v28683 (state s) (inputs i) = Zmod.unsigned (N.v28683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28683 s i)) at 1.
  unfold R.v28683, N.v28683.
  unfold R.v16463, N.v16463.
  rewrite !state_r1324_nr_5F1325.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1324_nr_5F1325 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28684 (s : N.State) (i : N.Inputs) :
  R.v28684 (state s) (inputs i) = Zmod.unsigned (N.v28684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28684 s i)) at 1.
  unfold R.v28684, N.v28684.
  unfold R.v6, N.v6.
  rewrite !state_r1323_nr_5F1324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1323_nr_5F1324 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28685 (s : N.State) (i : N.Inputs) :
  R.v28685 (state s) (inputs i) = Zmod.unsigned (N.v28685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28685 s i)) at 1.
  unfold R.v28685, N.v28685.
  unfold R.v6, N.v6.
  rewrite !state_r1322_nr_5F1323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1322_nr_5F1323 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28686 (s : N.State) (i : N.Inputs) :
  R.v28686 (state s) (inputs i) = Zmod.unsigned (N.v28686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28686 s i)) at 1.
  unfold R.v28686, N.v28686.
  rewrite ?node_28684.
  rewrite ?node_28685.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28687 (s : N.State) (i : N.Inputs) :
  R.v28687 (state s) (inputs i) = Zmod.unsigned (N.v28687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28687 s i)) at 1.
  unfold R.v28687, N.v28687.
  unfold R.v16484, N.v16484.
  rewrite ?node_28686.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28688 (s : N.State) (i : N.Inputs) :
  R.v28688 (state s) (inputs i) = Zmod.unsigned (N.v28688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28688 s i)) at 1.
  unfold R.v28688, N.v28688.
  rewrite ?node_28681.
  rewrite ?node_28682.
  rewrite ?node_28683.
  rewrite ?node_28687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28689 (s : N.State) (i : N.Inputs) :
  R.v28689 (state s) (inputs i) = Zmod.unsigned (N.v28689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28689 s i)) at 1.
  unfold R.v28689, N.v28689.
  unfold R.v6, N.v6.
  rewrite ?node_28688.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28690 (s : N.State) (i : N.Inputs) :
  R.v28690 (state s) (inputs i) = Zmod.unsigned (N.v28690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28690 s i)) at 1.
  unfold R.v28690, N.v28690.
  rewrite ?node_11254.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28691 (s : N.State) (i : N.Inputs) :
  R.v28691 (state s) (inputs i) = Zmod.unsigned (N.v28691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28691 s i)) at 1.
  unfold R.v28691, N.v28691.
  unfold R.v6, N.v6.
  rewrite ?node_11408.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28692 (s : N.State) (i : N.Inputs) :
  R.v28692 (state s) (inputs i) = Zmod.unsigned (N.v28692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28692 s i)) at 1.
  unfold R.v28692, N.v28692.
  unfold R.v6, N.v6.
  rewrite ?node_11467.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28693 (s : N.State) (i : N.Inputs) :
  R.v28693 (state s) (inputs i) = Zmod.unsigned (N.v28693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28693 s i)) at 1.
  unfold R.v28693, N.v28693.
  rewrite ?node_28690.
  rewrite ?node_28691.
  rewrite ?node_28692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28694 (s : N.State) (i : N.Inputs) :
  R.v28694 (state s) (inputs i) = Zmod.unsigned (N.v28694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28694 s i)) at 1.
  unfold R.v28694, N.v28694.
  rewrite ?node_28689.
  rewrite ?node_28693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28695 (s : N.State) (i : N.Inputs) :
  R.v28695 (state s) (inputs i) = Zmod.unsigned (N.v28695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28695 s i)) at 1.
  unfold R.v28695, N.v28695.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28696 (s : N.State) (i : N.Inputs) :
  R.v28696 (state s) (inputs i) = Zmod.unsigned (N.v28696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28696 s i)) at 1.
  unfold R.v28696, N.v28696.
  unfold R.v16463, N.v16463.
  rewrite !state_r1324_nr_5F1325.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1324_nr_5F1325 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28697 (s : N.State) (i : N.Inputs) :
  R.v28697 (state s) (inputs i) = Zmod.unsigned (N.v28697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28697 s i)) at 1.
  unfold R.v28697, N.v28697.
  unfold R.v6, N.v6.
  rewrite !state_r1323_nr_5F1324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1323_nr_5F1324 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28698 (s : N.State) (i : N.Inputs) :
  R.v28698 (state s) (inputs i) = Zmod.unsigned (N.v28698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28698 s i)) at 1.
  unfold R.v28698, N.v28698.
  unfold R.v6, N.v6.
  rewrite !state_r1322_nr_5F1323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1322_nr_5F1323 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28699 (s : N.State) (i : N.Inputs) :
  R.v28699 (state s) (inputs i) = Zmod.unsigned (N.v28699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28699 s i)) at 1.
  unfold R.v28699, N.v28699.
  rewrite ?node_28697.
  rewrite ?node_28698.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28700 (s : N.State) (i : N.Inputs) :
  R.v28700 (state s) (inputs i) = Zmod.unsigned (N.v28700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28700 s i)) at 1.
  unfold R.v28700, N.v28700.
  unfold R.v16484, N.v16484.
  rewrite ?node_28699.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28701 (s : N.State) (i : N.Inputs) :
  R.v28701 (state s) (inputs i) = Zmod.unsigned (N.v28701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28701 s i)) at 1.
  unfold R.v28701, N.v28701.
  rewrite ?node_28696.
  rewrite ?node_28700.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28702 (s : N.State) (i : N.Inputs) :
  R.v28702 (state s) (inputs i) = Zmod.unsigned (N.v28702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28702 s i)) at 1.
  unfold R.v28702, N.v28702.
  unfold R.v6, N.v6.
  rewrite ?node_28701.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28703 (s : N.State) (i : N.Inputs) :
  R.v28703 (state s) (inputs i) = Zmod.unsigned (N.v28703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28703 s i)) at 1.
  unfold R.v28703, N.v28703.
  rewrite ?node_11249.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28704 (s : N.State) (i : N.Inputs) :
  R.v28704 (state s) (inputs i) = Zmod.unsigned (N.v28704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28704 s i)) at 1.
  unfold R.v28704, N.v28704.
  unfold R.v6, N.v6.
  rewrite ?node_11408.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28705 (s : N.State) (i : N.Inputs) :
  R.v28705 (state s) (inputs i) = Zmod.unsigned (N.v28705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28705 s i)) at 1.
  unfold R.v28705, N.v28705.
  rewrite ?node_28703.
  rewrite ?node_28704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28706 (s : N.State) (i : N.Inputs) :
  R.v28706 (state s) (inputs i) = Zmod.unsigned (N.v28706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28706 s i)) at 1.
  unfold R.v28706, N.v28706.
  rewrite ?node_28702.
  rewrite ?node_28705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28707 (s : N.State) (i : N.Inputs) :
  R.v28707 (state s) (inputs i) = Zmod.unsigned (N.v28707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28707 s i)) at 1.
  unfold R.v28707, N.v28707.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28708 (s : N.State) (i : N.Inputs) :
  R.v28708 (state s) (inputs i) = Zmod.unsigned (N.v28708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28708 s i)) at 1.
  unfold R.v28708, N.v28708.
  rewrite ?node_11253.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28709 (s : N.State) (i : N.Inputs) :
  R.v28709 (state s) (inputs i) = Zmod.unsigned (N.v28709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28709 s i)) at 1.
  unfold R.v28709, N.v28709.
  unfold R.v6, N.v6.
  rewrite !state_r1325_nr_5F1326.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1325_nr_5F1326 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28710 (s : N.State) (i : N.Inputs) :
  R.v28710 (state s) (inputs i) = Zmod.unsigned (N.v28710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28710 s i)) at 1.
  unfold R.v28710, N.v28710.
  unfold R.v6, N.v6.
  rewrite ?node_11249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28711 (s : N.State) (i : N.Inputs) :
  R.v28711 (state s) (inputs i) = Zmod.unsigned (N.v28711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28711 s i)) at 1.
  unfold R.v28711, N.v28711.
  rewrite ?node_28709.
  rewrite ?node_28710.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28712 (s : N.State) (i : N.Inputs) :
  R.v28712 (state s) (inputs i) = Zmod.unsigned (N.v28712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28712 s i)) at 1.
  unfold R.v28712, N.v28712.
  unfold R.v16484, N.v16484.
  rewrite ?node_28711.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28713 (s : N.State) (i : N.Inputs) :
  R.v28713 (state s) (inputs i) = Zmod.unsigned (N.v28713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28713 s i)) at 1.
  unfold R.v28713, N.v28713.
  rewrite ?node_28708.
  rewrite ?node_28712.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28714 (s : N.State) (i : N.Inputs) :
  R.v28714 (state s) (inputs i) = Zmod.unsigned (N.v28714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28714 s i)) at 1.
  unfold R.v28714, N.v28714.
  unfold R.v6, N.v6.
  rewrite ?node_28713.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28715 (s : N.State) (i : N.Inputs) :
  R.v28715 (state s) (inputs i) = Zmod.unsigned (N.v28715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28715 s i)) at 1.
  unfold R.v28715, N.v28715.
  rewrite ?node_11254.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28716 (s : N.State) (i : N.Inputs) :
  R.v28716 (state s) (inputs i) = Zmod.unsigned (N.v28716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28716 s i)) at 1.
  unfold R.v28716, N.v28716.
  unfold R.v6, N.v6.
  rewrite ?node_11467.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28717 (s : N.State) (i : N.Inputs) :
  R.v28717 (state s) (inputs i) = Zmod.unsigned (N.v28717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28717 s i)) at 1.
  unfold R.v28717, N.v28717.
  rewrite ?node_28715.
  rewrite ?node_28716.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28718 (s : N.State) (i : N.Inputs) :
  R.v28718 (state s) (inputs i) = Zmod.unsigned (N.v28718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28718 s i)) at 1.
  unfold R.v28718, N.v28718.
  rewrite ?node_28714.
  rewrite ?node_28717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28719 (s : N.State) (i : N.Inputs) :
  R.v28719 (state s) (inputs i) = Zmod.unsigned (N.v28719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28719 s i)) at 1.
  unfold R.v28719, N.v28719.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28720 (s : N.State) (i : N.Inputs) :
  R.v28720 (state s) (inputs i) = Zmod.unsigned (N.v28720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28720 s i)) at 1.
  unfold R.v28720, N.v28720.
  rewrite ?node_11261.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28721 (s : N.State) (i : N.Inputs) :
  R.v28721 (state s) (inputs i) = Zmod.unsigned (N.v28721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28721 s i)) at 1.
  unfold R.v28721, N.v28721.
  unfold R.v16463, N.v16463.
  rewrite !state_r1329_nr_5F1330.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1329_nr_5F1330 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28722 (s : N.State) (i : N.Inputs) :
  R.v28722 (state s) (inputs i) = Zmod.unsigned (N.v28722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28722 s i)) at 1.
  unfold R.v28722, N.v28722.
  unfold R.v16463, N.v16463.
  rewrite !state_r1328_nr_5F1329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1328_nr_5F1329 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28723 (s : N.State) (i : N.Inputs) :
  R.v28723 (state s) (inputs i) = Zmod.unsigned (N.v28723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28723 s i)) at 1.
  unfold R.v28723, N.v28723.
  unfold R.v6, N.v6.
  rewrite !state_r1327_nr_5F1328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1327_nr_5F1328 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28724 (s : N.State) (i : N.Inputs) :
  R.v28724 (state s) (inputs i) = Zmod.unsigned (N.v28724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28724 s i)) at 1.
  unfold R.v28724, N.v28724.
  unfold R.v6, N.v6.
  rewrite !state_r1326_nr_5F1327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1326_nr_5F1327 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28725 (s : N.State) (i : N.Inputs) :
  R.v28725 (state s) (inputs i) = Zmod.unsigned (N.v28725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28725 s i)) at 1.
  unfold R.v28725, N.v28725.
  rewrite ?node_28723.
  rewrite ?node_28724.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28726 (s : N.State) (i : N.Inputs) :
  R.v28726 (state s) (inputs i) = Zmod.unsigned (N.v28726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28726 s i)) at 1.
  unfold R.v28726, N.v28726.
  unfold R.v16484, N.v16484.
  rewrite ?node_28725.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28727 (s : N.State) (i : N.Inputs) :
  R.v28727 (state s) (inputs i) = Zmod.unsigned (N.v28727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28727 s i)) at 1.
  unfold R.v28727, N.v28727.
  rewrite ?node_28720.
  rewrite ?node_28721.
  rewrite ?node_28722.
  rewrite ?node_28726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28728 (s : N.State) (i : N.Inputs) :
  R.v28728 (state s) (inputs i) = Zmod.unsigned (N.v28728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28728 s i)) at 1.
  unfold R.v28728, N.v28728.
  unfold R.v6, N.v6.
  rewrite ?node_28727.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28729 (s : N.State) (i : N.Inputs) :
  R.v28729 (state s) (inputs i) = Zmod.unsigned (N.v28729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28729 s i)) at 1.
  unfold R.v28729, N.v28729.
  rewrite ?node_11262.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28730 (s : N.State) (i : N.Inputs) :
  R.v28730 (state s) (inputs i) = Zmod.unsigned (N.v28730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28730 s i)) at 1.
  unfold R.v28730, N.v28730.
  unfold R.v6, N.v6.
  rewrite ?node_11416.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28731 (s : N.State) (i : N.Inputs) :
  R.v28731 (state s) (inputs i) = Zmod.unsigned (N.v28731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28731 s i)) at 1.
  unfold R.v28731, N.v28731.
  unfold R.v6, N.v6.
  rewrite ?node_11471.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28732 (s : N.State) (i : N.Inputs) :
  R.v28732 (state s) (inputs i) = Zmod.unsigned (N.v28732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28732 s i)) at 1.
  unfold R.v28732, N.v28732.
  rewrite ?node_28729.
  rewrite ?node_28730.
  rewrite ?node_28731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28733 (s : N.State) (i : N.Inputs) :
  R.v28733 (state s) (inputs i) = Zmod.unsigned (N.v28733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28733 s i)) at 1.
  unfold R.v28733, N.v28733.
  rewrite ?node_28728.
  rewrite ?node_28732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28734 (s : N.State) (i : N.Inputs) :
  R.v28734 (state s) (inputs i) = Zmod.unsigned (N.v28734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28734 s i)) at 1.
  unfold R.v28734, N.v28734.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28735 (s : N.State) (i : N.Inputs) :
  R.v28735 (state s) (inputs i) = Zmod.unsigned (N.v28735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28735 s i)) at 1.
  unfold R.v28735, N.v28735.
  unfold R.v16463, N.v16463.
  rewrite !state_r1328_nr_5F1329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1328_nr_5F1329 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28736 (s : N.State) (i : N.Inputs) :
  R.v28736 (state s) (inputs i) = Zmod.unsigned (N.v28736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28736 s i)) at 1.
  unfold R.v28736, N.v28736.
  unfold R.v6, N.v6.
  rewrite !state_r1327_nr_5F1328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1327_nr_5F1328 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28737 (s : N.State) (i : N.Inputs) :
  R.v28737 (state s) (inputs i) = Zmod.unsigned (N.v28737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28737 s i)) at 1.
  unfold R.v28737, N.v28737.
  unfold R.v6, N.v6.
  rewrite !state_r1326_nr_5F1327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1326_nr_5F1327 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28738 (s : N.State) (i : N.Inputs) :
  R.v28738 (state s) (inputs i) = Zmod.unsigned (N.v28738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28738 s i)) at 1.
  unfold R.v28738, N.v28738.
  rewrite ?node_28736.
  rewrite ?node_28737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28739 (s : N.State) (i : N.Inputs) :
  R.v28739 (state s) (inputs i) = Zmod.unsigned (N.v28739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28739 s i)) at 1.
  unfold R.v28739, N.v28739.
  unfold R.v16484, N.v16484.
  rewrite ?node_28738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28740 (s : N.State) (i : N.Inputs) :
  R.v28740 (state s) (inputs i) = Zmod.unsigned (N.v28740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28740 s i)) at 1.
  unfold R.v28740, N.v28740.
  rewrite ?node_28735.
  rewrite ?node_28739.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28741 (s : N.State) (i : N.Inputs) :
  R.v28741 (state s) (inputs i) = Zmod.unsigned (N.v28741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28741 s i)) at 1.
  unfold R.v28741, N.v28741.
  unfold R.v6, N.v6.
  rewrite ?node_28740.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28742 (s : N.State) (i : N.Inputs) :
  R.v28742 (state s) (inputs i) = Zmod.unsigned (N.v28742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28742 s i)) at 1.
  unfold R.v28742, N.v28742.
  rewrite ?node_11257.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28743 (s : N.State) (i : N.Inputs) :
  R.v28743 (state s) (inputs i) = Zmod.unsigned (N.v28743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28743 s i)) at 1.
  unfold R.v28743, N.v28743.
  unfold R.v6, N.v6.
  rewrite ?node_11416.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28744 (s : N.State) (i : N.Inputs) :
  R.v28744 (state s) (inputs i) = Zmod.unsigned (N.v28744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28744 s i)) at 1.
  unfold R.v28744, N.v28744.
  rewrite ?node_28742.
  rewrite ?node_28743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28745 (s : N.State) (i : N.Inputs) :
  R.v28745 (state s) (inputs i) = Zmod.unsigned (N.v28745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28745 s i)) at 1.
  unfold R.v28745, N.v28745.
  rewrite ?node_28741.
  rewrite ?node_28744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28746 (s : N.State) (i : N.Inputs) :
  R.v28746 (state s) (inputs i) = Zmod.unsigned (N.v28746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28746 s i)) at 1.
  unfold R.v28746, N.v28746.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28747 (s : N.State) (i : N.Inputs) :
  R.v28747 (state s) (inputs i) = Zmod.unsigned (N.v28747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28747 s i)) at 1.
  unfold R.v28747, N.v28747.
  rewrite ?node_11261.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28748 (s : N.State) (i : N.Inputs) :
  R.v28748 (state s) (inputs i) = Zmod.unsigned (N.v28748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28748 s i)) at 1.
  unfold R.v28748, N.v28748.
  unfold R.v6, N.v6.
  rewrite !state_r1329_nr_5F1330.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1329_nr_5F1330 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28749 (s : N.State) (i : N.Inputs) :
  R.v28749 (state s) (inputs i) = Zmod.unsigned (N.v28749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28749 s i)) at 1.
  unfold R.v28749, N.v28749.
  unfold R.v6, N.v6.
  rewrite ?node_11257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28750 (s : N.State) (i : N.Inputs) :
  R.v28750 (state s) (inputs i) = Zmod.unsigned (N.v28750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28750 s i)) at 1.
  unfold R.v28750, N.v28750.
  rewrite ?node_28748.
  rewrite ?node_28749.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28751 (s : N.State) (i : N.Inputs) :
  R.v28751 (state s) (inputs i) = Zmod.unsigned (N.v28751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28751 s i)) at 1.
  unfold R.v28751, N.v28751.
  unfold R.v16484, N.v16484.
  rewrite ?node_28750.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28752 (s : N.State) (i : N.Inputs) :
  R.v28752 (state s) (inputs i) = Zmod.unsigned (N.v28752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28752 s i)) at 1.
  unfold R.v28752, N.v28752.
  rewrite ?node_28747.
  rewrite ?node_28751.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28753 (s : N.State) (i : N.Inputs) :
  R.v28753 (state s) (inputs i) = Zmod.unsigned (N.v28753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28753 s i)) at 1.
  unfold R.v28753, N.v28753.
  unfold R.v6, N.v6.
  rewrite ?node_28752.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28754 (s : N.State) (i : N.Inputs) :
  R.v28754 (state s) (inputs i) = Zmod.unsigned (N.v28754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28754 s i)) at 1.
  unfold R.v28754, N.v28754.
  rewrite ?node_11262.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28755 (s : N.State) (i : N.Inputs) :
  R.v28755 (state s) (inputs i) = Zmod.unsigned (N.v28755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28755 s i)) at 1.
  unfold R.v28755, N.v28755.
  unfold R.v6, N.v6.
  rewrite ?node_11471.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28756 (s : N.State) (i : N.Inputs) :
  R.v28756 (state s) (inputs i) = Zmod.unsigned (N.v28756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28756 s i)) at 1.
  unfold R.v28756, N.v28756.
  rewrite ?node_28754.
  rewrite ?node_28755.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28757 (s : N.State) (i : N.Inputs) :
  R.v28757 (state s) (inputs i) = Zmod.unsigned (N.v28757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28757 s i)) at 1.
  unfold R.v28757, N.v28757.
  rewrite ?node_28753.
  rewrite ?node_28756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28758 (s : N.State) (i : N.Inputs) :
  R.v28758 (state s) (inputs i) = Zmod.unsigned (N.v28758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28758 s i)) at 1.
  unfold R.v28758, N.v28758.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28759 (s : N.State) (i : N.Inputs) :
  R.v28759 (state s) (inputs i) = Zmod.unsigned (N.v28759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28759 s i)) at 1.
  unfold R.v28759, N.v28759.
  rewrite ?node_11269.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28760 (s : N.State) (i : N.Inputs) :
  R.v28760 (state s) (inputs i) = Zmod.unsigned (N.v28760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28760 s i)) at 1.
  unfold R.v28760, N.v28760.
  unfold R.v16463, N.v16463.
  rewrite !state_r1333_nr_5F1334.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1333_nr_5F1334 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28761 (s : N.State) (i : N.Inputs) :
  R.v28761 (state s) (inputs i) = Zmod.unsigned (N.v28761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28761 s i)) at 1.
  unfold R.v28761, N.v28761.
  unfold R.v16463, N.v16463.
  rewrite !state_r1332_nr_5F1333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1332_nr_5F1333 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28762 (s : N.State) (i : N.Inputs) :
  R.v28762 (state s) (inputs i) = Zmod.unsigned (N.v28762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28762 s i)) at 1.
  unfold R.v28762, N.v28762.
  unfold R.v6, N.v6.
  rewrite !state_r1331_nr_5F1332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1331_nr_5F1332 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28763 (s : N.State) (i : N.Inputs) :
  R.v28763 (state s) (inputs i) = Zmod.unsigned (N.v28763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28763 s i)) at 1.
  unfold R.v28763, N.v28763.
  unfold R.v6, N.v6.
  rewrite !state_r1330_nr_5F1331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1330_nr_5F1331 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28764 (s : N.State) (i : N.Inputs) :
  R.v28764 (state s) (inputs i) = Zmod.unsigned (N.v28764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28764 s i)) at 1.
  unfold R.v28764, N.v28764.
  rewrite ?node_28762.
  rewrite ?node_28763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28765 (s : N.State) (i : N.Inputs) :
  R.v28765 (state s) (inputs i) = Zmod.unsigned (N.v28765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28765 s i)) at 1.
  unfold R.v28765, N.v28765.
  unfold R.v16484, N.v16484.
  rewrite ?node_28764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28766 (s : N.State) (i : N.Inputs) :
  R.v28766 (state s) (inputs i) = Zmod.unsigned (N.v28766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28766 s i)) at 1.
  unfold R.v28766, N.v28766.
  rewrite ?node_28759.
  rewrite ?node_28760.
  rewrite ?node_28761.
  rewrite ?node_28765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28767 (s : N.State) (i : N.Inputs) :
  R.v28767 (state s) (inputs i) = Zmod.unsigned (N.v28767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28767 s i)) at 1.
  unfold R.v28767, N.v28767.
  unfold R.v6, N.v6.
  rewrite ?node_28766.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28768 (s : N.State) (i : N.Inputs) :
  R.v28768 (state s) (inputs i) = Zmod.unsigned (N.v28768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28768 s i)) at 1.
  unfold R.v28768, N.v28768.
  rewrite ?node_11270.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28769 (s : N.State) (i : N.Inputs) :
  R.v28769 (state s) (inputs i) = Zmod.unsigned (N.v28769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28769 s i)) at 1.
  unfold R.v28769, N.v28769.
  unfold R.v6, N.v6.
  rewrite ?node_11424.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28770 (s : N.State) (i : N.Inputs) :
  R.v28770 (state s) (inputs i) = Zmod.unsigned (N.v28770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28770 s i)) at 1.
  unfold R.v28770, N.v28770.
  unfold R.v6, N.v6.
  rewrite ?node_11475.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28771 (s : N.State) (i : N.Inputs) :
  R.v28771 (state s) (inputs i) = Zmod.unsigned (N.v28771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28771 s i)) at 1.
  unfold R.v28771, N.v28771.
  rewrite ?node_28768.
  rewrite ?node_28769.
  rewrite ?node_28770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28772 (s : N.State) (i : N.Inputs) :
  R.v28772 (state s) (inputs i) = Zmod.unsigned (N.v28772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28772 s i)) at 1.
  unfold R.v28772, N.v28772.
  rewrite ?node_28767.
  rewrite ?node_28771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28773 (s : N.State) (i : N.Inputs) :
  R.v28773 (state s) (inputs i) = Zmod.unsigned (N.v28773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28773 s i)) at 1.
  unfold R.v28773, N.v28773.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28774 (s : N.State) (i : N.Inputs) :
  R.v28774 (state s) (inputs i) = Zmod.unsigned (N.v28774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28774 s i)) at 1.
  unfold R.v28774, N.v28774.
  unfold R.v16463, N.v16463.
  rewrite !state_r1332_nr_5F1333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1332_nr_5F1333 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28775 (s : N.State) (i : N.Inputs) :
  R.v28775 (state s) (inputs i) = Zmod.unsigned (N.v28775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28775 s i)) at 1.
  unfold R.v28775, N.v28775.
  unfold R.v6, N.v6.
  rewrite !state_r1331_nr_5F1332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1331_nr_5F1332 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28776 (s : N.State) (i : N.Inputs) :
  R.v28776 (state s) (inputs i) = Zmod.unsigned (N.v28776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28776 s i)) at 1.
  unfold R.v28776, N.v28776.
  unfold R.v6, N.v6.
  rewrite !state_r1330_nr_5F1331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1330_nr_5F1331 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28777 (s : N.State) (i : N.Inputs) :
  R.v28777 (state s) (inputs i) = Zmod.unsigned (N.v28777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28777 s i)) at 1.
  unfold R.v28777, N.v28777.
  rewrite ?node_28775.
  rewrite ?node_28776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28778 (s : N.State) (i : N.Inputs) :
  R.v28778 (state s) (inputs i) = Zmod.unsigned (N.v28778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28778 s i)) at 1.
  unfold R.v28778, N.v28778.
  unfold R.v16484, N.v16484.
  rewrite ?node_28777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28779 (s : N.State) (i : N.Inputs) :
  R.v28779 (state s) (inputs i) = Zmod.unsigned (N.v28779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28779 s i)) at 1.
  unfold R.v28779, N.v28779.
  rewrite ?node_28774.
  rewrite ?node_28778.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28780 (s : N.State) (i : N.Inputs) :
  R.v28780 (state s) (inputs i) = Zmod.unsigned (N.v28780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28780 s i)) at 1.
  unfold R.v28780, N.v28780.
  unfold R.v6, N.v6.
  rewrite ?node_28779.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28781 (s : N.State) (i : N.Inputs) :
  R.v28781 (state s) (inputs i) = Zmod.unsigned (N.v28781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28781 s i)) at 1.
  unfold R.v28781, N.v28781.
  rewrite ?node_11265.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28782 (s : N.State) (i : N.Inputs) :
  R.v28782 (state s) (inputs i) = Zmod.unsigned (N.v28782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28782 s i)) at 1.
  unfold R.v28782, N.v28782.
  unfold R.v6, N.v6.
  rewrite ?node_11424.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28783 (s : N.State) (i : N.Inputs) :
  R.v28783 (state s) (inputs i) = Zmod.unsigned (N.v28783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28783 s i)) at 1.
  unfold R.v28783, N.v28783.
  rewrite ?node_28781.
  rewrite ?node_28782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28784 (s : N.State) (i : N.Inputs) :
  R.v28784 (state s) (inputs i) = Zmod.unsigned (N.v28784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28784 s i)) at 1.
  unfold R.v28784, N.v28784.
  rewrite ?node_28780.
  rewrite ?node_28783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28785 (s : N.State) (i : N.Inputs) :
  R.v28785 (state s) (inputs i) = Zmod.unsigned (N.v28785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28785 s i)) at 1.
  unfold R.v28785, N.v28785.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28786 (s : N.State) (i : N.Inputs) :
  R.v28786 (state s) (inputs i) = Zmod.unsigned (N.v28786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28786 s i)) at 1.
  unfold R.v28786, N.v28786.
  rewrite ?node_11269.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28787 (s : N.State) (i : N.Inputs) :
  R.v28787 (state s) (inputs i) = Zmod.unsigned (N.v28787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28787 s i)) at 1.
  unfold R.v28787, N.v28787.
  unfold R.v6, N.v6.
  rewrite !state_r1333_nr_5F1334.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1333_nr_5F1334 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28788 (s : N.State) (i : N.Inputs) :
  R.v28788 (state s) (inputs i) = Zmod.unsigned (N.v28788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28788 s i)) at 1.
  unfold R.v28788, N.v28788.
  unfold R.v6, N.v6.
  rewrite ?node_11265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28789 (s : N.State) (i : N.Inputs) :
  R.v28789 (state s) (inputs i) = Zmod.unsigned (N.v28789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28789 s i)) at 1.
  unfold R.v28789, N.v28789.
  rewrite ?node_28787.
  rewrite ?node_28788.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28790 (s : N.State) (i : N.Inputs) :
  R.v28790 (state s) (inputs i) = Zmod.unsigned (N.v28790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28790 s i)) at 1.
  unfold R.v28790, N.v28790.
  unfold R.v16484, N.v16484.
  rewrite ?node_28789.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28791 (s : N.State) (i : N.Inputs) :
  R.v28791 (state s) (inputs i) = Zmod.unsigned (N.v28791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28791 s i)) at 1.
  unfold R.v28791, N.v28791.
  rewrite ?node_28786.
  rewrite ?node_28790.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28792 (s : N.State) (i : N.Inputs) :
  R.v28792 (state s) (inputs i) = Zmod.unsigned (N.v28792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28792 s i)) at 1.
  unfold R.v28792, N.v28792.
  unfold R.v6, N.v6.
  rewrite ?node_28791.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28793 (s : N.State) (i : N.Inputs) :
  R.v28793 (state s) (inputs i) = Zmod.unsigned (N.v28793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28793 s i)) at 1.
  unfold R.v28793, N.v28793.
  rewrite ?node_11270.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28794 (s : N.State) (i : N.Inputs) :
  R.v28794 (state s) (inputs i) = Zmod.unsigned (N.v28794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28794 s i)) at 1.
  unfold R.v28794, N.v28794.
  unfold R.v6, N.v6.
  rewrite ?node_11475.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28795 (s : N.State) (i : N.Inputs) :
  R.v28795 (state s) (inputs i) = Zmod.unsigned (N.v28795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28795 s i)) at 1.
  unfold R.v28795, N.v28795.
  rewrite ?node_28793.
  rewrite ?node_28794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28796 (s : N.State) (i : N.Inputs) :
  R.v28796 (state s) (inputs i) = Zmod.unsigned (N.v28796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28796 s i)) at 1.
  unfold R.v28796, N.v28796.
  rewrite ?node_28792.
  rewrite ?node_28795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28797 (s : N.State) (i : N.Inputs) :
  R.v28797 (state s) (inputs i) = Zmod.unsigned (N.v28797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28797 s i)) at 1.
  unfold R.v28797, N.v28797.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28798 (s : N.State) (i : N.Inputs) :
  R.v28798 (state s) (inputs i) = Zmod.unsigned (N.v28798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28798 s i)) at 1.
  unfold R.v28798, N.v28798.
  rewrite ?node_11281.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28799 (s : N.State) (i : N.Inputs) :
  R.v28799 (state s) (inputs i) = Zmod.unsigned (N.v28799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28799 s i)) at 1.
  unfold R.v28799, N.v28799.
  unfold R.v16463, N.v16463.
  rewrite !state_r1337_nr_5F1338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1337_nr_5F1338 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28800 (s : N.State) (i : N.Inputs) :
  R.v28800 (state s) (inputs i) = Zmod.unsigned (N.v28800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28800 s i)) at 1.
  unfold R.v28800, N.v28800.
  unfold R.v16463, N.v16463.
  rewrite !state_r1336_nr_5F1337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1336_nr_5F1337 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28801 (s : N.State) (i : N.Inputs) :
  R.v28801 (state s) (inputs i) = Zmod.unsigned (N.v28801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28801 s i)) at 1.
  unfold R.v28801, N.v28801.
  unfold R.v6, N.v6.
  rewrite !state_r1335_nr_5F1336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1335_nr_5F1336 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28802 (s : N.State) (i : N.Inputs) :
  R.v28802 (state s) (inputs i) = Zmod.unsigned (N.v28802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28802 s i)) at 1.
  unfold R.v28802, N.v28802.
  unfold R.v6, N.v6.
  rewrite !state_r1334_nr_5F1335.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1334_nr_5F1335 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28803 (s : N.State) (i : N.Inputs) :
  R.v28803 (state s) (inputs i) = Zmod.unsigned (N.v28803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28803 s i)) at 1.
  unfold R.v28803, N.v28803.
  rewrite ?node_28801.
  rewrite ?node_28802.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28804 (s : N.State) (i : N.Inputs) :
  R.v28804 (state s) (inputs i) = Zmod.unsigned (N.v28804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28804 s i)) at 1.
  unfold R.v28804, N.v28804.
  unfold R.v16484, N.v16484.
  rewrite ?node_28803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28805 (s : N.State) (i : N.Inputs) :
  R.v28805 (state s) (inputs i) = Zmod.unsigned (N.v28805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28805 s i)) at 1.
  unfold R.v28805, N.v28805.
  rewrite ?node_28798.
  rewrite ?node_28799.
  rewrite ?node_28800.
  rewrite ?node_28804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28806 (s : N.State) (i : N.Inputs) :
  R.v28806 (state s) (inputs i) = Zmod.unsigned (N.v28806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28806 s i)) at 1.
  unfold R.v28806, N.v28806.
  unfold R.v6, N.v6.
  rewrite ?node_28805.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28807 (s : N.State) (i : N.Inputs) :
  R.v28807 (state s) (inputs i) = Zmod.unsigned (N.v28807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28807 s i)) at 1.
  unfold R.v28807, N.v28807.
  rewrite ?node_11282.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28808 (s : N.State) (i : N.Inputs) :
  R.v28808 (state s) (inputs i) = Zmod.unsigned (N.v28808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28808 s i)) at 1.
  unfold R.v28808, N.v28808.
  unfold R.v6, N.v6.
  rewrite ?node_11436.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28809 (s : N.State) (i : N.Inputs) :
  R.v28809 (state s) (inputs i) = Zmod.unsigned (N.v28809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28809 s i)) at 1.
  unfold R.v28809, N.v28809.
  unfold R.v6, N.v6.
  rewrite ?node_11484.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28810 (s : N.State) (i : N.Inputs) :
  R.v28810 (state s) (inputs i) = Zmod.unsigned (N.v28810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28810 s i)) at 1.
  unfold R.v28810, N.v28810.
  rewrite ?node_28807.
  rewrite ?node_28808.
  rewrite ?node_28809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28811 (s : N.State) (i : N.Inputs) :
  R.v28811 (state s) (inputs i) = Zmod.unsigned (N.v28811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28811 s i)) at 1.
  unfold R.v28811, N.v28811.
  rewrite ?node_28806.
  rewrite ?node_28810.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28812 (s : N.State) (i : N.Inputs) :
  R.v28812 (state s) (inputs i) = Zmod.unsigned (N.v28812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28812 s i)) at 1.
  unfold R.v28812, N.v28812.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28813 (s : N.State) (i : N.Inputs) :
  R.v28813 (state s) (inputs i) = Zmod.unsigned (N.v28813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28813 s i)) at 1.
  unfold R.v28813, N.v28813.
  unfold R.v16463, N.v16463.
  rewrite !state_r1336_nr_5F1337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1336_nr_5F1337 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28814 (s : N.State) (i : N.Inputs) :
  R.v28814 (state s) (inputs i) = Zmod.unsigned (N.v28814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28814 s i)) at 1.
  unfold R.v28814, N.v28814.
  unfold R.v6, N.v6.
  rewrite !state_r1335_nr_5F1336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1335_nr_5F1336 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28815 (s : N.State) (i : N.Inputs) :
  R.v28815 (state s) (inputs i) = Zmod.unsigned (N.v28815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28815 s i)) at 1.
  unfold R.v28815, N.v28815.
  unfold R.v6, N.v6.
  rewrite !state_r1334_nr_5F1335.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1334_nr_5F1335 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28816 (s : N.State) (i : N.Inputs) :
  R.v28816 (state s) (inputs i) = Zmod.unsigned (N.v28816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28816 s i)) at 1.
  unfold R.v28816, N.v28816.
  rewrite ?node_28814.
  rewrite ?node_28815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28817 (s : N.State) (i : N.Inputs) :
  R.v28817 (state s) (inputs i) = Zmod.unsigned (N.v28817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28817 s i)) at 1.
  unfold R.v28817, N.v28817.
  unfold R.v16484, N.v16484.
  rewrite ?node_28816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28818 (s : N.State) (i : N.Inputs) :
  R.v28818 (state s) (inputs i) = Zmod.unsigned (N.v28818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28818 s i)) at 1.
  unfold R.v28818, N.v28818.
  rewrite ?node_28813.
  rewrite ?node_28817.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28819 (s : N.State) (i : N.Inputs) :
  R.v28819 (state s) (inputs i) = Zmod.unsigned (N.v28819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28819 s i)) at 1.
  unfold R.v28819, N.v28819.
  unfold R.v6, N.v6.
  rewrite ?node_28818.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28820 (s : N.State) (i : N.Inputs) :
  R.v28820 (state s) (inputs i) = Zmod.unsigned (N.v28820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28820 s i)) at 1.
  unfold R.v28820, N.v28820.
  rewrite ?node_11277.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28821 (s : N.State) (i : N.Inputs) :
  R.v28821 (state s) (inputs i) = Zmod.unsigned (N.v28821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28821 s i)) at 1.
  unfold R.v28821, N.v28821.
  unfold R.v6, N.v6.
  rewrite ?node_11436.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28822 (s : N.State) (i : N.Inputs) :
  R.v28822 (state s) (inputs i) = Zmod.unsigned (N.v28822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28822 s i)) at 1.
  unfold R.v28822, N.v28822.
  rewrite ?node_28820.
  rewrite ?node_28821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28823 (s : N.State) (i : N.Inputs) :
  R.v28823 (state s) (inputs i) = Zmod.unsigned (N.v28823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28823 s i)) at 1.
  unfold R.v28823, N.v28823.
  rewrite ?node_28819.
  rewrite ?node_28822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28824 (s : N.State) (i : N.Inputs) :
  R.v28824 (state s) (inputs i) = Zmod.unsigned (N.v28824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28824 s i)) at 1.
  unfold R.v28824, N.v28824.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28825 (s : N.State) (i : N.Inputs) :
  R.v28825 (state s) (inputs i) = Zmod.unsigned (N.v28825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28825 s i)) at 1.
  unfold R.v28825, N.v28825.
  rewrite ?node_11281.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28826 (s : N.State) (i : N.Inputs) :
  R.v28826 (state s) (inputs i) = Zmod.unsigned (N.v28826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28826 s i)) at 1.
  unfold R.v28826, N.v28826.
  unfold R.v6, N.v6.
  rewrite !state_r1337_nr_5F1338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1337_nr_5F1338 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28827 (s : N.State) (i : N.Inputs) :
  R.v28827 (state s) (inputs i) = Zmod.unsigned (N.v28827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28827 s i)) at 1.
  unfold R.v28827, N.v28827.
  unfold R.v6, N.v6.
  rewrite ?node_11277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28828 (s : N.State) (i : N.Inputs) :
  R.v28828 (state s) (inputs i) = Zmod.unsigned (N.v28828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28828 s i)) at 1.
  unfold R.v28828, N.v28828.
  rewrite ?node_28826.
  rewrite ?node_28827.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28829 (s : N.State) (i : N.Inputs) :
  R.v28829 (state s) (inputs i) = Zmod.unsigned (N.v28829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28829 s i)) at 1.
  unfold R.v28829, N.v28829.
  unfold R.v16484, N.v16484.
  rewrite ?node_28828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28830 (s : N.State) (i : N.Inputs) :
  R.v28830 (state s) (inputs i) = Zmod.unsigned (N.v28830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28830 s i)) at 1.
  unfold R.v28830, N.v28830.
  rewrite ?node_28825.
  rewrite ?node_28829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28831 (s : N.State) (i : N.Inputs) :
  R.v28831 (state s) (inputs i) = Zmod.unsigned (N.v28831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28831 s i)) at 1.
  unfold R.v28831, N.v28831.
  unfold R.v6, N.v6.
  rewrite ?node_28830.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28832 (s : N.State) (i : N.Inputs) :
  R.v28832 (state s) (inputs i) = Zmod.unsigned (N.v28832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28832 s i)) at 1.
  unfold R.v28832, N.v28832.
  rewrite ?node_11282.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28833 (s : N.State) (i : N.Inputs) :
  R.v28833 (state s) (inputs i) = Zmod.unsigned (N.v28833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28833 s i)) at 1.
  unfold R.v28833, N.v28833.
  unfold R.v6, N.v6.
  rewrite ?node_11484.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28834 (s : N.State) (i : N.Inputs) :
  R.v28834 (state s) (inputs i) = Zmod.unsigned (N.v28834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28834 s i)) at 1.
  unfold R.v28834, N.v28834.
  rewrite ?node_28832.
  rewrite ?node_28833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28835 (s : N.State) (i : N.Inputs) :
  R.v28835 (state s) (inputs i) = Zmod.unsigned (N.v28835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28835 s i)) at 1.
  unfold R.v28835, N.v28835.
  rewrite ?node_28831.
  rewrite ?node_28834.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28836 (s : N.State) (i : N.Inputs) :
  R.v28836 (state s) (inputs i) = Zmod.unsigned (N.v28836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28836 s i)) at 1.
  unfold R.v28836, N.v28836.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28837 (s : N.State) (i : N.Inputs) :
  R.v28837 (state s) (inputs i) = Zmod.unsigned (N.v28837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28837 s i)) at 1.
  unfold R.v28837, N.v28837.
  rewrite ?node_11288.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28838 (s : N.State) (i : N.Inputs) :
  R.v28838 (state s) (inputs i) = Zmod.unsigned (N.v28838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28838 s i)) at 1.
  unfold R.v28838, N.v28838.
  unfold R.v16463, N.v16463.
  rewrite !state_r1341_nr_5F1342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1341_nr_5F1342 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28839 (s : N.State) (i : N.Inputs) :
  R.v28839 (state s) (inputs i) = Zmod.unsigned (N.v28839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28839 s i)) at 1.
  unfold R.v28839, N.v28839.
  unfold R.v16463, N.v16463.
  rewrite !state_r1340_nr_5F1341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1340_nr_5F1341 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28840 (s : N.State) (i : N.Inputs) :
  R.v28840 (state s) (inputs i) = Zmod.unsigned (N.v28840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28840 s i)) at 1.
  unfold R.v28840, N.v28840.
  unfold R.v6, N.v6.
  rewrite !state_r1339_nr_5F1340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1339_nr_5F1340 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28841 (s : N.State) (i : N.Inputs) :
  R.v28841 (state s) (inputs i) = Zmod.unsigned (N.v28841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28841 s i)) at 1.
  unfold R.v28841, N.v28841.
  unfold R.v6, N.v6.
  rewrite !state_r1338_nr_5F1339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1338_nr_5F1339 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28842 (s : N.State) (i : N.Inputs) :
  R.v28842 (state s) (inputs i) = Zmod.unsigned (N.v28842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28842 s i)) at 1.
  unfold R.v28842, N.v28842.
  rewrite ?node_28840.
  rewrite ?node_28841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28843 (s : N.State) (i : N.Inputs) :
  R.v28843 (state s) (inputs i) = Zmod.unsigned (N.v28843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28843 s i)) at 1.
  unfold R.v28843, N.v28843.
  unfold R.v16484, N.v16484.
  rewrite ?node_28842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28844 (s : N.State) (i : N.Inputs) :
  R.v28844 (state s) (inputs i) = Zmod.unsigned (N.v28844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28844 s i)) at 1.
  unfold R.v28844, N.v28844.
  rewrite ?node_28837.
  rewrite ?node_28838.
  rewrite ?node_28839.
  rewrite ?node_28843.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28845 (s : N.State) (i : N.Inputs) :
  R.v28845 (state s) (inputs i) = Zmod.unsigned (N.v28845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28845 s i)) at 1.
  unfold R.v28845, N.v28845.
  unfold R.v6, N.v6.
  rewrite ?node_28844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28846 (s : N.State) (i : N.Inputs) :
  R.v28846 (state s) (inputs i) = Zmod.unsigned (N.v28846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28846 s i)) at 1.
  unfold R.v28846, N.v28846.
  rewrite ?node_11289.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28847 (s : N.State) (i : N.Inputs) :
  R.v28847 (state s) (inputs i) = Zmod.unsigned (N.v28847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28847 s i)) at 1.
  unfold R.v28847, N.v28847.
  unfold R.v6, N.v6.
  rewrite ?node_11443.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28848 (s : N.State) (i : N.Inputs) :
  R.v28848 (state s) (inputs i) = Zmod.unsigned (N.v28848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28848 s i)) at 1.
  unfold R.v28848, N.v28848.
  unfold R.v6, N.v6.
  rewrite ?node_11487.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28849 (s : N.State) (i : N.Inputs) :
  R.v28849 (state s) (inputs i) = Zmod.unsigned (N.v28849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28849 s i)) at 1.
  unfold R.v28849, N.v28849.
  rewrite ?node_28846.
  rewrite ?node_28847.
  rewrite ?node_28848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28850 (s : N.State) (i : N.Inputs) :
  R.v28850 (state s) (inputs i) = Zmod.unsigned (N.v28850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28850 s i)) at 1.
  unfold R.v28850, N.v28850.
  rewrite ?node_28845.
  rewrite ?node_28849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28851 (s : N.State) (i : N.Inputs) :
  R.v28851 (state s) (inputs i) = Zmod.unsigned (N.v28851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28851 s i)) at 1.
  unfold R.v28851, N.v28851.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28852 (s : N.State) (i : N.Inputs) :
  R.v28852 (state s) (inputs i) = Zmod.unsigned (N.v28852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28852 s i)) at 1.
  unfold R.v28852, N.v28852.
  unfold R.v16463, N.v16463.
  rewrite !state_r1340_nr_5F1341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1340_nr_5F1341 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28853 (s : N.State) (i : N.Inputs) :
  R.v28853 (state s) (inputs i) = Zmod.unsigned (N.v28853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28853 s i)) at 1.
  unfold R.v28853, N.v28853.
  unfold R.v6, N.v6.
  rewrite !state_r1339_nr_5F1340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1339_nr_5F1340 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28854 (s : N.State) (i : N.Inputs) :
  R.v28854 (state s) (inputs i) = Zmod.unsigned (N.v28854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28854 s i)) at 1.
  unfold R.v28854, N.v28854.
  unfold R.v6, N.v6.
  rewrite !state_r1338_nr_5F1339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1338_nr_5F1339 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28855 (s : N.State) (i : N.Inputs) :
  R.v28855 (state s) (inputs i) = Zmod.unsigned (N.v28855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28855 s i)) at 1.
  unfold R.v28855, N.v28855.
  rewrite ?node_28853.
  rewrite ?node_28854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28856 (s : N.State) (i : N.Inputs) :
  R.v28856 (state s) (inputs i) = Zmod.unsigned (N.v28856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28856 s i)) at 1.
  unfold R.v28856, N.v28856.
  unfold R.v16484, N.v16484.
  rewrite ?node_28855.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28857 (s : N.State) (i : N.Inputs) :
  R.v28857 (state s) (inputs i) = Zmod.unsigned (N.v28857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28857 s i)) at 1.
  unfold R.v28857, N.v28857.
  rewrite ?node_28852.
  rewrite ?node_28856.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28858 (s : N.State) (i : N.Inputs) :
  R.v28858 (state s) (inputs i) = Zmod.unsigned (N.v28858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28858 s i)) at 1.
  unfold R.v28858, N.v28858.
  unfold R.v6, N.v6.
  rewrite ?node_28857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28859 (s : N.State) (i : N.Inputs) :
  R.v28859 (state s) (inputs i) = Zmod.unsigned (N.v28859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28859 s i)) at 1.
  unfold R.v28859, N.v28859.
  rewrite ?node_11284.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28860 (s : N.State) (i : N.Inputs) :
  R.v28860 (state s) (inputs i) = Zmod.unsigned (N.v28860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28860 s i)) at 1.
  unfold R.v28860, N.v28860.
  unfold R.v6, N.v6.
  rewrite ?node_11443.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28861 (s : N.State) (i : N.Inputs) :
  R.v28861 (state s) (inputs i) = Zmod.unsigned (N.v28861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28861 s i)) at 1.
  unfold R.v28861, N.v28861.
  rewrite ?node_28859.
  rewrite ?node_28860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28862 (s : N.State) (i : N.Inputs) :
  R.v28862 (state s) (inputs i) = Zmod.unsigned (N.v28862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28862 s i)) at 1.
  unfold R.v28862, N.v28862.
  rewrite ?node_28858.
  rewrite ?node_28861.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28863 (s : N.State) (i : N.Inputs) :
  R.v28863 (state s) (inputs i) = Zmod.unsigned (N.v28863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28863 s i)) at 1.
  unfold R.v28863, N.v28863.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28864 (s : N.State) (i : N.Inputs) :
  R.v28864 (state s) (inputs i) = Zmod.unsigned (N.v28864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28864 s i)) at 1.
  unfold R.v28864, N.v28864.
  rewrite ?node_11288.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28865 (s : N.State) (i : N.Inputs) :
  R.v28865 (state s) (inputs i) = Zmod.unsigned (N.v28865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28865 s i)) at 1.
  unfold R.v28865, N.v28865.
  unfold R.v6, N.v6.
  rewrite !state_r1341_nr_5F1342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1341_nr_5F1342 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28866 (s : N.State) (i : N.Inputs) :
  R.v28866 (state s) (inputs i) = Zmod.unsigned (N.v28866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28866 s i)) at 1.
  unfold R.v28866, N.v28866.
  unfold R.v6, N.v6.
  rewrite ?node_11284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28867 (s : N.State) (i : N.Inputs) :
  R.v28867 (state s) (inputs i) = Zmod.unsigned (N.v28867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28867 s i)) at 1.
  unfold R.v28867, N.v28867.
  rewrite ?node_28865.
  rewrite ?node_28866.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28868 (s : N.State) (i : N.Inputs) :
  R.v28868 (state s) (inputs i) = Zmod.unsigned (N.v28868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28868 s i)) at 1.
  unfold R.v28868, N.v28868.
  unfold R.v16484, N.v16484.
  rewrite ?node_28867.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28869 (s : N.State) (i : N.Inputs) :
  R.v28869 (state s) (inputs i) = Zmod.unsigned (N.v28869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28869 s i)) at 1.
  unfold R.v28869, N.v28869.
  rewrite ?node_28864.
  rewrite ?node_28868.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28870 (s : N.State) (i : N.Inputs) :
  R.v28870 (state s) (inputs i) = Zmod.unsigned (N.v28870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28870 s i)) at 1.
  unfold R.v28870, N.v28870.
  unfold R.v6, N.v6.
  rewrite ?node_28869.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28871 (s : N.State) (i : N.Inputs) :
  R.v28871 (state s) (inputs i) = Zmod.unsigned (N.v28871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28871 s i)) at 1.
  unfold R.v28871, N.v28871.
  rewrite ?node_11289.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28872 (s : N.State) (i : N.Inputs) :
  R.v28872 (state s) (inputs i) = Zmod.unsigned (N.v28872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28872 s i)) at 1.
  unfold R.v28872, N.v28872.
  unfold R.v6, N.v6.
  rewrite ?node_11487.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28873 (s : N.State) (i : N.Inputs) :
  R.v28873 (state s) (inputs i) = Zmod.unsigned (N.v28873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28873 s i)) at 1.
  unfold R.v28873, N.v28873.
  rewrite ?node_28871.
  rewrite ?node_28872.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28874 (s : N.State) (i : N.Inputs) :
  R.v28874 (state s) (inputs i) = Zmod.unsigned (N.v28874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28874 s i)) at 1.
  unfold R.v28874, N.v28874.
  rewrite ?node_28870.
  rewrite ?node_28873.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28875 (s : N.State) (i : N.Inputs) :
  R.v28875 (state s) (inputs i) = Zmod.unsigned (N.v28875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28875 s i)) at 1.
  unfold R.v28875, N.v28875.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28876 (s : N.State) (i : N.Inputs) :
  R.v28876 (state s) (inputs i) = Zmod.unsigned (N.v28876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28876 s i)) at 1.
  unfold R.v28876, N.v28876.
  rewrite ?node_11296.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28877 (s : N.State) (i : N.Inputs) :
  R.v28877 (state s) (inputs i) = Zmod.unsigned (N.v28877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28877 s i)) at 1.
  unfold R.v28877, N.v28877.
  unfold R.v16463, N.v16463.
  rewrite !state_r1345_nr_5F1346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1345_nr_5F1346 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28878 (s : N.State) (i : N.Inputs) :
  R.v28878 (state s) (inputs i) = Zmod.unsigned (N.v28878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28878 s i)) at 1.
  unfold R.v28878, N.v28878.
  unfold R.v16463, N.v16463.
  rewrite !state_r1344_nr_5F1345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1344_nr_5F1345 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28879 (s : N.State) (i : N.Inputs) :
  R.v28879 (state s) (inputs i) = Zmod.unsigned (N.v28879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28879 s i)) at 1.
  unfold R.v28879, N.v28879.
  unfold R.v6, N.v6.
  rewrite !state_r1343_nr_5F1344.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1343_nr_5F1344 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28880 (s : N.State) (i : N.Inputs) :
  R.v28880 (state s) (inputs i) = Zmod.unsigned (N.v28880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28880 s i)) at 1.
  unfold R.v28880, N.v28880.
  unfold R.v6, N.v6.
  rewrite !state_r1342_nr_5F1343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1342_nr_5F1343 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28881 (s : N.State) (i : N.Inputs) :
  R.v28881 (state s) (inputs i) = Zmod.unsigned (N.v28881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28881 s i)) at 1.
  unfold R.v28881, N.v28881.
  rewrite ?node_28879.
  rewrite ?node_28880.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28882 (s : N.State) (i : N.Inputs) :
  R.v28882 (state s) (inputs i) = Zmod.unsigned (N.v28882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28882 s i)) at 1.
  unfold R.v28882, N.v28882.
  unfold R.v16484, N.v16484.
  rewrite ?node_28881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28883 (s : N.State) (i : N.Inputs) :
  R.v28883 (state s) (inputs i) = Zmod.unsigned (N.v28883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28883 s i)) at 1.
  unfold R.v28883, N.v28883.
  rewrite ?node_28876.
  rewrite ?node_28877.
  rewrite ?node_28878.
  rewrite ?node_28882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28884 (s : N.State) (i : N.Inputs) :
  R.v28884 (state s) (inputs i) = Zmod.unsigned (N.v28884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28884 s i)) at 1.
  unfold R.v28884, N.v28884.
  unfold R.v6, N.v6.
  rewrite ?node_28883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28885 (s : N.State) (i : N.Inputs) :
  R.v28885 (state s) (inputs i) = Zmod.unsigned (N.v28885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28885 s i)) at 1.
  unfold R.v28885, N.v28885.
  rewrite ?node_11297.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28886 (s : N.State) (i : N.Inputs) :
  R.v28886 (state s) (inputs i) = Zmod.unsigned (N.v28886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28886 s i)) at 1.
  unfold R.v28886, N.v28886.
  unfold R.v6, N.v6.
  rewrite ?node_11451.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28887 (s : N.State) (i : N.Inputs) :
  R.v28887 (state s) (inputs i) = Zmod.unsigned (N.v28887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28887 s i)) at 1.
  unfold R.v28887, N.v28887.
  unfold R.v6, N.v6.
  rewrite ?node_11491.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28888 (s : N.State) (i : N.Inputs) :
  R.v28888 (state s) (inputs i) = Zmod.unsigned (N.v28888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28888 s i)) at 1.
  unfold R.v28888, N.v28888.
  rewrite ?node_28885.
  rewrite ?node_28886.
  rewrite ?node_28887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28889 (s : N.State) (i : N.Inputs) :
  R.v28889 (state s) (inputs i) = Zmod.unsigned (N.v28889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28889 s i)) at 1.
  unfold R.v28889, N.v28889.
  rewrite ?node_28884.
  rewrite ?node_28888.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28890 (s : N.State) (i : N.Inputs) :
  R.v28890 (state s) (inputs i) = Zmod.unsigned (N.v28890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28890 s i)) at 1.
  unfold R.v28890, N.v28890.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28891 (s : N.State) (i : N.Inputs) :
  R.v28891 (state s) (inputs i) = Zmod.unsigned (N.v28891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28891 s i)) at 1.
  unfold R.v28891, N.v28891.
  unfold R.v16463, N.v16463.
  rewrite !state_r1344_nr_5F1345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1344_nr_5F1345 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28892 (s : N.State) (i : N.Inputs) :
  R.v28892 (state s) (inputs i) = Zmod.unsigned (N.v28892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28892 s i)) at 1.
  unfold R.v28892, N.v28892.
  unfold R.v6, N.v6.
  rewrite !state_r1343_nr_5F1344.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1343_nr_5F1344 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28893 (s : N.State) (i : N.Inputs) :
  R.v28893 (state s) (inputs i) = Zmod.unsigned (N.v28893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28893 s i)) at 1.
  unfold R.v28893, N.v28893.
  unfold R.v6, N.v6.
  rewrite !state_r1342_nr_5F1343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1342_nr_5F1343 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28894 (s : N.State) (i : N.Inputs) :
  R.v28894 (state s) (inputs i) = Zmod.unsigned (N.v28894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28894 s i)) at 1.
  unfold R.v28894, N.v28894.
  rewrite ?node_28892.
  rewrite ?node_28893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28895 (s : N.State) (i : N.Inputs) :
  R.v28895 (state s) (inputs i) = Zmod.unsigned (N.v28895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28895 s i)) at 1.
  unfold R.v28895, N.v28895.
  unfold R.v16484, N.v16484.
  rewrite ?node_28894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28896 (s : N.State) (i : N.Inputs) :
  R.v28896 (state s) (inputs i) = Zmod.unsigned (N.v28896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28896 s i)) at 1.
  unfold R.v28896, N.v28896.
  rewrite ?node_28891.
  rewrite ?node_28895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28897 (s : N.State) (i : N.Inputs) :
  R.v28897 (state s) (inputs i) = Zmod.unsigned (N.v28897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28897 s i)) at 1.
  unfold R.v28897, N.v28897.
  unfold R.v6, N.v6.
  rewrite ?node_28896.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28898 (s : N.State) (i : N.Inputs) :
  R.v28898 (state s) (inputs i) = Zmod.unsigned (N.v28898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28898 s i)) at 1.
  unfold R.v28898, N.v28898.
  rewrite ?node_11292.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28899 (s : N.State) (i : N.Inputs) :
  R.v28899 (state s) (inputs i) = Zmod.unsigned (N.v28899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28899 s i)) at 1.
  unfold R.v28899, N.v28899.
  unfold R.v6, N.v6.
  rewrite ?node_11451.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28900 (s : N.State) (i : N.Inputs) :
  R.v28900 (state s) (inputs i) = Zmod.unsigned (N.v28900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28900 s i)) at 1.
  unfold R.v28900, N.v28900.
  rewrite ?node_28898.
  rewrite ?node_28899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28901 (s : N.State) (i : N.Inputs) :
  R.v28901 (state s) (inputs i) = Zmod.unsigned (N.v28901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28901 s i)) at 1.
  unfold R.v28901, N.v28901.
  rewrite ?node_28897.
  rewrite ?node_28900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28902 (s : N.State) (i : N.Inputs) :
  R.v28902 (state s) (inputs i) = Zmod.unsigned (N.v28902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28902 s i)) at 1.
  unfold R.v28902, N.v28902.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28903 (s : N.State) (i : N.Inputs) :
  R.v28903 (state s) (inputs i) = Zmod.unsigned (N.v28903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28903 s i)) at 1.
  unfold R.v28903, N.v28903.
  rewrite ?node_11296.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28904 (s : N.State) (i : N.Inputs) :
  R.v28904 (state s) (inputs i) = Zmod.unsigned (N.v28904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28904 s i)) at 1.
  unfold R.v28904, N.v28904.
  unfold R.v6, N.v6.
  rewrite !state_r1345_nr_5F1346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1345_nr_5F1346 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28905 (s : N.State) (i : N.Inputs) :
  R.v28905 (state s) (inputs i) = Zmod.unsigned (N.v28905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28905 s i)) at 1.
  unfold R.v28905, N.v28905.
  unfold R.v6, N.v6.
  rewrite ?node_11292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28906 (s : N.State) (i : N.Inputs) :
  R.v28906 (state s) (inputs i) = Zmod.unsigned (N.v28906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28906 s i)) at 1.
  unfold R.v28906, N.v28906.
  rewrite ?node_28904.
  rewrite ?node_28905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28907 (s : N.State) (i : N.Inputs) :
  R.v28907 (state s) (inputs i) = Zmod.unsigned (N.v28907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28907 s i)) at 1.
  unfold R.v28907, N.v28907.
  unfold R.v16484, N.v16484.
  rewrite ?node_28906.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28908 (s : N.State) (i : N.Inputs) :
  R.v28908 (state s) (inputs i) = Zmod.unsigned (N.v28908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28908 s i)) at 1.
  unfold R.v28908, N.v28908.
  rewrite ?node_28903.
  rewrite ?node_28907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28909 (s : N.State) (i : N.Inputs) :
  R.v28909 (state s) (inputs i) = Zmod.unsigned (N.v28909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28909 s i)) at 1.
  unfold R.v28909, N.v28909.
  unfold R.v6, N.v6.
  rewrite ?node_28908.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28910 (s : N.State) (i : N.Inputs) :
  R.v28910 (state s) (inputs i) = Zmod.unsigned (N.v28910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28910 s i)) at 1.
  unfold R.v28910, N.v28910.
  rewrite ?node_11297.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28911 (s : N.State) (i : N.Inputs) :
  R.v28911 (state s) (inputs i) = Zmod.unsigned (N.v28911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28911 s i)) at 1.
  unfold R.v28911, N.v28911.
  unfold R.v6, N.v6.
  rewrite ?node_11491.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28912 (s : N.State) (i : N.Inputs) :
  R.v28912 (state s) (inputs i) = Zmod.unsigned (N.v28912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28912 s i)) at 1.
  unfold R.v28912, N.v28912.
  rewrite ?node_28910.
  rewrite ?node_28911.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28913 (s : N.State) (i : N.Inputs) :
  R.v28913 (state s) (inputs i) = Zmod.unsigned (N.v28913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28913 s i)) at 1.
  unfold R.v28913, N.v28913.
  rewrite ?node_28909.
  rewrite ?node_28912.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28914 (s : N.State) (i : N.Inputs) :
  R.v28914 (state s) (inputs i) = Zmod.unsigned (N.v28914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28914 s i)) at 1.
  unfold R.v28914, N.v28914.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28915 (s : N.State) (i : N.Inputs) :
  R.v28915 (state s) (inputs i) = Zmod.unsigned (N.v28915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28915 s i)) at 1.
  unfold R.v28915, N.v28915.
  unfold R.v16463, N.v16463.
  rewrite !state_r1348_nr_5F1349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1348_nr_5F1349 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28916 (s : N.State) (i : N.Inputs) :
  R.v28916 (state s) (inputs i) = Zmod.unsigned (N.v28916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28916 s i)) at 1.
  unfold R.v28916, N.v28916.
  unfold R.v6, N.v6.
  rewrite !state_r1347_nr_5F1348.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1347_nr_5F1348 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28917 (s : N.State) (i : N.Inputs) :
  R.v28917 (state s) (inputs i) = Zmod.unsigned (N.v28917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28917 s i)) at 1.
  unfold R.v28917, N.v28917.
  unfold R.v6, N.v6.
  rewrite !state_r1346_nr_5F1347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1346_nr_5F1347 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28918 (s : N.State) (i : N.Inputs) :
  R.v28918 (state s) (inputs i) = Zmod.unsigned (N.v28918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28918 s i)) at 1.
  unfold R.v28918, N.v28918.
  rewrite ?node_28916.
  rewrite ?node_28917.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28919 (s : N.State) (i : N.Inputs) :
  R.v28919 (state s) (inputs i) = Zmod.unsigned (N.v28919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28919 s i)) at 1.
  unfold R.v28919, N.v28919.
  unfold R.v16484, N.v16484.
  rewrite ?node_28918.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28920 (s : N.State) (i : N.Inputs) :
  R.v28920 (state s) (inputs i) = Zmod.unsigned (N.v28920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28920 s i)) at 1.
  unfold R.v28920, N.v28920.
  rewrite ?node_28915.
  rewrite ?node_28919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28921 (s : N.State) (i : N.Inputs) :
  R.v28921 (state s) (inputs i) = Zmod.unsigned (N.v28921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28921 s i)) at 1.
  unfold R.v28921, N.v28921.
  unfold R.v6, N.v6.
  rewrite ?node_28920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28922 (s : N.State) (i : N.Inputs) :
  R.v28922 (state s) (inputs i) = Zmod.unsigned (N.v28922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28922 s i)) at 1.
  unfold R.v28922, N.v28922.
  rewrite ?node_11300.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28923 (s : N.State) (i : N.Inputs) :
  R.v28923 (state s) (inputs i) = Zmod.unsigned (N.v28923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28923 s i)) at 1.
  unfold R.v28923, N.v28923.
  unfold R.v6, N.v6.
  rewrite ?node_11495.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28924 (s : N.State) (i : N.Inputs) :
  R.v28924 (state s) (inputs i) = Zmod.unsigned (N.v28924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28924 s i)) at 1.
  unfold R.v28924, N.v28924.
  rewrite ?node_28922.
  rewrite ?node_28923.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28925 (s : N.State) (i : N.Inputs) :
  R.v28925 (state s) (inputs i) = Zmod.unsigned (N.v28925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28925 s i)) at 1.
  unfold R.v28925, N.v28925.
  rewrite ?node_28921.
  rewrite ?node_28924.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28926 (s : N.State) (i : N.Inputs) :
  R.v28926 (state s) (inputs i) = Zmod.unsigned (N.v28926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28926 s i)) at 1.
  unfold R.v28926, N.v28926.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28927 (s : N.State) (i : N.Inputs) :
  R.v28927 (state s) (inputs i) = Zmod.unsigned (N.v28927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28927 s i)) at 1.
  unfold R.v28927, N.v28927.
  rewrite ?node_11401.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28928 (s : N.State) (i : N.Inputs) :
  R.v28928 (state s) (inputs i) = Zmod.unsigned (N.v28928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28928 s i)) at 1.
  unfold R.v28928, N.v28928.
  unfold R.v16463, N.v16463.
  rewrite !state_r1351_nr_5F1353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1351_nr_5F1353 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28929 (s : N.State) (i : N.Inputs) :
  R.v28929 (state s) (inputs i) = Zmod.unsigned (N.v28929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28929 s i)) at 1.
  unfold R.v28929, N.v28929.
  unfold R.v16463, N.v16463.
  rewrite !state_r1350_nr_5F1352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1350_nr_5F1352 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28930 (s : N.State) (i : N.Inputs) :
  R.v28930 (state s) (inputs i) = Zmod.unsigned (N.v28930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28930 s i)) at 1.
  unfold R.v28930, N.v28930.
  unfold R.v6, N.v6.
  rewrite !state_r1349_nr_5F1351.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1349_nr_5F1351 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28931 (s : N.State) (i : N.Inputs) :
  R.v28931 (state s) (inputs i) = Zmod.unsigned (N.v28931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28931 s i)) at 1.
  unfold R.v28931, N.v28931.
  unfold R.v19, N.v19.
  rewrite ?node_28930.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28932 (s : N.State) (i : N.Inputs) :
  R.v28932 (state s) (inputs i) = Zmod.unsigned (N.v28932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28932 s i)) at 1.
  unfold R.v28932, N.v28932.
  unfold R.v16484, N.v16484.
  rewrite ?node_28931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28933 (s : N.State) (i : N.Inputs) :
  R.v28933 (state s) (inputs i) = Zmod.unsigned (N.v28933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28933 s i)) at 1.
  unfold R.v28933, N.v28933.
  rewrite ?node_28927.
  rewrite ?node_28928.
  rewrite ?node_28929.
  rewrite ?node_28932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28934 (s : N.State) (i : N.Inputs) :
  R.v28934 (state s) (inputs i) = Zmod.unsigned (N.v28934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28934 s i)) at 1.
  unfold R.v28934, N.v28934.
  unfold R.v6, N.v6.
  rewrite ?node_28933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28935 (s : N.State) (i : N.Inputs) :
  R.v28935 (state s) (inputs i) = Zmod.unsigned (N.v28935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28935 s i)) at 1.
  unfold R.v28935, N.v28935.
  rewrite ?node_11402.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28936 (s : N.State) (i : N.Inputs) :
  R.v28936 (state s) (inputs i) = Zmod.unsigned (N.v28936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28936 s i)) at 1.
  unfold R.v28936, N.v28936.
  unfold R.v6, N.v6.
  rewrite ?node_11551.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28937 (s : N.State) (i : N.Inputs) :
  R.v28937 (state s) (inputs i) = Zmod.unsigned (N.v28937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28937 s i)) at 1.
  unfold R.v28937, N.v28937.
  unfold R.v6, N.v6.
  rewrite ?node_11613.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28938 (s : N.State) (i : N.Inputs) :
  R.v28938 (state s) (inputs i) = Zmod.unsigned (N.v28938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28938 s i)) at 1.
  unfold R.v28938, N.v28938.
  rewrite ?node_28935.
  rewrite ?node_28936.
  rewrite ?node_28937.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28939 (s : N.State) (i : N.Inputs) :
  R.v28939 (state s) (inputs i) = Zmod.unsigned (N.v28939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28939 s i)) at 1.
  unfold R.v28939, N.v28939.
  rewrite ?node_28934.
  rewrite ?node_28938.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28940 (s : N.State) (i : N.Inputs) :
  R.v28940 (state s) (inputs i) = Zmod.unsigned (N.v28940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28940 s i)) at 1.
  unfold R.v28940, N.v28940.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28941 (s : N.State) (i : N.Inputs) :
  R.v28941 (state s) (inputs i) = Zmod.unsigned (N.v28941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28941 s i)) at 1.
  unfold R.v28941, N.v28941.
  unfold R.v16463, N.v16463.
  rewrite !state_r1350_nr_5F1352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1350_nr_5F1352 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28942 (s : N.State) (i : N.Inputs) :
  R.v28942 (state s) (inputs i) = Zmod.unsigned (N.v28942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28942 s i)) at 1.
  unfold R.v28942, N.v28942.
  unfold R.v6, N.v6.
  rewrite !state_r1349_nr_5F1351.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1349_nr_5F1351 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28943 (s : N.State) (i : N.Inputs) :
  R.v28943 (state s) (inputs i) = Zmod.unsigned (N.v28943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28943 s i)) at 1.
  unfold R.v28943, N.v28943.
  unfold R.v19, N.v19.
  rewrite ?node_28942.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28944 (s : N.State) (i : N.Inputs) :
  R.v28944 (state s) (inputs i) = Zmod.unsigned (N.v28944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28944 s i)) at 1.
  unfold R.v28944, N.v28944.
  unfold R.v16484, N.v16484.
  rewrite ?node_28943.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28945 (s : N.State) (i : N.Inputs) :
  R.v28945 (state s) (inputs i) = Zmod.unsigned (N.v28945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28945 s i)) at 1.
  unfold R.v28945, N.v28945.
  rewrite ?node_28941.
  rewrite ?node_28944.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28946 (s : N.State) (i : N.Inputs) :
  R.v28946 (state s) (inputs i) = Zmod.unsigned (N.v28946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28946 s i)) at 1.
  unfold R.v28946, N.v28946.
  unfold R.v6, N.v6.
  rewrite ?node_28945.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28947 (s : N.State) (i : N.Inputs) :
  R.v28947 (state s) (inputs i) = Zmod.unsigned (N.v28947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28947 s i)) at 1.
  unfold R.v28947, N.v28947.
  rewrite ?node_11397.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28948 (s : N.State) (i : N.Inputs) :
  R.v28948 (state s) (inputs i) = Zmod.unsigned (N.v28948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28948 s i)) at 1.
  unfold R.v28948, N.v28948.
  unfold R.v6, N.v6.
  rewrite ?node_11551.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28949 (s : N.State) (i : N.Inputs) :
  R.v28949 (state s) (inputs i) = Zmod.unsigned (N.v28949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28949 s i)) at 1.
  unfold R.v28949, N.v28949.
  rewrite ?node_28947.
  rewrite ?node_28948.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28950 (s : N.State) (i : N.Inputs) :
  R.v28950 (state s) (inputs i) = Zmod.unsigned (N.v28950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28950 s i)) at 1.
  unfold R.v28950, N.v28950.
  rewrite ?node_28946.
  rewrite ?node_28949.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28951 (s : N.State) (i : N.Inputs) :
  R.v28951 (state s) (inputs i) = Zmod.unsigned (N.v28951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28951 s i)) at 1.
  unfold R.v28951, N.v28951.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28952 (s : N.State) (i : N.Inputs) :
  R.v28952 (state s) (inputs i) = Zmod.unsigned (N.v28952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28952 s i)) at 1.
  unfold R.v28952, N.v28952.
  rewrite ?node_11401.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28953 (s : N.State) (i : N.Inputs) :
  R.v28953 (state s) (inputs i) = Zmod.unsigned (N.v28953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28953 s i)) at 1.
  unfold R.v28953, N.v28953.
  unfold R.v6, N.v6.
  rewrite !state_r1351_nr_5F1353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1351_nr_5F1353 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28954 (s : N.State) (i : N.Inputs) :
  R.v28954 (state s) (inputs i) = Zmod.unsigned (N.v28954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28954 s i)) at 1.
  unfold R.v28954, N.v28954.
  unfold R.v6, N.v6.
  rewrite ?node_11397.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28955 (s : N.State) (i : N.Inputs) :
  R.v28955 (state s) (inputs i) = Zmod.unsigned (N.v28955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28955 s i)) at 1.
  unfold R.v28955, N.v28955.
  rewrite ?node_28953.
  rewrite ?node_28954.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28956 (s : N.State) (i : N.Inputs) :
  R.v28956 (state s) (inputs i) = Zmod.unsigned (N.v28956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28956 s i)) at 1.
  unfold R.v28956, N.v28956.
  unfold R.v16484, N.v16484.
  rewrite ?node_28955.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28957 (s : N.State) (i : N.Inputs) :
  R.v28957 (state s) (inputs i) = Zmod.unsigned (N.v28957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28957 s i)) at 1.
  unfold R.v28957, N.v28957.
  rewrite ?node_28952.
  rewrite ?node_28956.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28958 (s : N.State) (i : N.Inputs) :
  R.v28958 (state s) (inputs i) = Zmod.unsigned (N.v28958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28958 s i)) at 1.
  unfold R.v28958, N.v28958.
  unfold R.v6, N.v6.
  rewrite ?node_28957.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28959 (s : N.State) (i : N.Inputs) :
  R.v28959 (state s) (inputs i) = Zmod.unsigned (N.v28959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28959 s i)) at 1.
  unfold R.v28959, N.v28959.
  rewrite ?node_11402.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28960 (s : N.State) (i : N.Inputs) :
  R.v28960 (state s) (inputs i) = Zmod.unsigned (N.v28960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28960 s i)) at 1.
  unfold R.v28960, N.v28960.
  unfold R.v6, N.v6.
  rewrite ?node_11613.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28961 (s : N.State) (i : N.Inputs) :
  R.v28961 (state s) (inputs i) = Zmod.unsigned (N.v28961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28961 s i)) at 1.
  unfold R.v28961, N.v28961.
  rewrite ?node_28959.
  rewrite ?node_28960.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28962 (s : N.State) (i : N.Inputs) :
  R.v28962 (state s) (inputs i) = Zmod.unsigned (N.v28962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28962 s i)) at 1.
  unfold R.v28962, N.v28962.
  rewrite ?node_28958.
  rewrite ?node_28961.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28963 (s : N.State) (i : N.Inputs) :
  R.v28963 (state s) (inputs i) = Zmod.unsigned (N.v28963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28963 s i)) at 1.
  unfold R.v28963, N.v28963.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28964 (s : N.State) (i : N.Inputs) :
  R.v28964 (state s) (inputs i) = Zmod.unsigned (N.v28964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28964 s i)) at 1.
  unfold R.v28964, N.v28964.
  rewrite ?node_11408.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28965 (s : N.State) (i : N.Inputs) :
  R.v28965 (state s) (inputs i) = Zmod.unsigned (N.v28965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28965 s i)) at 1.
  unfold R.v28965, N.v28965.
  unfold R.v16463, N.v16463.
  rewrite !state_r1355_nr_5F1357.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1355_nr_5F1357 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28966 (s : N.State) (i : N.Inputs) :
  R.v28966 (state s) (inputs i) = Zmod.unsigned (N.v28966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28966 s i)) at 1.
  unfold R.v28966, N.v28966.
  unfold R.v16463, N.v16463.
  rewrite !state_r1354_nr_5F1356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1354_nr_5F1356 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28967 (s : N.State) (i : N.Inputs) :
  R.v28967 (state s) (inputs i) = Zmod.unsigned (N.v28967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28967 s i)) at 1.
  unfold R.v28967, N.v28967.
  unfold R.v6, N.v6.
  rewrite !state_r1353_nr_5F1355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1353_nr_5F1355 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28968 (s : N.State) (i : N.Inputs) :
  R.v28968 (state s) (inputs i) = Zmod.unsigned (N.v28968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28968 s i)) at 1.
  unfold R.v28968, N.v28968.
  unfold R.v6, N.v6.
  rewrite !state_r1352_nr_5F1354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1352_nr_5F1354 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28969 (s : N.State) (i : N.Inputs) :
  R.v28969 (state s) (inputs i) = Zmod.unsigned (N.v28969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28969 s i)) at 1.
  unfold R.v28969, N.v28969.
  rewrite ?node_28967.
  rewrite ?node_28968.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28970 (s : N.State) (i : N.Inputs) :
  R.v28970 (state s) (inputs i) = Zmod.unsigned (N.v28970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28970 s i)) at 1.
  unfold R.v28970, N.v28970.
  unfold R.v16484, N.v16484.
  rewrite ?node_28969.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28971 (s : N.State) (i : N.Inputs) :
  R.v28971 (state s) (inputs i) = Zmod.unsigned (N.v28971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28971 s i)) at 1.
  unfold R.v28971, N.v28971.
  rewrite ?node_28964.
  rewrite ?node_28965.
  rewrite ?node_28966.
  rewrite ?node_28970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28972 (s : N.State) (i : N.Inputs) :
  R.v28972 (state s) (inputs i) = Zmod.unsigned (N.v28972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28972 s i)) at 1.
  unfold R.v28972, N.v28972.
  unfold R.v6, N.v6.
  rewrite ?node_28971.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28973 (s : N.State) (i : N.Inputs) :
  R.v28973 (state s) (inputs i) = Zmod.unsigned (N.v28973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28973 s i)) at 1.
  unfold R.v28973, N.v28973.
  rewrite ?node_11409.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28974 (s : N.State) (i : N.Inputs) :
  R.v28974 (state s) (inputs i) = Zmod.unsigned (N.v28974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28974 s i)) at 1.
  unfold R.v28974, N.v28974.
  unfold R.v6, N.v6.
  rewrite ?node_11558.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28975 (s : N.State) (i : N.Inputs) :
  R.v28975 (state s) (inputs i) = Zmod.unsigned (N.v28975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28975 s i)) at 1.
  unfold R.v28975, N.v28975.
  unfold R.v6, N.v6.
  rewrite ?node_11616.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28976 (s : N.State) (i : N.Inputs) :
  R.v28976 (state s) (inputs i) = Zmod.unsigned (N.v28976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28976 s i)) at 1.
  unfold R.v28976, N.v28976.
  rewrite ?node_28973.
  rewrite ?node_28974.
  rewrite ?node_28975.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28977 (s : N.State) (i : N.Inputs) :
  R.v28977 (state s) (inputs i) = Zmod.unsigned (N.v28977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28977 s i)) at 1.
  unfold R.v28977, N.v28977.
  rewrite ?node_28972.
  rewrite ?node_28976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28978 (s : N.State) (i : N.Inputs) :
  R.v28978 (state s) (inputs i) = Zmod.unsigned (N.v28978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28978 s i)) at 1.
  unfold R.v28978, N.v28978.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28979 (s : N.State) (i : N.Inputs) :
  R.v28979 (state s) (inputs i) = Zmod.unsigned (N.v28979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28979 s i)) at 1.
  unfold R.v28979, N.v28979.
  unfold R.v16463, N.v16463.
  rewrite !state_r1354_nr_5F1356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1354_nr_5F1356 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28980 (s : N.State) (i : N.Inputs) :
  R.v28980 (state s) (inputs i) = Zmod.unsigned (N.v28980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28980 s i)) at 1.
  unfold R.v28980, N.v28980.
  unfold R.v6, N.v6.
  rewrite !state_r1353_nr_5F1355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1353_nr_5F1355 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28981 (s : N.State) (i : N.Inputs) :
  R.v28981 (state s) (inputs i) = Zmod.unsigned (N.v28981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28981 s i)) at 1.
  unfold R.v28981, N.v28981.
  unfold R.v6, N.v6.
  rewrite !state_r1352_nr_5F1354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1352_nr_5F1354 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28982 (s : N.State) (i : N.Inputs) :
  R.v28982 (state s) (inputs i) = Zmod.unsigned (N.v28982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28982 s i)) at 1.
  unfold R.v28982, N.v28982.
  rewrite ?node_28980.
  rewrite ?node_28981.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28983 (s : N.State) (i : N.Inputs) :
  R.v28983 (state s) (inputs i) = Zmod.unsigned (N.v28983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28983 s i)) at 1.
  unfold R.v28983, N.v28983.
  unfold R.v16484, N.v16484.
  rewrite ?node_28982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28984 (s : N.State) (i : N.Inputs) :
  R.v28984 (state s) (inputs i) = Zmod.unsigned (N.v28984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28984 s i)) at 1.
  unfold R.v28984, N.v28984.
  rewrite ?node_28979.
  rewrite ?node_28983.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28985 (s : N.State) (i : N.Inputs) :
  R.v28985 (state s) (inputs i) = Zmod.unsigned (N.v28985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28985 s i)) at 1.
  unfold R.v28985, N.v28985.
  unfold R.v6, N.v6.
  rewrite ?node_28984.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28986 (s : N.State) (i : N.Inputs) :
  R.v28986 (state s) (inputs i) = Zmod.unsigned (N.v28986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28986 s i)) at 1.
  unfold R.v28986, N.v28986.
  rewrite ?node_11404.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28987 (s : N.State) (i : N.Inputs) :
  R.v28987 (state s) (inputs i) = Zmod.unsigned (N.v28987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28987 s i)) at 1.
  unfold R.v28987, N.v28987.
  unfold R.v6, N.v6.
  rewrite ?node_11558.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28988 (s : N.State) (i : N.Inputs) :
  R.v28988 (state s) (inputs i) = Zmod.unsigned (N.v28988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28988 s i)) at 1.
  unfold R.v28988, N.v28988.
  rewrite ?node_28986.
  rewrite ?node_28987.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28989 (s : N.State) (i : N.Inputs) :
  R.v28989 (state s) (inputs i) = Zmod.unsigned (N.v28989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28989 s i)) at 1.
  unfold R.v28989, N.v28989.
  rewrite ?node_28985.
  rewrite ?node_28988.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28990 (s : N.State) (i : N.Inputs) :
  R.v28990 (state s) (inputs i) = Zmod.unsigned (N.v28990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28990 s i)) at 1.
  unfold R.v28990, N.v28990.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28991 (s : N.State) (i : N.Inputs) :
  R.v28991 (state s) (inputs i) = Zmod.unsigned (N.v28991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28991 s i)) at 1.
  unfold R.v28991, N.v28991.
  rewrite ?node_11408.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28992 (s : N.State) (i : N.Inputs) :
  R.v28992 (state s) (inputs i) = Zmod.unsigned (N.v28992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28992 s i)) at 1.
  unfold R.v28992, N.v28992.
  unfold R.v6, N.v6.
  rewrite !state_r1355_nr_5F1357.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1355_nr_5F1357 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28993 (s : N.State) (i : N.Inputs) :
  R.v28993 (state s) (inputs i) = Zmod.unsigned (N.v28993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28993 s i)) at 1.
  unfold R.v28993, N.v28993.
  unfold R.v6, N.v6.
  rewrite ?node_11404.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28994 (s : N.State) (i : N.Inputs) :
  R.v28994 (state s) (inputs i) = Zmod.unsigned (N.v28994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28994 s i)) at 1.
  unfold R.v28994, N.v28994.
  rewrite ?node_28992.
  rewrite ?node_28993.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28995 (s : N.State) (i : N.Inputs) :
  R.v28995 (state s) (inputs i) = Zmod.unsigned (N.v28995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28995 s i)) at 1.
  unfold R.v28995, N.v28995.
  unfold R.v16484, N.v16484.
  rewrite ?node_28994.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28996 (s : N.State) (i : N.Inputs) :
  R.v28996 (state s) (inputs i) = Zmod.unsigned (N.v28996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28996 s i)) at 1.
  unfold R.v28996, N.v28996.
  rewrite ?node_28991.
  rewrite ?node_28995.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28997 (s : N.State) (i : N.Inputs) :
  R.v28997 (state s) (inputs i) = Zmod.unsigned (N.v28997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28997 s i)) at 1.
  unfold R.v28997, N.v28997.
  unfold R.v6, N.v6.
  rewrite ?node_28996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28998 (s : N.State) (i : N.Inputs) :
  R.v28998 (state s) (inputs i) = Zmod.unsigned (N.v28998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28998 s i)) at 1.
  unfold R.v28998, N.v28998.
  rewrite ?node_11409.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28999 (s : N.State) (i : N.Inputs) :
  R.v28999 (state s) (inputs i) = Zmod.unsigned (N.v28999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28999 s i)) at 1.
  unfold R.v28999, N.v28999.
  unfold R.v6, N.v6.
  rewrite ?node_11616.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
