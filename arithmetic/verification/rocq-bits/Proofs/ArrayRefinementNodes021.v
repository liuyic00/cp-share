(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes020.
Lemma node_21000 (s : N.State) (i : N.Inputs) :
  R.v21000 (state s) (inputs i) = Zmod.unsigned (N.v21000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21000 s i)) at 1.
  unfold R.v21000, N.v21000.
  rewrite ?node_20998.
  rewrite ?node_20999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21001 (s : N.State) (i : N.Inputs) :
  R.v21001 (state s) (inputs i) = Zmod.unsigned (N.v21001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21001 s i)) at 1.
  unfold R.v21001, N.v21001.
  rewrite ?node_20997.
  rewrite ?node_21000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21002 (s : N.State) (i : N.Inputs) :
  R.v21002 (state s) (inputs i) = Zmod.unsigned (N.v21002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21002 s i)) at 1.
  unfold R.v21002, N.v21002.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21003 (s : N.State) (i : N.Inputs) :
  R.v21003 (state s) (inputs i) = Zmod.unsigned (N.v21003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21003 s i)) at 1.
  unfold R.v21003, N.v21003.
  rewrite ?node_7385.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21004 (s : N.State) (i : N.Inputs) :
  R.v21004 (state s) (inputs i) = Zmod.unsigned (N.v21004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21004 s i)) at 1.
  unfold R.v21004, N.v21004.
  unfold R.v16463, N.v16463.
  rewrite !state_r511_nr_5F511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r511_nr_5F511 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21005 (s : N.State) (i : N.Inputs) :
  R.v21005 (state s) (inputs i) = Zmod.unsigned (N.v21005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21005 s i)) at 1.
  unfold R.v21005, N.v21005.
  unfold R.v16463, N.v16463.
  rewrite !state_r510_nr_5F510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r510_nr_5F510 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21006 (s : N.State) (i : N.Inputs) :
  R.v21006 (state s) (inputs i) = Zmod.unsigned (N.v21006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21006 s i)) at 1.
  unfold R.v21006, N.v21006.
  unfold R.v6, N.v6.
  rewrite !state_r509_nr_5F509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r509_nr_5F509 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21007 (s : N.State) (i : N.Inputs) :
  R.v21007 (state s) (inputs i) = Zmod.unsigned (N.v21007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21007 s i)) at 1.
  unfold R.v21007, N.v21007.
  unfold R.v6, N.v6.
  rewrite !state_r508_nr_5F508.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r508_nr_5F508 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21008 (s : N.State) (i : N.Inputs) :
  R.v21008 (state s) (inputs i) = Zmod.unsigned (N.v21008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21008 s i)) at 1.
  unfold R.v21008, N.v21008.
  rewrite ?node_21006.
  rewrite ?node_21007.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21009 (s : N.State) (i : N.Inputs) :
  R.v21009 (state s) (inputs i) = Zmod.unsigned (N.v21009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21009 s i)) at 1.
  unfold R.v21009, N.v21009.
  unfold R.v16484, N.v16484.
  rewrite ?node_21008.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21010 (s : N.State) (i : N.Inputs) :
  R.v21010 (state s) (inputs i) = Zmod.unsigned (N.v21010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21010 s i)) at 1.
  unfold R.v21010, N.v21010.
  rewrite ?node_21003.
  rewrite ?node_21004.
  rewrite ?node_21005.
  rewrite ?node_21009.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21011 (s : N.State) (i : N.Inputs) :
  R.v21011 (state s) (inputs i) = Zmod.unsigned (N.v21011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21011 s i)) at 1.
  unfold R.v21011, N.v21011.
  unfold R.v6, N.v6.
  rewrite ?node_21010.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21012 (s : N.State) (i : N.Inputs) :
  R.v21012 (state s) (inputs i) = Zmod.unsigned (N.v21012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21012 s i)) at 1.
  unfold R.v21012, N.v21012.
  rewrite ?node_7386.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21013 (s : N.State) (i : N.Inputs) :
  R.v21013 (state s) (inputs i) = Zmod.unsigned (N.v21013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21013 s i)) at 1.
  unfold R.v21013, N.v21013.
  unfold R.v6, N.v6.
  rewrite ?node_7492.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21014 (s : N.State) (i : N.Inputs) :
  R.v21014 (state s) (inputs i) = Zmod.unsigned (N.v21014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21014 s i)) at 1.
  unfold R.v21014, N.v21014.
  unfold R.v6, N.v6.
  rewrite ?node_7531.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21015 (s : N.State) (i : N.Inputs) :
  R.v21015 (state s) (inputs i) = Zmod.unsigned (N.v21015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21015 s i)) at 1.
  unfold R.v21015, N.v21015.
  rewrite ?node_21012.
  rewrite ?node_21013.
  rewrite ?node_21014.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21016 (s : N.State) (i : N.Inputs) :
  R.v21016 (state s) (inputs i) = Zmod.unsigned (N.v21016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21016 s i)) at 1.
  unfold R.v21016, N.v21016.
  rewrite ?node_21011.
  rewrite ?node_21015.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21017 (s : N.State) (i : N.Inputs) :
  R.v21017 (state s) (inputs i) = Zmod.unsigned (N.v21017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21017 s i)) at 1.
  unfold R.v21017, N.v21017.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21018 (s : N.State) (i : N.Inputs) :
  R.v21018 (state s) (inputs i) = Zmod.unsigned (N.v21018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21018 s i)) at 1.
  unfold R.v21018, N.v21018.
  unfold R.v16463, N.v16463.
  rewrite !state_r510_nr_5F510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r510_nr_5F510 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21019 (s : N.State) (i : N.Inputs) :
  R.v21019 (state s) (inputs i) = Zmod.unsigned (N.v21019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21019 s i)) at 1.
  unfold R.v21019, N.v21019.
  unfold R.v6, N.v6.
  rewrite !state_r509_nr_5F509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r509_nr_5F509 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21020 (s : N.State) (i : N.Inputs) :
  R.v21020 (state s) (inputs i) = Zmod.unsigned (N.v21020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21020 s i)) at 1.
  unfold R.v21020, N.v21020.
  unfold R.v6, N.v6.
  rewrite !state_r508_nr_5F508.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r508_nr_5F508 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21021 (s : N.State) (i : N.Inputs) :
  R.v21021 (state s) (inputs i) = Zmod.unsigned (N.v21021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21021 s i)) at 1.
  unfold R.v21021, N.v21021.
  rewrite ?node_21019.
  rewrite ?node_21020.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21022 (s : N.State) (i : N.Inputs) :
  R.v21022 (state s) (inputs i) = Zmod.unsigned (N.v21022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21022 s i)) at 1.
  unfold R.v21022, N.v21022.
  unfold R.v16484, N.v16484.
  rewrite ?node_21021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21023 (s : N.State) (i : N.Inputs) :
  R.v21023 (state s) (inputs i) = Zmod.unsigned (N.v21023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21023 s i)) at 1.
  unfold R.v21023, N.v21023.
  rewrite ?node_21018.
  rewrite ?node_21022.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21024 (s : N.State) (i : N.Inputs) :
  R.v21024 (state s) (inputs i) = Zmod.unsigned (N.v21024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21024 s i)) at 1.
  unfold R.v21024, N.v21024.
  unfold R.v6, N.v6.
  rewrite ?node_21023.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21025 (s : N.State) (i : N.Inputs) :
  R.v21025 (state s) (inputs i) = Zmod.unsigned (N.v21025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21025 s i)) at 1.
  unfold R.v21025, N.v21025.
  rewrite ?node_7381.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21026 (s : N.State) (i : N.Inputs) :
  R.v21026 (state s) (inputs i) = Zmod.unsigned (N.v21026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21026 s i)) at 1.
  unfold R.v21026, N.v21026.
  unfold R.v6, N.v6.
  rewrite ?node_7492.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21027 (s : N.State) (i : N.Inputs) :
  R.v21027 (state s) (inputs i) = Zmod.unsigned (N.v21027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21027 s i)) at 1.
  unfold R.v21027, N.v21027.
  rewrite ?node_21025.
  rewrite ?node_21026.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21028 (s : N.State) (i : N.Inputs) :
  R.v21028 (state s) (inputs i) = Zmod.unsigned (N.v21028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21028 s i)) at 1.
  unfold R.v21028, N.v21028.
  rewrite ?node_21024.
  rewrite ?node_21027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21029 (s : N.State) (i : N.Inputs) :
  R.v21029 (state s) (inputs i) = Zmod.unsigned (N.v21029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21029 s i)) at 1.
  unfold R.v21029, N.v21029.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21030 (s : N.State) (i : N.Inputs) :
  R.v21030 (state s) (inputs i) = Zmod.unsigned (N.v21030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21030 s i)) at 1.
  unfold R.v21030, N.v21030.
  rewrite ?node_7385.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21031 (s : N.State) (i : N.Inputs) :
  R.v21031 (state s) (inputs i) = Zmod.unsigned (N.v21031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21031 s i)) at 1.
  unfold R.v21031, N.v21031.
  unfold R.v6, N.v6.
  rewrite !state_r511_nr_5F511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r511_nr_5F511 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21032 (s : N.State) (i : N.Inputs) :
  R.v21032 (state s) (inputs i) = Zmod.unsigned (N.v21032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21032 s i)) at 1.
  unfold R.v21032, N.v21032.
  unfold R.v6, N.v6.
  rewrite ?node_7381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21033 (s : N.State) (i : N.Inputs) :
  R.v21033 (state s) (inputs i) = Zmod.unsigned (N.v21033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21033 s i)) at 1.
  unfold R.v21033, N.v21033.
  rewrite ?node_21031.
  rewrite ?node_21032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21034 (s : N.State) (i : N.Inputs) :
  R.v21034 (state s) (inputs i) = Zmod.unsigned (N.v21034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21034 s i)) at 1.
  unfold R.v21034, N.v21034.
  unfold R.v16484, N.v16484.
  rewrite ?node_21033.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21035 (s : N.State) (i : N.Inputs) :
  R.v21035 (state s) (inputs i) = Zmod.unsigned (N.v21035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21035 s i)) at 1.
  unfold R.v21035, N.v21035.
  rewrite ?node_21030.
  rewrite ?node_21034.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21036 (s : N.State) (i : N.Inputs) :
  R.v21036 (state s) (inputs i) = Zmod.unsigned (N.v21036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21036 s i)) at 1.
  unfold R.v21036, N.v21036.
  unfold R.v6, N.v6.
  rewrite ?node_21035.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21037 (s : N.State) (i : N.Inputs) :
  R.v21037 (state s) (inputs i) = Zmod.unsigned (N.v21037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21037 s i)) at 1.
  unfold R.v21037, N.v21037.
  rewrite ?node_7386.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21038 (s : N.State) (i : N.Inputs) :
  R.v21038 (state s) (inputs i) = Zmod.unsigned (N.v21038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21038 s i)) at 1.
  unfold R.v21038, N.v21038.
  unfold R.v6, N.v6.
  rewrite ?node_7531.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21039 (s : N.State) (i : N.Inputs) :
  R.v21039 (state s) (inputs i) = Zmod.unsigned (N.v21039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21039 s i)) at 1.
  unfold R.v21039, N.v21039.
  rewrite ?node_21037.
  rewrite ?node_21038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21040 (s : N.State) (i : N.Inputs) :
  R.v21040 (state s) (inputs i) = Zmod.unsigned (N.v21040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21040 s i)) at 1.
  unfold R.v21040, N.v21040.
  rewrite ?node_21036.
  rewrite ?node_21039.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21041 (s : N.State) (i : N.Inputs) :
  R.v21041 (state s) (inputs i) = Zmod.unsigned (N.v21041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21041 s i)) at 1.
  unfold R.v21041, N.v21041.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21042 (s : N.State) (i : N.Inputs) :
  R.v21042 (state s) (inputs i) = Zmod.unsigned (N.v21042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21042 s i)) at 1.
  unfold R.v21042, N.v21042.
  rewrite ?node_7393.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21043 (s : N.State) (i : N.Inputs) :
  R.v21043 (state s) (inputs i) = Zmod.unsigned (N.v21043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21043 s i)) at 1.
  unfold R.v21043, N.v21043.
  unfold R.v16463, N.v16463.
  rewrite !state_r515_nr_5F515.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r515_nr_5F515 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21044 (s : N.State) (i : N.Inputs) :
  R.v21044 (state s) (inputs i) = Zmod.unsigned (N.v21044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21044 s i)) at 1.
  unfold R.v21044, N.v21044.
  unfold R.v16463, N.v16463.
  rewrite !state_r514_nr_5F514.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r514_nr_5F514 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21045 (s : N.State) (i : N.Inputs) :
  R.v21045 (state s) (inputs i) = Zmod.unsigned (N.v21045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21045 s i)) at 1.
  unfold R.v21045, N.v21045.
  unfold R.v6, N.v6.
  rewrite !state_r513_nr_5F513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r513_nr_5F513 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21046 (s : N.State) (i : N.Inputs) :
  R.v21046 (state s) (inputs i) = Zmod.unsigned (N.v21046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21046 s i)) at 1.
  unfold R.v21046, N.v21046.
  unfold R.v6, N.v6.
  rewrite !state_r512_nr_5F512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r512_nr_5F512 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21047 (s : N.State) (i : N.Inputs) :
  R.v21047 (state s) (inputs i) = Zmod.unsigned (N.v21047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21047 s i)) at 1.
  unfold R.v21047, N.v21047.
  rewrite ?node_21045.
  rewrite ?node_21046.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21048 (s : N.State) (i : N.Inputs) :
  R.v21048 (state s) (inputs i) = Zmod.unsigned (N.v21048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21048 s i)) at 1.
  unfold R.v21048, N.v21048.
  unfold R.v16484, N.v16484.
  rewrite ?node_21047.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21049 (s : N.State) (i : N.Inputs) :
  R.v21049 (state s) (inputs i) = Zmod.unsigned (N.v21049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21049 s i)) at 1.
  unfold R.v21049, N.v21049.
  rewrite ?node_21042.
  rewrite ?node_21043.
  rewrite ?node_21044.
  rewrite ?node_21048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21050 (s : N.State) (i : N.Inputs) :
  R.v21050 (state s) (inputs i) = Zmod.unsigned (N.v21050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21050 s i)) at 1.
  unfold R.v21050, N.v21050.
  unfold R.v6, N.v6.
  rewrite ?node_21049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21051 (s : N.State) (i : N.Inputs) :
  R.v21051 (state s) (inputs i) = Zmod.unsigned (N.v21051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21051 s i)) at 1.
  unfold R.v21051, N.v21051.
  rewrite ?node_7394.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21052 (s : N.State) (i : N.Inputs) :
  R.v21052 (state s) (inputs i) = Zmod.unsigned (N.v21052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21052 s i)) at 1.
  unfold R.v21052, N.v21052.
  unfold R.v6, N.v6.
  rewrite ?node_7500.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21053 (s : N.State) (i : N.Inputs) :
  R.v21053 (state s) (inputs i) = Zmod.unsigned (N.v21053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21053 s i)) at 1.
  unfold R.v21053, N.v21053.
  unfold R.v6, N.v6.
  rewrite ?node_7540.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21054 (s : N.State) (i : N.Inputs) :
  R.v21054 (state s) (inputs i) = Zmod.unsigned (N.v21054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21054 s i)) at 1.
  unfold R.v21054, N.v21054.
  rewrite ?node_21051.
  rewrite ?node_21052.
  rewrite ?node_21053.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21055 (s : N.State) (i : N.Inputs) :
  R.v21055 (state s) (inputs i) = Zmod.unsigned (N.v21055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21055 s i)) at 1.
  unfold R.v21055, N.v21055.
  rewrite ?node_21050.
  rewrite ?node_21054.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21056 (s : N.State) (i : N.Inputs) :
  R.v21056 (state s) (inputs i) = Zmod.unsigned (N.v21056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21056 s i)) at 1.
  unfold R.v21056, N.v21056.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21057 (s : N.State) (i : N.Inputs) :
  R.v21057 (state s) (inputs i) = Zmod.unsigned (N.v21057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21057 s i)) at 1.
  unfold R.v21057, N.v21057.
  unfold R.v16463, N.v16463.
  rewrite !state_r514_nr_5F514.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r514_nr_5F514 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21058 (s : N.State) (i : N.Inputs) :
  R.v21058 (state s) (inputs i) = Zmod.unsigned (N.v21058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21058 s i)) at 1.
  unfold R.v21058, N.v21058.
  unfold R.v6, N.v6.
  rewrite !state_r513_nr_5F513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r513_nr_5F513 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21059 (s : N.State) (i : N.Inputs) :
  R.v21059 (state s) (inputs i) = Zmod.unsigned (N.v21059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21059 s i)) at 1.
  unfold R.v21059, N.v21059.
  unfold R.v6, N.v6.
  rewrite !state_r512_nr_5F512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r512_nr_5F512 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21060 (s : N.State) (i : N.Inputs) :
  R.v21060 (state s) (inputs i) = Zmod.unsigned (N.v21060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21060 s i)) at 1.
  unfold R.v21060, N.v21060.
  rewrite ?node_21058.
  rewrite ?node_21059.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21061 (s : N.State) (i : N.Inputs) :
  R.v21061 (state s) (inputs i) = Zmod.unsigned (N.v21061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21061 s i)) at 1.
  unfold R.v21061, N.v21061.
  unfold R.v16484, N.v16484.
  rewrite ?node_21060.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21062 (s : N.State) (i : N.Inputs) :
  R.v21062 (state s) (inputs i) = Zmod.unsigned (N.v21062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21062 s i)) at 1.
  unfold R.v21062, N.v21062.
  rewrite ?node_21057.
  rewrite ?node_21061.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21063 (s : N.State) (i : N.Inputs) :
  R.v21063 (state s) (inputs i) = Zmod.unsigned (N.v21063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21063 s i)) at 1.
  unfold R.v21063, N.v21063.
  unfold R.v6, N.v6.
  rewrite ?node_21062.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21064 (s : N.State) (i : N.Inputs) :
  R.v21064 (state s) (inputs i) = Zmod.unsigned (N.v21064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21064 s i)) at 1.
  unfold R.v21064, N.v21064.
  rewrite ?node_7389.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21065 (s : N.State) (i : N.Inputs) :
  R.v21065 (state s) (inputs i) = Zmod.unsigned (N.v21065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21065 s i)) at 1.
  unfold R.v21065, N.v21065.
  unfold R.v6, N.v6.
  rewrite ?node_7500.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21066 (s : N.State) (i : N.Inputs) :
  R.v21066 (state s) (inputs i) = Zmod.unsigned (N.v21066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21066 s i)) at 1.
  unfold R.v21066, N.v21066.
  rewrite ?node_21064.
  rewrite ?node_21065.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21067 (s : N.State) (i : N.Inputs) :
  R.v21067 (state s) (inputs i) = Zmod.unsigned (N.v21067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21067 s i)) at 1.
  unfold R.v21067, N.v21067.
  rewrite ?node_21063.
  rewrite ?node_21066.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21068 (s : N.State) (i : N.Inputs) :
  R.v21068 (state s) (inputs i) = Zmod.unsigned (N.v21068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21068 s i)) at 1.
  unfold R.v21068, N.v21068.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21069 (s : N.State) (i : N.Inputs) :
  R.v21069 (state s) (inputs i) = Zmod.unsigned (N.v21069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21069 s i)) at 1.
  unfold R.v21069, N.v21069.
  rewrite ?node_7393.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21070 (s : N.State) (i : N.Inputs) :
  R.v21070 (state s) (inputs i) = Zmod.unsigned (N.v21070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21070 s i)) at 1.
  unfold R.v21070, N.v21070.
  unfold R.v6, N.v6.
  rewrite !state_r515_nr_5F515.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r515_nr_5F515 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21071 (s : N.State) (i : N.Inputs) :
  R.v21071 (state s) (inputs i) = Zmod.unsigned (N.v21071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21071 s i)) at 1.
  unfold R.v21071, N.v21071.
  unfold R.v6, N.v6.
  rewrite ?node_7389.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21072 (s : N.State) (i : N.Inputs) :
  R.v21072 (state s) (inputs i) = Zmod.unsigned (N.v21072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21072 s i)) at 1.
  unfold R.v21072, N.v21072.
  rewrite ?node_21070.
  rewrite ?node_21071.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21073 (s : N.State) (i : N.Inputs) :
  R.v21073 (state s) (inputs i) = Zmod.unsigned (N.v21073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21073 s i)) at 1.
  unfold R.v21073, N.v21073.
  unfold R.v16484, N.v16484.
  rewrite ?node_21072.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21074 (s : N.State) (i : N.Inputs) :
  R.v21074 (state s) (inputs i) = Zmod.unsigned (N.v21074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21074 s i)) at 1.
  unfold R.v21074, N.v21074.
  rewrite ?node_21069.
  rewrite ?node_21073.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21075 (s : N.State) (i : N.Inputs) :
  R.v21075 (state s) (inputs i) = Zmod.unsigned (N.v21075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21075 s i)) at 1.
  unfold R.v21075, N.v21075.
  unfold R.v6, N.v6.
  rewrite ?node_21074.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21076 (s : N.State) (i : N.Inputs) :
  R.v21076 (state s) (inputs i) = Zmod.unsigned (N.v21076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21076 s i)) at 1.
  unfold R.v21076, N.v21076.
  rewrite ?node_7394.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21077 (s : N.State) (i : N.Inputs) :
  R.v21077 (state s) (inputs i) = Zmod.unsigned (N.v21077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21077 s i)) at 1.
  unfold R.v21077, N.v21077.
  unfold R.v6, N.v6.
  rewrite ?node_7540.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21078 (s : N.State) (i : N.Inputs) :
  R.v21078 (state s) (inputs i) = Zmod.unsigned (N.v21078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21078 s i)) at 1.
  unfold R.v21078, N.v21078.
  rewrite ?node_21076.
  rewrite ?node_21077.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21079 (s : N.State) (i : N.Inputs) :
  R.v21079 (state s) (inputs i) = Zmod.unsigned (N.v21079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21079 s i)) at 1.
  unfold R.v21079, N.v21079.
  rewrite ?node_21075.
  rewrite ?node_21078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21080 (s : N.State) (i : N.Inputs) :
  R.v21080 (state s) (inputs i) = Zmod.unsigned (N.v21080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21080 s i)) at 1.
  unfold R.v21080, N.v21080.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21081 (s : N.State) (i : N.Inputs) :
  R.v21081 (state s) (inputs i) = Zmod.unsigned (N.v21081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21081 s i)) at 1.
  unfold R.v21081, N.v21081.
  rewrite ?node_7401.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21082 (s : N.State) (i : N.Inputs) :
  R.v21082 (state s) (inputs i) = Zmod.unsigned (N.v21082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21082 s i)) at 1.
  unfold R.v21082, N.v21082.
  unfold R.v16463, N.v16463.
  rewrite !state_r519_nr_5F519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r519_nr_5F519 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21083 (s : N.State) (i : N.Inputs) :
  R.v21083 (state s) (inputs i) = Zmod.unsigned (N.v21083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21083 s i)) at 1.
  unfold R.v21083, N.v21083.
  unfold R.v16463, N.v16463.
  rewrite !state_r518_nr_5F518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r518_nr_5F518 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21084 (s : N.State) (i : N.Inputs) :
  R.v21084 (state s) (inputs i) = Zmod.unsigned (N.v21084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21084 s i)) at 1.
  unfold R.v21084, N.v21084.
  unfold R.v6, N.v6.
  rewrite !state_r517_nr_5F517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r517_nr_5F517 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21085 (s : N.State) (i : N.Inputs) :
  R.v21085 (state s) (inputs i) = Zmod.unsigned (N.v21085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21085 s i)) at 1.
  unfold R.v21085, N.v21085.
  unfold R.v6, N.v6.
  rewrite !state_r516_nr_5F516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r516_nr_5F516 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21086 (s : N.State) (i : N.Inputs) :
  R.v21086 (state s) (inputs i) = Zmod.unsigned (N.v21086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21086 s i)) at 1.
  unfold R.v21086, N.v21086.
  rewrite ?node_21084.
  rewrite ?node_21085.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21087 (s : N.State) (i : N.Inputs) :
  R.v21087 (state s) (inputs i) = Zmod.unsigned (N.v21087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21087 s i)) at 1.
  unfold R.v21087, N.v21087.
  unfold R.v16484, N.v16484.
  rewrite ?node_21086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21088 (s : N.State) (i : N.Inputs) :
  R.v21088 (state s) (inputs i) = Zmod.unsigned (N.v21088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21088 s i)) at 1.
  unfold R.v21088, N.v21088.
  rewrite ?node_21081.
  rewrite ?node_21082.
  rewrite ?node_21083.
  rewrite ?node_21087.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21089 (s : N.State) (i : N.Inputs) :
  R.v21089 (state s) (inputs i) = Zmod.unsigned (N.v21089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21089 s i)) at 1.
  unfold R.v21089, N.v21089.
  unfold R.v6, N.v6.
  rewrite ?node_21088.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21090 (s : N.State) (i : N.Inputs) :
  R.v21090 (state s) (inputs i) = Zmod.unsigned (N.v21090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21090 s i)) at 1.
  unfold R.v21090, N.v21090.
  rewrite ?node_7402.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21091 (s : N.State) (i : N.Inputs) :
  R.v21091 (state s) (inputs i) = Zmod.unsigned (N.v21091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21091 s i)) at 1.
  unfold R.v21091, N.v21091.
  unfold R.v6, N.v6.
  rewrite ?node_7508.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21092 (s : N.State) (i : N.Inputs) :
  R.v21092 (state s) (inputs i) = Zmod.unsigned (N.v21092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21092 s i)) at 1.
  unfold R.v21092, N.v21092.
  unfold R.v6, N.v6.
  rewrite ?node_7543.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21093 (s : N.State) (i : N.Inputs) :
  R.v21093 (state s) (inputs i) = Zmod.unsigned (N.v21093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21093 s i)) at 1.
  unfold R.v21093, N.v21093.
  rewrite ?node_21090.
  rewrite ?node_21091.
  rewrite ?node_21092.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21094 (s : N.State) (i : N.Inputs) :
  R.v21094 (state s) (inputs i) = Zmod.unsigned (N.v21094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21094 s i)) at 1.
  unfold R.v21094, N.v21094.
  rewrite ?node_21089.
  rewrite ?node_21093.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21095 (s : N.State) (i : N.Inputs) :
  R.v21095 (state s) (inputs i) = Zmod.unsigned (N.v21095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21095 s i)) at 1.
  unfold R.v21095, N.v21095.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21096 (s : N.State) (i : N.Inputs) :
  R.v21096 (state s) (inputs i) = Zmod.unsigned (N.v21096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21096 s i)) at 1.
  unfold R.v21096, N.v21096.
  unfold R.v16463, N.v16463.
  rewrite !state_r518_nr_5F518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r518_nr_5F518 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21097 (s : N.State) (i : N.Inputs) :
  R.v21097 (state s) (inputs i) = Zmod.unsigned (N.v21097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21097 s i)) at 1.
  unfold R.v21097, N.v21097.
  unfold R.v6, N.v6.
  rewrite !state_r517_nr_5F517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r517_nr_5F517 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21098 (s : N.State) (i : N.Inputs) :
  R.v21098 (state s) (inputs i) = Zmod.unsigned (N.v21098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21098 s i)) at 1.
  unfold R.v21098, N.v21098.
  unfold R.v6, N.v6.
  rewrite !state_r516_nr_5F516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r516_nr_5F516 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21099 (s : N.State) (i : N.Inputs) :
  R.v21099 (state s) (inputs i) = Zmod.unsigned (N.v21099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21099 s i)) at 1.
  unfold R.v21099, N.v21099.
  rewrite ?node_21097.
  rewrite ?node_21098.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21100 (s : N.State) (i : N.Inputs) :
  R.v21100 (state s) (inputs i) = Zmod.unsigned (N.v21100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21100 s i)) at 1.
  unfold R.v21100, N.v21100.
  unfold R.v16484, N.v16484.
  rewrite ?node_21099.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21101 (s : N.State) (i : N.Inputs) :
  R.v21101 (state s) (inputs i) = Zmod.unsigned (N.v21101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21101 s i)) at 1.
  unfold R.v21101, N.v21101.
  rewrite ?node_21096.
  rewrite ?node_21100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21102 (s : N.State) (i : N.Inputs) :
  R.v21102 (state s) (inputs i) = Zmod.unsigned (N.v21102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21102 s i)) at 1.
  unfold R.v21102, N.v21102.
  unfold R.v6, N.v6.
  rewrite ?node_21101.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21103 (s : N.State) (i : N.Inputs) :
  R.v21103 (state s) (inputs i) = Zmod.unsigned (N.v21103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21103 s i)) at 1.
  unfold R.v21103, N.v21103.
  rewrite ?node_7397.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21104 (s : N.State) (i : N.Inputs) :
  R.v21104 (state s) (inputs i) = Zmod.unsigned (N.v21104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21104 s i)) at 1.
  unfold R.v21104, N.v21104.
  unfold R.v6, N.v6.
  rewrite ?node_7508.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21105 (s : N.State) (i : N.Inputs) :
  R.v21105 (state s) (inputs i) = Zmod.unsigned (N.v21105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21105 s i)) at 1.
  unfold R.v21105, N.v21105.
  rewrite ?node_21103.
  rewrite ?node_21104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21106 (s : N.State) (i : N.Inputs) :
  R.v21106 (state s) (inputs i) = Zmod.unsigned (N.v21106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21106 s i)) at 1.
  unfold R.v21106, N.v21106.
  rewrite ?node_21102.
  rewrite ?node_21105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21107 (s : N.State) (i : N.Inputs) :
  R.v21107 (state s) (inputs i) = Zmod.unsigned (N.v21107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21107 s i)) at 1.
  unfold R.v21107, N.v21107.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21108 (s : N.State) (i : N.Inputs) :
  R.v21108 (state s) (inputs i) = Zmod.unsigned (N.v21108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21108 s i)) at 1.
  unfold R.v21108, N.v21108.
  rewrite ?node_7401.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21109 (s : N.State) (i : N.Inputs) :
  R.v21109 (state s) (inputs i) = Zmod.unsigned (N.v21109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21109 s i)) at 1.
  unfold R.v21109, N.v21109.
  unfold R.v6, N.v6.
  rewrite !state_r519_nr_5F519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r519_nr_5F519 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21110 (s : N.State) (i : N.Inputs) :
  R.v21110 (state s) (inputs i) = Zmod.unsigned (N.v21110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21110 s i)) at 1.
  unfold R.v21110, N.v21110.
  unfold R.v6, N.v6.
  rewrite ?node_7397.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21111 (s : N.State) (i : N.Inputs) :
  R.v21111 (state s) (inputs i) = Zmod.unsigned (N.v21111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21111 s i)) at 1.
  unfold R.v21111, N.v21111.
  rewrite ?node_21109.
  rewrite ?node_21110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21112 (s : N.State) (i : N.Inputs) :
  R.v21112 (state s) (inputs i) = Zmod.unsigned (N.v21112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21112 s i)) at 1.
  unfold R.v21112, N.v21112.
  unfold R.v16484, N.v16484.
  rewrite ?node_21111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21113 (s : N.State) (i : N.Inputs) :
  R.v21113 (state s) (inputs i) = Zmod.unsigned (N.v21113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21113 s i)) at 1.
  unfold R.v21113, N.v21113.
  rewrite ?node_21108.
  rewrite ?node_21112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21114 (s : N.State) (i : N.Inputs) :
  R.v21114 (state s) (inputs i) = Zmod.unsigned (N.v21114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21114 s i)) at 1.
  unfold R.v21114, N.v21114.
  unfold R.v6, N.v6.
  rewrite ?node_21113.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21115 (s : N.State) (i : N.Inputs) :
  R.v21115 (state s) (inputs i) = Zmod.unsigned (N.v21115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21115 s i)) at 1.
  unfold R.v21115, N.v21115.
  rewrite ?node_7402.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21116 (s : N.State) (i : N.Inputs) :
  R.v21116 (state s) (inputs i) = Zmod.unsigned (N.v21116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21116 s i)) at 1.
  unfold R.v21116, N.v21116.
  unfold R.v6, N.v6.
  rewrite ?node_7543.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21117 (s : N.State) (i : N.Inputs) :
  R.v21117 (state s) (inputs i) = Zmod.unsigned (N.v21117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21117 s i)) at 1.
  unfold R.v21117, N.v21117.
  rewrite ?node_21115.
  rewrite ?node_21116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21118 (s : N.State) (i : N.Inputs) :
  R.v21118 (state s) (inputs i) = Zmod.unsigned (N.v21118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21118 s i)) at 1.
  unfold R.v21118, N.v21118.
  rewrite ?node_21114.
  rewrite ?node_21117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21119 (s : N.State) (i : N.Inputs) :
  R.v21119 (state s) (inputs i) = Zmod.unsigned (N.v21119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21119 s i)) at 1.
  unfold R.v21119, N.v21119.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21120 (s : N.State) (i : N.Inputs) :
  R.v21120 (state s) (inputs i) = Zmod.unsigned (N.v21120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21120 s i)) at 1.
  unfold R.v21120, N.v21120.
  rewrite ?node_7413.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21121 (s : N.State) (i : N.Inputs) :
  R.v21121 (state s) (inputs i) = Zmod.unsigned (N.v21121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21121 s i)) at 1.
  unfold R.v21121, N.v21121.
  unfold R.v16463, N.v16463.
  rewrite !state_r523_nr_5F523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r523_nr_5F523 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21122 (s : N.State) (i : N.Inputs) :
  R.v21122 (state s) (inputs i) = Zmod.unsigned (N.v21122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21122 s i)) at 1.
  unfold R.v21122, N.v21122.
  unfold R.v16463, N.v16463.
  rewrite !state_r522_nr_5F522.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r522_nr_5F522 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21123 (s : N.State) (i : N.Inputs) :
  R.v21123 (state s) (inputs i) = Zmod.unsigned (N.v21123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21123 s i)) at 1.
  unfold R.v21123, N.v21123.
  unfold R.v6, N.v6.
  rewrite !state_r521_nr_5F521.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r521_nr_5F521 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21124 (s : N.State) (i : N.Inputs) :
  R.v21124 (state s) (inputs i) = Zmod.unsigned (N.v21124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21124 s i)) at 1.
  unfold R.v21124, N.v21124.
  unfold R.v6, N.v6.
  rewrite !state_r520_nr_5F520.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r520_nr_5F520 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21125 (s : N.State) (i : N.Inputs) :
  R.v21125 (state s) (inputs i) = Zmod.unsigned (N.v21125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21125 s i)) at 1.
  unfold R.v21125, N.v21125.
  rewrite ?node_21123.
  rewrite ?node_21124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21126 (s : N.State) (i : N.Inputs) :
  R.v21126 (state s) (inputs i) = Zmod.unsigned (N.v21126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21126 s i)) at 1.
  unfold R.v21126, N.v21126.
  unfold R.v16484, N.v16484.
  rewrite ?node_21125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21127 (s : N.State) (i : N.Inputs) :
  R.v21127 (state s) (inputs i) = Zmod.unsigned (N.v21127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21127 s i)) at 1.
  unfold R.v21127, N.v21127.
  rewrite ?node_21120.
  rewrite ?node_21121.
  rewrite ?node_21122.
  rewrite ?node_21126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21128 (s : N.State) (i : N.Inputs) :
  R.v21128 (state s) (inputs i) = Zmod.unsigned (N.v21128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21128 s i)) at 1.
  unfold R.v21128, N.v21128.
  unfold R.v6, N.v6.
  rewrite ?node_21127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21129 (s : N.State) (i : N.Inputs) :
  R.v21129 (state s) (inputs i) = Zmod.unsigned (N.v21129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21129 s i)) at 1.
  unfold R.v21129, N.v21129.
  rewrite ?node_7414.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21130 (s : N.State) (i : N.Inputs) :
  R.v21130 (state s) (inputs i) = Zmod.unsigned (N.v21130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21130 s i)) at 1.
  unfold R.v21130, N.v21130.
  unfold R.v6, N.v6.
  rewrite ?node_7520.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21131 (s : N.State) (i : N.Inputs) :
  R.v21131 (state s) (inputs i) = Zmod.unsigned (N.v21131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21131 s i)) at 1.
  unfold R.v21131, N.v21131.
  unfold R.v6, N.v6.
  rewrite ?node_7547.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21132 (s : N.State) (i : N.Inputs) :
  R.v21132 (state s) (inputs i) = Zmod.unsigned (N.v21132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21132 s i)) at 1.
  unfold R.v21132, N.v21132.
  rewrite ?node_21129.
  rewrite ?node_21130.
  rewrite ?node_21131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21133 (s : N.State) (i : N.Inputs) :
  R.v21133 (state s) (inputs i) = Zmod.unsigned (N.v21133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21133 s i)) at 1.
  unfold R.v21133, N.v21133.
  rewrite ?node_21128.
  rewrite ?node_21132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21134 (s : N.State) (i : N.Inputs) :
  R.v21134 (state s) (inputs i) = Zmod.unsigned (N.v21134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21134 s i)) at 1.
  unfold R.v21134, N.v21134.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21135 (s : N.State) (i : N.Inputs) :
  R.v21135 (state s) (inputs i) = Zmod.unsigned (N.v21135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21135 s i)) at 1.
  unfold R.v21135, N.v21135.
  unfold R.v16463, N.v16463.
  rewrite !state_r522_nr_5F522.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r522_nr_5F522 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21136 (s : N.State) (i : N.Inputs) :
  R.v21136 (state s) (inputs i) = Zmod.unsigned (N.v21136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21136 s i)) at 1.
  unfold R.v21136, N.v21136.
  unfold R.v6, N.v6.
  rewrite !state_r521_nr_5F521.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r521_nr_5F521 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21137 (s : N.State) (i : N.Inputs) :
  R.v21137 (state s) (inputs i) = Zmod.unsigned (N.v21137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21137 s i)) at 1.
  unfold R.v21137, N.v21137.
  unfold R.v6, N.v6.
  rewrite !state_r520_nr_5F520.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r520_nr_5F520 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21138 (s : N.State) (i : N.Inputs) :
  R.v21138 (state s) (inputs i) = Zmod.unsigned (N.v21138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21138 s i)) at 1.
  unfold R.v21138, N.v21138.
  rewrite ?node_21136.
  rewrite ?node_21137.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21139 (s : N.State) (i : N.Inputs) :
  R.v21139 (state s) (inputs i) = Zmod.unsigned (N.v21139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21139 s i)) at 1.
  unfold R.v21139, N.v21139.
  unfold R.v16484, N.v16484.
  rewrite ?node_21138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21140 (s : N.State) (i : N.Inputs) :
  R.v21140 (state s) (inputs i) = Zmod.unsigned (N.v21140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21140 s i)) at 1.
  unfold R.v21140, N.v21140.
  rewrite ?node_21135.
  rewrite ?node_21139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21141 (s : N.State) (i : N.Inputs) :
  R.v21141 (state s) (inputs i) = Zmod.unsigned (N.v21141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21141 s i)) at 1.
  unfold R.v21141, N.v21141.
  unfold R.v6, N.v6.
  rewrite ?node_21140.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21142 (s : N.State) (i : N.Inputs) :
  R.v21142 (state s) (inputs i) = Zmod.unsigned (N.v21142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21142 s i)) at 1.
  unfold R.v21142, N.v21142.
  rewrite ?node_7409.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21143 (s : N.State) (i : N.Inputs) :
  R.v21143 (state s) (inputs i) = Zmod.unsigned (N.v21143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21143 s i)) at 1.
  unfold R.v21143, N.v21143.
  unfold R.v6, N.v6.
  rewrite ?node_7520.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21144 (s : N.State) (i : N.Inputs) :
  R.v21144 (state s) (inputs i) = Zmod.unsigned (N.v21144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21144 s i)) at 1.
  unfold R.v21144, N.v21144.
  rewrite ?node_21142.
  rewrite ?node_21143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21145 (s : N.State) (i : N.Inputs) :
  R.v21145 (state s) (inputs i) = Zmod.unsigned (N.v21145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21145 s i)) at 1.
  unfold R.v21145, N.v21145.
  rewrite ?node_21141.
  rewrite ?node_21144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21146 (s : N.State) (i : N.Inputs) :
  R.v21146 (state s) (inputs i) = Zmod.unsigned (N.v21146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21146 s i)) at 1.
  unfold R.v21146, N.v21146.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21147 (s : N.State) (i : N.Inputs) :
  R.v21147 (state s) (inputs i) = Zmod.unsigned (N.v21147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21147 s i)) at 1.
  unfold R.v21147, N.v21147.
  rewrite ?node_7413.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21148 (s : N.State) (i : N.Inputs) :
  R.v21148 (state s) (inputs i) = Zmod.unsigned (N.v21148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21148 s i)) at 1.
  unfold R.v21148, N.v21148.
  unfold R.v6, N.v6.
  rewrite !state_r523_nr_5F523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r523_nr_5F523 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21149 (s : N.State) (i : N.Inputs) :
  R.v21149 (state s) (inputs i) = Zmod.unsigned (N.v21149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21149 s i)) at 1.
  unfold R.v21149, N.v21149.
  unfold R.v6, N.v6.
  rewrite ?node_7409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21150 (s : N.State) (i : N.Inputs) :
  R.v21150 (state s) (inputs i) = Zmod.unsigned (N.v21150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21150 s i)) at 1.
  unfold R.v21150, N.v21150.
  rewrite ?node_21148.
  rewrite ?node_21149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21151 (s : N.State) (i : N.Inputs) :
  R.v21151 (state s) (inputs i) = Zmod.unsigned (N.v21151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21151 s i)) at 1.
  unfold R.v21151, N.v21151.
  unfold R.v16484, N.v16484.
  rewrite ?node_21150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21152 (s : N.State) (i : N.Inputs) :
  R.v21152 (state s) (inputs i) = Zmod.unsigned (N.v21152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21152 s i)) at 1.
  unfold R.v21152, N.v21152.
  rewrite ?node_21147.
  rewrite ?node_21151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21153 (s : N.State) (i : N.Inputs) :
  R.v21153 (state s) (inputs i) = Zmod.unsigned (N.v21153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21153 s i)) at 1.
  unfold R.v21153, N.v21153.
  unfold R.v6, N.v6.
  rewrite ?node_21152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21154 (s : N.State) (i : N.Inputs) :
  R.v21154 (state s) (inputs i) = Zmod.unsigned (N.v21154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21154 s i)) at 1.
  unfold R.v21154, N.v21154.
  rewrite ?node_7414.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21155 (s : N.State) (i : N.Inputs) :
  R.v21155 (state s) (inputs i) = Zmod.unsigned (N.v21155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21155 s i)) at 1.
  unfold R.v21155, N.v21155.
  unfold R.v6, N.v6.
  rewrite ?node_7547.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21156 (s : N.State) (i : N.Inputs) :
  R.v21156 (state s) (inputs i) = Zmod.unsigned (N.v21156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21156 s i)) at 1.
  unfold R.v21156, N.v21156.
  rewrite ?node_21154.
  rewrite ?node_21155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21157 (s : N.State) (i : N.Inputs) :
  R.v21157 (state s) (inputs i) = Zmod.unsigned (N.v21157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21157 s i)) at 1.
  unfold R.v21157, N.v21157.
  rewrite ?node_21153.
  rewrite ?node_21156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21158 (s : N.State) (i : N.Inputs) :
  R.v21158 (state s) (inputs i) = Zmod.unsigned (N.v21158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21158 s i)) at 1.
  unfold R.v21158, N.v21158.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21159 (s : N.State) (i : N.Inputs) :
  R.v21159 (state s) (inputs i) = Zmod.unsigned (N.v21159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21159 s i)) at 1.
  unfold R.v21159, N.v21159.
  unfold R.v16463, N.v16463.
  rewrite !state_r526_nr_5F526.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r526_nr_5F526 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21160 (s : N.State) (i : N.Inputs) :
  R.v21160 (state s) (inputs i) = Zmod.unsigned (N.v21160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21160 s i)) at 1.
  unfold R.v21160, N.v21160.
  unfold R.v6, N.v6.
  rewrite !state_r525_nr_5F525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r525_nr_5F525 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21161 (s : N.State) (i : N.Inputs) :
  R.v21161 (state s) (inputs i) = Zmod.unsigned (N.v21161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21161 s i)) at 1.
  unfold R.v21161, N.v21161.
  unfold R.v6, N.v6.
  rewrite !state_r524_nr_5F524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r524_nr_5F524 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21162 (s : N.State) (i : N.Inputs) :
  R.v21162 (state s) (inputs i) = Zmod.unsigned (N.v21162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21162 s i)) at 1.
  unfold R.v21162, N.v21162.
  rewrite ?node_21160.
  rewrite ?node_21161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21163 (s : N.State) (i : N.Inputs) :
  R.v21163 (state s) (inputs i) = Zmod.unsigned (N.v21163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21163 s i)) at 1.
  unfold R.v21163, N.v21163.
  unfold R.v16484, N.v16484.
  rewrite ?node_21162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21164 (s : N.State) (i : N.Inputs) :
  R.v21164 (state s) (inputs i) = Zmod.unsigned (N.v21164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21164 s i)) at 1.
  unfold R.v21164, N.v21164.
  rewrite ?node_21159.
  rewrite ?node_21163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21165 (s : N.State) (i : N.Inputs) :
  R.v21165 (state s) (inputs i) = Zmod.unsigned (N.v21165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21165 s i)) at 1.
  unfold R.v21165, N.v21165.
  unfold R.v6, N.v6.
  rewrite ?node_21164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21166 (s : N.State) (i : N.Inputs) :
  R.v21166 (state s) (inputs i) = Zmod.unsigned (N.v21166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21166 s i)) at 1.
  unfold R.v21166, N.v21166.
  rewrite ?node_7416.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21167 (s : N.State) (i : N.Inputs) :
  R.v21167 (state s) (inputs i) = Zmod.unsigned (N.v21167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21167 s i)) at 1.
  unfold R.v21167, N.v21167.
  unfold R.v6, N.v6.
  rewrite ?node_7551.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21168 (s : N.State) (i : N.Inputs) :
  R.v21168 (state s) (inputs i) = Zmod.unsigned (N.v21168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21168 s i)) at 1.
  unfold R.v21168, N.v21168.
  rewrite ?node_21166.
  rewrite ?node_21167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21169 (s : N.State) (i : N.Inputs) :
  R.v21169 (state s) (inputs i) = Zmod.unsigned (N.v21169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21169 s i)) at 1.
  unfold R.v21169, N.v21169.
  rewrite ?node_21165.
  rewrite ?node_21168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21170 (s : N.State) (i : N.Inputs) :
  R.v21170 (state s) (inputs i) = Zmod.unsigned (N.v21170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21170 s i)) at 1.
  unfold R.v21170, N.v21170.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21171 (s : N.State) (i : N.Inputs) :
  R.v21171 (state s) (inputs i) = Zmod.unsigned (N.v21171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21171 s i)) at 1.
  unfold R.v21171, N.v21171.
  rewrite ?node_7485.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21172 (s : N.State) (i : N.Inputs) :
  R.v21172 (state s) (inputs i) = Zmod.unsigned (N.v21172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21172 s i)) at 1.
  unfold R.v21172, N.v21172.
  unfold R.v16463, N.v16463.
  rewrite !state_r530_nr_5F530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r530_nr_5F530 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21173 (s : N.State) (i : N.Inputs) :
  R.v21173 (state s) (inputs i) = Zmod.unsigned (N.v21173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21173 s i)) at 1.
  unfold R.v21173, N.v21173.
  unfold R.v16463, N.v16463.
  rewrite !state_r529_nr_5F529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r529_nr_5F529 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21174 (s : N.State) (i : N.Inputs) :
  R.v21174 (state s) (inputs i) = Zmod.unsigned (N.v21174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21174 s i)) at 1.
  unfold R.v21174, N.v21174.
  unfold R.v6, N.v6.
  rewrite !state_r528_nr_5F528.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r528_nr_5F528 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21175 (s : N.State) (i : N.Inputs) :
  R.v21175 (state s) (inputs i) = Zmod.unsigned (N.v21175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21175 s i)) at 1.
  unfold R.v21175, N.v21175.
  unfold R.v6, N.v6.
  rewrite !state_r527_nr_5F527.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r527_nr_5F527 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21176 (s : N.State) (i : N.Inputs) :
  R.v21176 (state s) (inputs i) = Zmod.unsigned (N.v21176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21176 s i)) at 1.
  unfold R.v21176, N.v21176.
  rewrite ?node_21174.
  rewrite ?node_21175.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21177 (s : N.State) (i : N.Inputs) :
  R.v21177 (state s) (inputs i) = Zmod.unsigned (N.v21177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21177 s i)) at 1.
  unfold R.v21177, N.v21177.
  unfold R.v16484, N.v16484.
  rewrite ?node_21176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21178 (s : N.State) (i : N.Inputs) :
  R.v21178 (state s) (inputs i) = Zmod.unsigned (N.v21178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21178 s i)) at 1.
  unfold R.v21178, N.v21178.
  rewrite ?node_21171.
  rewrite ?node_21172.
  rewrite ?node_21173.
  rewrite ?node_21177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21179 (s : N.State) (i : N.Inputs) :
  R.v21179 (state s) (inputs i) = Zmod.unsigned (N.v21179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21179 s i)) at 1.
  unfold R.v21179, N.v21179.
  unfold R.v6, N.v6.
  rewrite ?node_21178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21180 (s : N.State) (i : N.Inputs) :
  R.v21180 (state s) (inputs i) = Zmod.unsigned (N.v21180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21180 s i)) at 1.
  unfold R.v21180, N.v21180.
  rewrite ?node_7486.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21181 (s : N.State) (i : N.Inputs) :
  R.v21181 (state s) (inputs i) = Zmod.unsigned (N.v21181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21181 s i)) at 1.
  unfold R.v21181, N.v21181.
  unfold R.v6, N.v6.
  rewrite ?node_7596.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21182 (s : N.State) (i : N.Inputs) :
  R.v21182 (state s) (inputs i) = Zmod.unsigned (N.v21182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21182 s i)) at 1.
  unfold R.v21182, N.v21182.
  unfold R.v6, N.v6.
  rewrite ?node_7639.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21183 (s : N.State) (i : N.Inputs) :
  R.v21183 (state s) (inputs i) = Zmod.unsigned (N.v21183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21183 s i)) at 1.
  unfold R.v21183, N.v21183.
  rewrite ?node_21180.
  rewrite ?node_21181.
  rewrite ?node_21182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21184 (s : N.State) (i : N.Inputs) :
  R.v21184 (state s) (inputs i) = Zmod.unsigned (N.v21184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21184 s i)) at 1.
  unfold R.v21184, N.v21184.
  rewrite ?node_21179.
  rewrite ?node_21183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21185 (s : N.State) (i : N.Inputs) :
  R.v21185 (state s) (inputs i) = Zmod.unsigned (N.v21185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21185 s i)) at 1.
  unfold R.v21185, N.v21185.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21186 (s : N.State) (i : N.Inputs) :
  R.v21186 (state s) (inputs i) = Zmod.unsigned (N.v21186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21186 s i)) at 1.
  unfold R.v21186, N.v21186.
  unfold R.v16463, N.v16463.
  rewrite !state_r529_nr_5F529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r529_nr_5F529 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21187 (s : N.State) (i : N.Inputs) :
  R.v21187 (state s) (inputs i) = Zmod.unsigned (N.v21187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21187 s i)) at 1.
  unfold R.v21187, N.v21187.
  unfold R.v6, N.v6.
  rewrite !state_r528_nr_5F528.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r528_nr_5F528 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21188 (s : N.State) (i : N.Inputs) :
  R.v21188 (state s) (inputs i) = Zmod.unsigned (N.v21188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21188 s i)) at 1.
  unfold R.v21188, N.v21188.
  unfold R.v6, N.v6.
  rewrite !state_r527_nr_5F527.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r527_nr_5F527 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21189 (s : N.State) (i : N.Inputs) :
  R.v21189 (state s) (inputs i) = Zmod.unsigned (N.v21189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21189 s i)) at 1.
  unfold R.v21189, N.v21189.
  rewrite ?node_21187.
  rewrite ?node_21188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21190 (s : N.State) (i : N.Inputs) :
  R.v21190 (state s) (inputs i) = Zmod.unsigned (N.v21190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21190 s i)) at 1.
  unfold R.v21190, N.v21190.
  unfold R.v16484, N.v16484.
  rewrite ?node_21189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21191 (s : N.State) (i : N.Inputs) :
  R.v21191 (state s) (inputs i) = Zmod.unsigned (N.v21191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21191 s i)) at 1.
  unfold R.v21191, N.v21191.
  rewrite ?node_21186.
  rewrite ?node_21190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21192 (s : N.State) (i : N.Inputs) :
  R.v21192 (state s) (inputs i) = Zmod.unsigned (N.v21192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21192 s i)) at 1.
  unfold R.v21192, N.v21192.
  unfold R.v6, N.v6.
  rewrite ?node_21191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21193 (s : N.State) (i : N.Inputs) :
  R.v21193 (state s) (inputs i) = Zmod.unsigned (N.v21193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21193 s i)) at 1.
  unfold R.v21193, N.v21193.
  rewrite ?node_7481.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21194 (s : N.State) (i : N.Inputs) :
  R.v21194 (state s) (inputs i) = Zmod.unsigned (N.v21194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21194 s i)) at 1.
  unfold R.v21194, N.v21194.
  unfold R.v6, N.v6.
  rewrite ?node_7596.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21195 (s : N.State) (i : N.Inputs) :
  R.v21195 (state s) (inputs i) = Zmod.unsigned (N.v21195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21195 s i)) at 1.
  unfold R.v21195, N.v21195.
  rewrite ?node_21193.
  rewrite ?node_21194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21196 (s : N.State) (i : N.Inputs) :
  R.v21196 (state s) (inputs i) = Zmod.unsigned (N.v21196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21196 s i)) at 1.
  unfold R.v21196, N.v21196.
  rewrite ?node_21192.
  rewrite ?node_21195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21197 (s : N.State) (i : N.Inputs) :
  R.v21197 (state s) (inputs i) = Zmod.unsigned (N.v21197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21197 s i)) at 1.
  unfold R.v21197, N.v21197.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21198 (s : N.State) (i : N.Inputs) :
  R.v21198 (state s) (inputs i) = Zmod.unsigned (N.v21198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21198 s i)) at 1.
  unfold R.v21198, N.v21198.
  rewrite ?node_7485.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21199 (s : N.State) (i : N.Inputs) :
  R.v21199 (state s) (inputs i) = Zmod.unsigned (N.v21199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21199 s i)) at 1.
  unfold R.v21199, N.v21199.
  unfold R.v6, N.v6.
  rewrite !state_r530_nr_5F530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r530_nr_5F530 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21200 (s : N.State) (i : N.Inputs) :
  R.v21200 (state s) (inputs i) = Zmod.unsigned (N.v21200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21200 s i)) at 1.
  unfold R.v21200, N.v21200.
  unfold R.v6, N.v6.
  rewrite ?node_7481.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21201 (s : N.State) (i : N.Inputs) :
  R.v21201 (state s) (inputs i) = Zmod.unsigned (N.v21201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21201 s i)) at 1.
  unfold R.v21201, N.v21201.
  rewrite ?node_21199.
  rewrite ?node_21200.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21202 (s : N.State) (i : N.Inputs) :
  R.v21202 (state s) (inputs i) = Zmod.unsigned (N.v21202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21202 s i)) at 1.
  unfold R.v21202, N.v21202.
  unfold R.v16484, N.v16484.
  rewrite ?node_21201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21203 (s : N.State) (i : N.Inputs) :
  R.v21203 (state s) (inputs i) = Zmod.unsigned (N.v21203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21203 s i)) at 1.
  unfold R.v21203, N.v21203.
  rewrite ?node_21198.
  rewrite ?node_21202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21204 (s : N.State) (i : N.Inputs) :
  R.v21204 (state s) (inputs i) = Zmod.unsigned (N.v21204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21204 s i)) at 1.
  unfold R.v21204, N.v21204.
  unfold R.v6, N.v6.
  rewrite ?node_21203.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21205 (s : N.State) (i : N.Inputs) :
  R.v21205 (state s) (inputs i) = Zmod.unsigned (N.v21205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21205 s i)) at 1.
  unfold R.v21205, N.v21205.
  rewrite ?node_7486.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21206 (s : N.State) (i : N.Inputs) :
  R.v21206 (state s) (inputs i) = Zmod.unsigned (N.v21206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21206 s i)) at 1.
  unfold R.v21206, N.v21206.
  unfold R.v6, N.v6.
  rewrite ?node_7639.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21207 (s : N.State) (i : N.Inputs) :
  R.v21207 (state s) (inputs i) = Zmod.unsigned (N.v21207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21207 s i)) at 1.
  unfold R.v21207, N.v21207.
  rewrite ?node_21205.
  rewrite ?node_21206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21208 (s : N.State) (i : N.Inputs) :
  R.v21208 (state s) (inputs i) = Zmod.unsigned (N.v21208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21208 s i)) at 1.
  unfold R.v21208, N.v21208.
  rewrite ?node_21204.
  rewrite ?node_21207.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21209 (s : N.State) (i : N.Inputs) :
  R.v21209 (state s) (inputs i) = Zmod.unsigned (N.v21209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21209 s i)) at 1.
  unfold R.v21209, N.v21209.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21210 (s : N.State) (i : N.Inputs) :
  R.v21210 (state s) (inputs i) = Zmod.unsigned (N.v21210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21210 s i)) at 1.
  unfold R.v21210, N.v21210.
  rewrite ?node_7492.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21211 (s : N.State) (i : N.Inputs) :
  R.v21211 (state s) (inputs i) = Zmod.unsigned (N.v21211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21211 s i)) at 1.
  unfold R.v21211, N.v21211.
  unfold R.v16463, N.v16463.
  rewrite !state_r534_nr_5F534.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r534_nr_5F534 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21212 (s : N.State) (i : N.Inputs) :
  R.v21212 (state s) (inputs i) = Zmod.unsigned (N.v21212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21212 s i)) at 1.
  unfold R.v21212, N.v21212.
  unfold R.v16463, N.v16463.
  rewrite !state_r533_nr_5F533.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r533_nr_5F533 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21213 (s : N.State) (i : N.Inputs) :
  R.v21213 (state s) (inputs i) = Zmod.unsigned (N.v21213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21213 s i)) at 1.
  unfold R.v21213, N.v21213.
  unfold R.v6, N.v6.
  rewrite !state_r532_nr_5F532.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r532_nr_5F532 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21214 (s : N.State) (i : N.Inputs) :
  R.v21214 (state s) (inputs i) = Zmod.unsigned (N.v21214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21214 s i)) at 1.
  unfold R.v21214, N.v21214.
  unfold R.v6, N.v6.
  rewrite !state_r531_nr_5F531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r531_nr_5F531 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21215 (s : N.State) (i : N.Inputs) :
  R.v21215 (state s) (inputs i) = Zmod.unsigned (N.v21215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21215 s i)) at 1.
  unfold R.v21215, N.v21215.
  rewrite ?node_21213.
  rewrite ?node_21214.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21216 (s : N.State) (i : N.Inputs) :
  R.v21216 (state s) (inputs i) = Zmod.unsigned (N.v21216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21216 s i)) at 1.
  unfold R.v21216, N.v21216.
  unfold R.v16484, N.v16484.
  rewrite ?node_21215.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21217 (s : N.State) (i : N.Inputs) :
  R.v21217 (state s) (inputs i) = Zmod.unsigned (N.v21217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21217 s i)) at 1.
  unfold R.v21217, N.v21217.
  rewrite ?node_21210.
  rewrite ?node_21211.
  rewrite ?node_21212.
  rewrite ?node_21216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21218 (s : N.State) (i : N.Inputs) :
  R.v21218 (state s) (inputs i) = Zmod.unsigned (N.v21218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21218 s i)) at 1.
  unfold R.v21218, N.v21218.
  unfold R.v6, N.v6.
  rewrite ?node_21217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21219 (s : N.State) (i : N.Inputs) :
  R.v21219 (state s) (inputs i) = Zmod.unsigned (N.v21219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21219 s i)) at 1.
  unfold R.v21219, N.v21219.
  rewrite ?node_7493.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21220 (s : N.State) (i : N.Inputs) :
  R.v21220 (state s) (inputs i) = Zmod.unsigned (N.v21220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21220 s i)) at 1.
  unfold R.v21220, N.v21220.
  unfold R.v6, N.v6.
  rewrite ?node_7603.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21221 (s : N.State) (i : N.Inputs) :
  R.v21221 (state s) (inputs i) = Zmod.unsigned (N.v21221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21221 s i)) at 1.
  unfold R.v21221, N.v21221.
  unfold R.v6, N.v6.
  rewrite ?node_7643.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21222 (s : N.State) (i : N.Inputs) :
  R.v21222 (state s) (inputs i) = Zmod.unsigned (N.v21222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21222 s i)) at 1.
  unfold R.v21222, N.v21222.
  rewrite ?node_21219.
  rewrite ?node_21220.
  rewrite ?node_21221.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21223 (s : N.State) (i : N.Inputs) :
  R.v21223 (state s) (inputs i) = Zmod.unsigned (N.v21223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21223 s i)) at 1.
  unfold R.v21223, N.v21223.
  rewrite ?node_21218.
  rewrite ?node_21222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21224 (s : N.State) (i : N.Inputs) :
  R.v21224 (state s) (inputs i) = Zmod.unsigned (N.v21224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21224 s i)) at 1.
  unfold R.v21224, N.v21224.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21225 (s : N.State) (i : N.Inputs) :
  R.v21225 (state s) (inputs i) = Zmod.unsigned (N.v21225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21225 s i)) at 1.
  unfold R.v21225, N.v21225.
  unfold R.v16463, N.v16463.
  rewrite !state_r533_nr_5F533.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r533_nr_5F533 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21226 (s : N.State) (i : N.Inputs) :
  R.v21226 (state s) (inputs i) = Zmod.unsigned (N.v21226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21226 s i)) at 1.
  unfold R.v21226, N.v21226.
  unfold R.v6, N.v6.
  rewrite !state_r532_nr_5F532.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r532_nr_5F532 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21227 (s : N.State) (i : N.Inputs) :
  R.v21227 (state s) (inputs i) = Zmod.unsigned (N.v21227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21227 s i)) at 1.
  unfold R.v21227, N.v21227.
  unfold R.v6, N.v6.
  rewrite !state_r531_nr_5F531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r531_nr_5F531 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21228 (s : N.State) (i : N.Inputs) :
  R.v21228 (state s) (inputs i) = Zmod.unsigned (N.v21228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21228 s i)) at 1.
  unfold R.v21228, N.v21228.
  rewrite ?node_21226.
  rewrite ?node_21227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21229 (s : N.State) (i : N.Inputs) :
  R.v21229 (state s) (inputs i) = Zmod.unsigned (N.v21229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21229 s i)) at 1.
  unfold R.v21229, N.v21229.
  unfold R.v16484, N.v16484.
  rewrite ?node_21228.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21230 (s : N.State) (i : N.Inputs) :
  R.v21230 (state s) (inputs i) = Zmod.unsigned (N.v21230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21230 s i)) at 1.
  unfold R.v21230, N.v21230.
  rewrite ?node_21225.
  rewrite ?node_21229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21231 (s : N.State) (i : N.Inputs) :
  R.v21231 (state s) (inputs i) = Zmod.unsigned (N.v21231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21231 s i)) at 1.
  unfold R.v21231, N.v21231.
  unfold R.v6, N.v6.
  rewrite ?node_21230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21232 (s : N.State) (i : N.Inputs) :
  R.v21232 (state s) (inputs i) = Zmod.unsigned (N.v21232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21232 s i)) at 1.
  unfold R.v21232, N.v21232.
  rewrite ?node_7488.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21233 (s : N.State) (i : N.Inputs) :
  R.v21233 (state s) (inputs i) = Zmod.unsigned (N.v21233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21233 s i)) at 1.
  unfold R.v21233, N.v21233.
  unfold R.v6, N.v6.
  rewrite ?node_7603.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21234 (s : N.State) (i : N.Inputs) :
  R.v21234 (state s) (inputs i) = Zmod.unsigned (N.v21234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21234 s i)) at 1.
  unfold R.v21234, N.v21234.
  rewrite ?node_21232.
  rewrite ?node_21233.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21235 (s : N.State) (i : N.Inputs) :
  R.v21235 (state s) (inputs i) = Zmod.unsigned (N.v21235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21235 s i)) at 1.
  unfold R.v21235, N.v21235.
  rewrite ?node_21231.
  rewrite ?node_21234.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21236 (s : N.State) (i : N.Inputs) :
  R.v21236 (state s) (inputs i) = Zmod.unsigned (N.v21236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21236 s i)) at 1.
  unfold R.v21236, N.v21236.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21237 (s : N.State) (i : N.Inputs) :
  R.v21237 (state s) (inputs i) = Zmod.unsigned (N.v21237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21237 s i)) at 1.
  unfold R.v21237, N.v21237.
  rewrite ?node_7492.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21238 (s : N.State) (i : N.Inputs) :
  R.v21238 (state s) (inputs i) = Zmod.unsigned (N.v21238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21238 s i)) at 1.
  unfold R.v21238, N.v21238.
  unfold R.v6, N.v6.
  rewrite !state_r534_nr_5F534.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r534_nr_5F534 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21239 (s : N.State) (i : N.Inputs) :
  R.v21239 (state s) (inputs i) = Zmod.unsigned (N.v21239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21239 s i)) at 1.
  unfold R.v21239, N.v21239.
  unfold R.v6, N.v6.
  rewrite ?node_7488.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21240 (s : N.State) (i : N.Inputs) :
  R.v21240 (state s) (inputs i) = Zmod.unsigned (N.v21240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21240 s i)) at 1.
  unfold R.v21240, N.v21240.
  rewrite ?node_21238.
  rewrite ?node_21239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21241 (s : N.State) (i : N.Inputs) :
  R.v21241 (state s) (inputs i) = Zmod.unsigned (N.v21241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21241 s i)) at 1.
  unfold R.v21241, N.v21241.
  unfold R.v16484, N.v16484.
  rewrite ?node_21240.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21242 (s : N.State) (i : N.Inputs) :
  R.v21242 (state s) (inputs i) = Zmod.unsigned (N.v21242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21242 s i)) at 1.
  unfold R.v21242, N.v21242.
  rewrite ?node_21237.
  rewrite ?node_21241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21243 (s : N.State) (i : N.Inputs) :
  R.v21243 (state s) (inputs i) = Zmod.unsigned (N.v21243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21243 s i)) at 1.
  unfold R.v21243, N.v21243.
  unfold R.v6, N.v6.
  rewrite ?node_21242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21244 (s : N.State) (i : N.Inputs) :
  R.v21244 (state s) (inputs i) = Zmod.unsigned (N.v21244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21244 s i)) at 1.
  unfold R.v21244, N.v21244.
  rewrite ?node_7493.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21245 (s : N.State) (i : N.Inputs) :
  R.v21245 (state s) (inputs i) = Zmod.unsigned (N.v21245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21245 s i)) at 1.
  unfold R.v21245, N.v21245.
  unfold R.v6, N.v6.
  rewrite ?node_7643.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21246 (s : N.State) (i : N.Inputs) :
  R.v21246 (state s) (inputs i) = Zmod.unsigned (N.v21246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21246 s i)) at 1.
  unfold R.v21246, N.v21246.
  rewrite ?node_21244.
  rewrite ?node_21245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21247 (s : N.State) (i : N.Inputs) :
  R.v21247 (state s) (inputs i) = Zmod.unsigned (N.v21247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21247 s i)) at 1.
  unfold R.v21247, N.v21247.
  rewrite ?node_21243.
  rewrite ?node_21246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21248 (s : N.State) (i : N.Inputs) :
  R.v21248 (state s) (inputs i) = Zmod.unsigned (N.v21248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21248 s i)) at 1.
  unfold R.v21248, N.v21248.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21249 (s : N.State) (i : N.Inputs) :
  R.v21249 (state s) (inputs i) = Zmod.unsigned (N.v21249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21249 s i)) at 1.
  unfold R.v21249, N.v21249.
  rewrite ?node_7500.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21250 (s : N.State) (i : N.Inputs) :
  R.v21250 (state s) (inputs i) = Zmod.unsigned (N.v21250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21250 s i)) at 1.
  unfold R.v21250, N.v21250.
  unfold R.v16463, N.v16463.
  rewrite !state_r538_nr_5F538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r538_nr_5F538 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21251 (s : N.State) (i : N.Inputs) :
  R.v21251 (state s) (inputs i) = Zmod.unsigned (N.v21251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21251 s i)) at 1.
  unfold R.v21251, N.v21251.
  unfold R.v16463, N.v16463.
  rewrite !state_r537_nr_5F537.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r537_nr_5F537 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21252 (s : N.State) (i : N.Inputs) :
  R.v21252 (state s) (inputs i) = Zmod.unsigned (N.v21252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21252 s i)) at 1.
  unfold R.v21252, N.v21252.
  unfold R.v6, N.v6.
  rewrite !state_r536_nr_5F536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r536_nr_5F536 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21253 (s : N.State) (i : N.Inputs) :
  R.v21253 (state s) (inputs i) = Zmod.unsigned (N.v21253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21253 s i)) at 1.
  unfold R.v21253, N.v21253.
  unfold R.v6, N.v6.
  rewrite !state_r535_nr_5F535.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r535_nr_5F535 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21254 (s : N.State) (i : N.Inputs) :
  R.v21254 (state s) (inputs i) = Zmod.unsigned (N.v21254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21254 s i)) at 1.
  unfold R.v21254, N.v21254.
  rewrite ?node_21252.
  rewrite ?node_21253.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21255 (s : N.State) (i : N.Inputs) :
  R.v21255 (state s) (inputs i) = Zmod.unsigned (N.v21255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21255 s i)) at 1.
  unfold R.v21255, N.v21255.
  unfold R.v16484, N.v16484.
  rewrite ?node_21254.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21256 (s : N.State) (i : N.Inputs) :
  R.v21256 (state s) (inputs i) = Zmod.unsigned (N.v21256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21256 s i)) at 1.
  unfold R.v21256, N.v21256.
  rewrite ?node_21249.
  rewrite ?node_21250.
  rewrite ?node_21251.
  rewrite ?node_21255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21257 (s : N.State) (i : N.Inputs) :
  R.v21257 (state s) (inputs i) = Zmod.unsigned (N.v21257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21257 s i)) at 1.
  unfold R.v21257, N.v21257.
  unfold R.v6, N.v6.
  rewrite ?node_21256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21258 (s : N.State) (i : N.Inputs) :
  R.v21258 (state s) (inputs i) = Zmod.unsigned (N.v21258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21258 s i)) at 1.
  unfold R.v21258, N.v21258.
  rewrite ?node_7501.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21259 (s : N.State) (i : N.Inputs) :
  R.v21259 (state s) (inputs i) = Zmod.unsigned (N.v21259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21259 s i)) at 1.
  unfold R.v21259, N.v21259.
  unfold R.v6, N.v6.
  rewrite ?node_7611.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21260 (s : N.State) (i : N.Inputs) :
  R.v21260 (state s) (inputs i) = Zmod.unsigned (N.v21260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21260 s i)) at 1.
  unfold R.v21260, N.v21260.
  unfold R.v6, N.v6.
  rewrite ?node_7652.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21261 (s : N.State) (i : N.Inputs) :
  R.v21261 (state s) (inputs i) = Zmod.unsigned (N.v21261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21261 s i)) at 1.
  unfold R.v21261, N.v21261.
  rewrite ?node_21258.
  rewrite ?node_21259.
  rewrite ?node_21260.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21262 (s : N.State) (i : N.Inputs) :
  R.v21262 (state s) (inputs i) = Zmod.unsigned (N.v21262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21262 s i)) at 1.
  unfold R.v21262, N.v21262.
  rewrite ?node_21257.
  rewrite ?node_21261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21263 (s : N.State) (i : N.Inputs) :
  R.v21263 (state s) (inputs i) = Zmod.unsigned (N.v21263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21263 s i)) at 1.
  unfold R.v21263, N.v21263.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21264 (s : N.State) (i : N.Inputs) :
  R.v21264 (state s) (inputs i) = Zmod.unsigned (N.v21264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21264 s i)) at 1.
  unfold R.v21264, N.v21264.
  unfold R.v16463, N.v16463.
  rewrite !state_r537_nr_5F537.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r537_nr_5F537 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21265 (s : N.State) (i : N.Inputs) :
  R.v21265 (state s) (inputs i) = Zmod.unsigned (N.v21265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21265 s i)) at 1.
  unfold R.v21265, N.v21265.
  unfold R.v6, N.v6.
  rewrite !state_r536_nr_5F536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r536_nr_5F536 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21266 (s : N.State) (i : N.Inputs) :
  R.v21266 (state s) (inputs i) = Zmod.unsigned (N.v21266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21266 s i)) at 1.
  unfold R.v21266, N.v21266.
  unfold R.v6, N.v6.
  rewrite !state_r535_nr_5F535.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r535_nr_5F535 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21267 (s : N.State) (i : N.Inputs) :
  R.v21267 (state s) (inputs i) = Zmod.unsigned (N.v21267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21267 s i)) at 1.
  unfold R.v21267, N.v21267.
  rewrite ?node_21265.
  rewrite ?node_21266.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21268 (s : N.State) (i : N.Inputs) :
  R.v21268 (state s) (inputs i) = Zmod.unsigned (N.v21268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21268 s i)) at 1.
  unfold R.v21268, N.v21268.
  unfold R.v16484, N.v16484.
  rewrite ?node_21267.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21269 (s : N.State) (i : N.Inputs) :
  R.v21269 (state s) (inputs i) = Zmod.unsigned (N.v21269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21269 s i)) at 1.
  unfold R.v21269, N.v21269.
  rewrite ?node_21264.
  rewrite ?node_21268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21270 (s : N.State) (i : N.Inputs) :
  R.v21270 (state s) (inputs i) = Zmod.unsigned (N.v21270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21270 s i)) at 1.
  unfold R.v21270, N.v21270.
  unfold R.v6, N.v6.
  rewrite ?node_21269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21271 (s : N.State) (i : N.Inputs) :
  R.v21271 (state s) (inputs i) = Zmod.unsigned (N.v21271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21271 s i)) at 1.
  unfold R.v21271, N.v21271.
  rewrite ?node_7496.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21272 (s : N.State) (i : N.Inputs) :
  R.v21272 (state s) (inputs i) = Zmod.unsigned (N.v21272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21272 s i)) at 1.
  unfold R.v21272, N.v21272.
  unfold R.v6, N.v6.
  rewrite ?node_7611.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21273 (s : N.State) (i : N.Inputs) :
  R.v21273 (state s) (inputs i) = Zmod.unsigned (N.v21273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21273 s i)) at 1.
  unfold R.v21273, N.v21273.
  rewrite ?node_21271.
  rewrite ?node_21272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21274 (s : N.State) (i : N.Inputs) :
  R.v21274 (state s) (inputs i) = Zmod.unsigned (N.v21274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21274 s i)) at 1.
  unfold R.v21274, N.v21274.
  rewrite ?node_21270.
  rewrite ?node_21273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21275 (s : N.State) (i : N.Inputs) :
  R.v21275 (state s) (inputs i) = Zmod.unsigned (N.v21275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21275 s i)) at 1.
  unfold R.v21275, N.v21275.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21276 (s : N.State) (i : N.Inputs) :
  R.v21276 (state s) (inputs i) = Zmod.unsigned (N.v21276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21276 s i)) at 1.
  unfold R.v21276, N.v21276.
  rewrite ?node_7500.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21277 (s : N.State) (i : N.Inputs) :
  R.v21277 (state s) (inputs i) = Zmod.unsigned (N.v21277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21277 s i)) at 1.
  unfold R.v21277, N.v21277.
  unfold R.v6, N.v6.
  rewrite !state_r538_nr_5F538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r538_nr_5F538 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21278 (s : N.State) (i : N.Inputs) :
  R.v21278 (state s) (inputs i) = Zmod.unsigned (N.v21278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21278 s i)) at 1.
  unfold R.v21278, N.v21278.
  unfold R.v6, N.v6.
  rewrite ?node_7496.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21279 (s : N.State) (i : N.Inputs) :
  R.v21279 (state s) (inputs i) = Zmod.unsigned (N.v21279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21279 s i)) at 1.
  unfold R.v21279, N.v21279.
  rewrite ?node_21277.
  rewrite ?node_21278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21280 (s : N.State) (i : N.Inputs) :
  R.v21280 (state s) (inputs i) = Zmod.unsigned (N.v21280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21280 s i)) at 1.
  unfold R.v21280, N.v21280.
  unfold R.v16484, N.v16484.
  rewrite ?node_21279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21281 (s : N.State) (i : N.Inputs) :
  R.v21281 (state s) (inputs i) = Zmod.unsigned (N.v21281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21281 s i)) at 1.
  unfold R.v21281, N.v21281.
  rewrite ?node_21276.
  rewrite ?node_21280.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21282 (s : N.State) (i : N.Inputs) :
  R.v21282 (state s) (inputs i) = Zmod.unsigned (N.v21282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21282 s i)) at 1.
  unfold R.v21282, N.v21282.
  unfold R.v6, N.v6.
  rewrite ?node_21281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21283 (s : N.State) (i : N.Inputs) :
  R.v21283 (state s) (inputs i) = Zmod.unsigned (N.v21283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21283 s i)) at 1.
  unfold R.v21283, N.v21283.
  rewrite ?node_7501.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21284 (s : N.State) (i : N.Inputs) :
  R.v21284 (state s) (inputs i) = Zmod.unsigned (N.v21284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21284 s i)) at 1.
  unfold R.v21284, N.v21284.
  unfold R.v6, N.v6.
  rewrite ?node_7652.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21285 (s : N.State) (i : N.Inputs) :
  R.v21285 (state s) (inputs i) = Zmod.unsigned (N.v21285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21285 s i)) at 1.
  unfold R.v21285, N.v21285.
  rewrite ?node_21283.
  rewrite ?node_21284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21286 (s : N.State) (i : N.Inputs) :
  R.v21286 (state s) (inputs i) = Zmod.unsigned (N.v21286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21286 s i)) at 1.
  unfold R.v21286, N.v21286.
  rewrite ?node_21282.
  rewrite ?node_21285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21287 (s : N.State) (i : N.Inputs) :
  R.v21287 (state s) (inputs i) = Zmod.unsigned (N.v21287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21287 s i)) at 1.
  unfold R.v21287, N.v21287.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21288 (s : N.State) (i : N.Inputs) :
  R.v21288 (state s) (inputs i) = Zmod.unsigned (N.v21288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21288 s i)) at 1.
  unfold R.v21288, N.v21288.
  rewrite ?node_7508.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21289 (s : N.State) (i : N.Inputs) :
  R.v21289 (state s) (inputs i) = Zmod.unsigned (N.v21289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21289 s i)) at 1.
  unfold R.v21289, N.v21289.
  unfold R.v16463, N.v16463.
  rewrite !state_r542_nr_5F542.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r542_nr_5F542 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21290 (s : N.State) (i : N.Inputs) :
  R.v21290 (state s) (inputs i) = Zmod.unsigned (N.v21290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21290 s i)) at 1.
  unfold R.v21290, N.v21290.
  unfold R.v16463, N.v16463.
  rewrite !state_r541_nr_5F541.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r541_nr_5F541 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21291 (s : N.State) (i : N.Inputs) :
  R.v21291 (state s) (inputs i) = Zmod.unsigned (N.v21291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21291 s i)) at 1.
  unfold R.v21291, N.v21291.
  unfold R.v6, N.v6.
  rewrite !state_r540_nr_5F540.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r540_nr_5F540 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21292 (s : N.State) (i : N.Inputs) :
  R.v21292 (state s) (inputs i) = Zmod.unsigned (N.v21292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21292 s i)) at 1.
  unfold R.v21292, N.v21292.
  unfold R.v6, N.v6.
  rewrite !state_r539_nr_5F539.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r539_nr_5F539 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21293 (s : N.State) (i : N.Inputs) :
  R.v21293 (state s) (inputs i) = Zmod.unsigned (N.v21293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21293 s i)) at 1.
  unfold R.v21293, N.v21293.
  rewrite ?node_21291.
  rewrite ?node_21292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21294 (s : N.State) (i : N.Inputs) :
  R.v21294 (state s) (inputs i) = Zmod.unsigned (N.v21294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21294 s i)) at 1.
  unfold R.v21294, N.v21294.
  unfold R.v16484, N.v16484.
  rewrite ?node_21293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21295 (s : N.State) (i : N.Inputs) :
  R.v21295 (state s) (inputs i) = Zmod.unsigned (N.v21295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21295 s i)) at 1.
  unfold R.v21295, N.v21295.
  rewrite ?node_21288.
  rewrite ?node_21289.
  rewrite ?node_21290.
  rewrite ?node_21294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21296 (s : N.State) (i : N.Inputs) :
  R.v21296 (state s) (inputs i) = Zmod.unsigned (N.v21296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21296 s i)) at 1.
  unfold R.v21296, N.v21296.
  unfold R.v6, N.v6.
  rewrite ?node_21295.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21297 (s : N.State) (i : N.Inputs) :
  R.v21297 (state s) (inputs i) = Zmod.unsigned (N.v21297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21297 s i)) at 1.
  unfold R.v21297, N.v21297.
  rewrite ?node_7509.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21298 (s : N.State) (i : N.Inputs) :
  R.v21298 (state s) (inputs i) = Zmod.unsigned (N.v21298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21298 s i)) at 1.
  unfold R.v21298, N.v21298.
  unfold R.v6, N.v6.
  rewrite ?node_7619.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21299 (s : N.State) (i : N.Inputs) :
  R.v21299 (state s) (inputs i) = Zmod.unsigned (N.v21299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21299 s i)) at 1.
  unfold R.v21299, N.v21299.
  unfold R.v6, N.v6.
  rewrite ?node_7655.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21300 (s : N.State) (i : N.Inputs) :
  R.v21300 (state s) (inputs i) = Zmod.unsigned (N.v21300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21300 s i)) at 1.
  unfold R.v21300, N.v21300.
  rewrite ?node_21297.
  rewrite ?node_21298.
  rewrite ?node_21299.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21301 (s : N.State) (i : N.Inputs) :
  R.v21301 (state s) (inputs i) = Zmod.unsigned (N.v21301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21301 s i)) at 1.
  unfold R.v21301, N.v21301.
  rewrite ?node_21296.
  rewrite ?node_21300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21302 (s : N.State) (i : N.Inputs) :
  R.v21302 (state s) (inputs i) = Zmod.unsigned (N.v21302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21302 s i)) at 1.
  unfold R.v21302, N.v21302.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21303 (s : N.State) (i : N.Inputs) :
  R.v21303 (state s) (inputs i) = Zmod.unsigned (N.v21303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21303 s i)) at 1.
  unfold R.v21303, N.v21303.
  unfold R.v16463, N.v16463.
  rewrite !state_r541_nr_5F541.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r541_nr_5F541 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21304 (s : N.State) (i : N.Inputs) :
  R.v21304 (state s) (inputs i) = Zmod.unsigned (N.v21304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21304 s i)) at 1.
  unfold R.v21304, N.v21304.
  unfold R.v6, N.v6.
  rewrite !state_r540_nr_5F540.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r540_nr_5F540 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21305 (s : N.State) (i : N.Inputs) :
  R.v21305 (state s) (inputs i) = Zmod.unsigned (N.v21305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21305 s i)) at 1.
  unfold R.v21305, N.v21305.
  unfold R.v6, N.v6.
  rewrite !state_r539_nr_5F539.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r539_nr_5F539 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21306 (s : N.State) (i : N.Inputs) :
  R.v21306 (state s) (inputs i) = Zmod.unsigned (N.v21306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21306 s i)) at 1.
  unfold R.v21306, N.v21306.
  rewrite ?node_21304.
  rewrite ?node_21305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21307 (s : N.State) (i : N.Inputs) :
  R.v21307 (state s) (inputs i) = Zmod.unsigned (N.v21307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21307 s i)) at 1.
  unfold R.v21307, N.v21307.
  unfold R.v16484, N.v16484.
  rewrite ?node_21306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21308 (s : N.State) (i : N.Inputs) :
  R.v21308 (state s) (inputs i) = Zmod.unsigned (N.v21308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21308 s i)) at 1.
  unfold R.v21308, N.v21308.
  rewrite ?node_21303.
  rewrite ?node_21307.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21309 (s : N.State) (i : N.Inputs) :
  R.v21309 (state s) (inputs i) = Zmod.unsigned (N.v21309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21309 s i)) at 1.
  unfold R.v21309, N.v21309.
  unfold R.v6, N.v6.
  rewrite ?node_21308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21310 (s : N.State) (i : N.Inputs) :
  R.v21310 (state s) (inputs i) = Zmod.unsigned (N.v21310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21310 s i)) at 1.
  unfold R.v21310, N.v21310.
  rewrite ?node_7504.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21311 (s : N.State) (i : N.Inputs) :
  R.v21311 (state s) (inputs i) = Zmod.unsigned (N.v21311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21311 s i)) at 1.
  unfold R.v21311, N.v21311.
  unfold R.v6, N.v6.
  rewrite ?node_7619.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21312 (s : N.State) (i : N.Inputs) :
  R.v21312 (state s) (inputs i) = Zmod.unsigned (N.v21312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21312 s i)) at 1.
  unfold R.v21312, N.v21312.
  rewrite ?node_21310.
  rewrite ?node_21311.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21313 (s : N.State) (i : N.Inputs) :
  R.v21313 (state s) (inputs i) = Zmod.unsigned (N.v21313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21313 s i)) at 1.
  unfold R.v21313, N.v21313.
  rewrite ?node_21309.
  rewrite ?node_21312.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21314 (s : N.State) (i : N.Inputs) :
  R.v21314 (state s) (inputs i) = Zmod.unsigned (N.v21314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21314 s i)) at 1.
  unfold R.v21314, N.v21314.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21315 (s : N.State) (i : N.Inputs) :
  R.v21315 (state s) (inputs i) = Zmod.unsigned (N.v21315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21315 s i)) at 1.
  unfold R.v21315, N.v21315.
  rewrite ?node_7508.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21316 (s : N.State) (i : N.Inputs) :
  R.v21316 (state s) (inputs i) = Zmod.unsigned (N.v21316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21316 s i)) at 1.
  unfold R.v21316, N.v21316.
  unfold R.v6, N.v6.
  rewrite !state_r542_nr_5F542.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r542_nr_5F542 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21317 (s : N.State) (i : N.Inputs) :
  R.v21317 (state s) (inputs i) = Zmod.unsigned (N.v21317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21317 s i)) at 1.
  unfold R.v21317, N.v21317.
  unfold R.v6, N.v6.
  rewrite ?node_7504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21318 (s : N.State) (i : N.Inputs) :
  R.v21318 (state s) (inputs i) = Zmod.unsigned (N.v21318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21318 s i)) at 1.
  unfold R.v21318, N.v21318.
  rewrite ?node_21316.
  rewrite ?node_21317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21319 (s : N.State) (i : N.Inputs) :
  R.v21319 (state s) (inputs i) = Zmod.unsigned (N.v21319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21319 s i)) at 1.
  unfold R.v21319, N.v21319.
  unfold R.v16484, N.v16484.
  rewrite ?node_21318.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21320 (s : N.State) (i : N.Inputs) :
  R.v21320 (state s) (inputs i) = Zmod.unsigned (N.v21320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21320 s i)) at 1.
  unfold R.v21320, N.v21320.
  rewrite ?node_21315.
  rewrite ?node_21319.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21321 (s : N.State) (i : N.Inputs) :
  R.v21321 (state s) (inputs i) = Zmod.unsigned (N.v21321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21321 s i)) at 1.
  unfold R.v21321, N.v21321.
  unfold R.v6, N.v6.
  rewrite ?node_21320.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21322 (s : N.State) (i : N.Inputs) :
  R.v21322 (state s) (inputs i) = Zmod.unsigned (N.v21322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21322 s i)) at 1.
  unfold R.v21322, N.v21322.
  rewrite ?node_7509.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21323 (s : N.State) (i : N.Inputs) :
  R.v21323 (state s) (inputs i) = Zmod.unsigned (N.v21323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21323 s i)) at 1.
  unfold R.v21323, N.v21323.
  unfold R.v6, N.v6.
  rewrite ?node_7655.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21324 (s : N.State) (i : N.Inputs) :
  R.v21324 (state s) (inputs i) = Zmod.unsigned (N.v21324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21324 s i)) at 1.
  unfold R.v21324, N.v21324.
  rewrite ?node_21322.
  rewrite ?node_21323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21325 (s : N.State) (i : N.Inputs) :
  R.v21325 (state s) (inputs i) = Zmod.unsigned (N.v21325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21325 s i)) at 1.
  unfold R.v21325, N.v21325.
  rewrite ?node_21321.
  rewrite ?node_21324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21326 (s : N.State) (i : N.Inputs) :
  R.v21326 (state s) (inputs i) = Zmod.unsigned (N.v21326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21326 s i)) at 1.
  unfold R.v21326, N.v21326.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21327 (s : N.State) (i : N.Inputs) :
  R.v21327 (state s) (inputs i) = Zmod.unsigned (N.v21327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21327 s i)) at 1.
  unfold R.v21327, N.v21327.
  rewrite ?node_7520.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21328 (s : N.State) (i : N.Inputs) :
  R.v21328 (state s) (inputs i) = Zmod.unsigned (N.v21328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21328 s i)) at 1.
  unfold R.v21328, N.v21328.
  unfold R.v16463, N.v16463.
  rewrite !state_r546_nr_5F546.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r546_nr_5F546 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21329 (s : N.State) (i : N.Inputs) :
  R.v21329 (state s) (inputs i) = Zmod.unsigned (N.v21329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21329 s i)) at 1.
  unfold R.v21329, N.v21329.
  unfold R.v16463, N.v16463.
  rewrite !state_r545_nr_5F545.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r545_nr_5F545 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21330 (s : N.State) (i : N.Inputs) :
  R.v21330 (state s) (inputs i) = Zmod.unsigned (N.v21330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21330 s i)) at 1.
  unfold R.v21330, N.v21330.
  unfold R.v6, N.v6.
  rewrite !state_r544_nr_5F544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r544_nr_5F544 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21331 (s : N.State) (i : N.Inputs) :
  R.v21331 (state s) (inputs i) = Zmod.unsigned (N.v21331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21331 s i)) at 1.
  unfold R.v21331, N.v21331.
  unfold R.v6, N.v6.
  rewrite !state_r543_nr_5F543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r543_nr_5F543 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21332 (s : N.State) (i : N.Inputs) :
  R.v21332 (state s) (inputs i) = Zmod.unsigned (N.v21332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21332 s i)) at 1.
  unfold R.v21332, N.v21332.
  rewrite ?node_21330.
  rewrite ?node_21331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21333 (s : N.State) (i : N.Inputs) :
  R.v21333 (state s) (inputs i) = Zmod.unsigned (N.v21333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21333 s i)) at 1.
  unfold R.v21333, N.v21333.
  unfold R.v16484, N.v16484.
  rewrite ?node_21332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21334 (s : N.State) (i : N.Inputs) :
  R.v21334 (state s) (inputs i) = Zmod.unsigned (N.v21334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21334 s i)) at 1.
  unfold R.v21334, N.v21334.
  rewrite ?node_21327.
  rewrite ?node_21328.
  rewrite ?node_21329.
  rewrite ?node_21333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21335 (s : N.State) (i : N.Inputs) :
  R.v21335 (state s) (inputs i) = Zmod.unsigned (N.v21335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21335 s i)) at 1.
  unfold R.v21335, N.v21335.
  unfold R.v6, N.v6.
  rewrite ?node_21334.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21336 (s : N.State) (i : N.Inputs) :
  R.v21336 (state s) (inputs i) = Zmod.unsigned (N.v21336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21336 s i)) at 1.
  unfold R.v21336, N.v21336.
  rewrite ?node_7521.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21337 (s : N.State) (i : N.Inputs) :
  R.v21337 (state s) (inputs i) = Zmod.unsigned (N.v21337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21337 s i)) at 1.
  unfold R.v21337, N.v21337.
  unfold R.v6, N.v6.
  rewrite ?node_7631.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21338 (s : N.State) (i : N.Inputs) :
  R.v21338 (state s) (inputs i) = Zmod.unsigned (N.v21338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21338 s i)) at 1.
  unfold R.v21338, N.v21338.
  unfold R.v6, N.v6.
  rewrite ?node_7659.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21339 (s : N.State) (i : N.Inputs) :
  R.v21339 (state s) (inputs i) = Zmod.unsigned (N.v21339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21339 s i)) at 1.
  unfold R.v21339, N.v21339.
  rewrite ?node_21336.
  rewrite ?node_21337.
  rewrite ?node_21338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21340 (s : N.State) (i : N.Inputs) :
  R.v21340 (state s) (inputs i) = Zmod.unsigned (N.v21340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21340 s i)) at 1.
  unfold R.v21340, N.v21340.
  rewrite ?node_21335.
  rewrite ?node_21339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21341 (s : N.State) (i : N.Inputs) :
  R.v21341 (state s) (inputs i) = Zmod.unsigned (N.v21341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21341 s i)) at 1.
  unfold R.v21341, N.v21341.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21342 (s : N.State) (i : N.Inputs) :
  R.v21342 (state s) (inputs i) = Zmod.unsigned (N.v21342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21342 s i)) at 1.
  unfold R.v21342, N.v21342.
  unfold R.v16463, N.v16463.
  rewrite !state_r545_nr_5F545.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r545_nr_5F545 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21343 (s : N.State) (i : N.Inputs) :
  R.v21343 (state s) (inputs i) = Zmod.unsigned (N.v21343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21343 s i)) at 1.
  unfold R.v21343, N.v21343.
  unfold R.v6, N.v6.
  rewrite !state_r544_nr_5F544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r544_nr_5F544 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21344 (s : N.State) (i : N.Inputs) :
  R.v21344 (state s) (inputs i) = Zmod.unsigned (N.v21344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21344 s i)) at 1.
  unfold R.v21344, N.v21344.
  unfold R.v6, N.v6.
  rewrite !state_r543_nr_5F543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r543_nr_5F543 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21345 (s : N.State) (i : N.Inputs) :
  R.v21345 (state s) (inputs i) = Zmod.unsigned (N.v21345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21345 s i)) at 1.
  unfold R.v21345, N.v21345.
  rewrite ?node_21343.
  rewrite ?node_21344.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21346 (s : N.State) (i : N.Inputs) :
  R.v21346 (state s) (inputs i) = Zmod.unsigned (N.v21346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21346 s i)) at 1.
  unfold R.v21346, N.v21346.
  unfold R.v16484, N.v16484.
  rewrite ?node_21345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21347 (s : N.State) (i : N.Inputs) :
  R.v21347 (state s) (inputs i) = Zmod.unsigned (N.v21347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21347 s i)) at 1.
  unfold R.v21347, N.v21347.
  rewrite ?node_21342.
  rewrite ?node_21346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21348 (s : N.State) (i : N.Inputs) :
  R.v21348 (state s) (inputs i) = Zmod.unsigned (N.v21348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21348 s i)) at 1.
  unfold R.v21348, N.v21348.
  unfold R.v6, N.v6.
  rewrite ?node_21347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21349 (s : N.State) (i : N.Inputs) :
  R.v21349 (state s) (inputs i) = Zmod.unsigned (N.v21349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21349 s i)) at 1.
  unfold R.v21349, N.v21349.
  rewrite ?node_7516.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21350 (s : N.State) (i : N.Inputs) :
  R.v21350 (state s) (inputs i) = Zmod.unsigned (N.v21350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21350 s i)) at 1.
  unfold R.v21350, N.v21350.
  unfold R.v6, N.v6.
  rewrite ?node_7631.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21351 (s : N.State) (i : N.Inputs) :
  R.v21351 (state s) (inputs i) = Zmod.unsigned (N.v21351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21351 s i)) at 1.
  unfold R.v21351, N.v21351.
  rewrite ?node_21349.
  rewrite ?node_21350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21352 (s : N.State) (i : N.Inputs) :
  R.v21352 (state s) (inputs i) = Zmod.unsigned (N.v21352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21352 s i)) at 1.
  unfold R.v21352, N.v21352.
  rewrite ?node_21348.
  rewrite ?node_21351.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21353 (s : N.State) (i : N.Inputs) :
  R.v21353 (state s) (inputs i) = Zmod.unsigned (N.v21353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21353 s i)) at 1.
  unfold R.v21353, N.v21353.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21354 (s : N.State) (i : N.Inputs) :
  R.v21354 (state s) (inputs i) = Zmod.unsigned (N.v21354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21354 s i)) at 1.
  unfold R.v21354, N.v21354.
  rewrite ?node_7520.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21355 (s : N.State) (i : N.Inputs) :
  R.v21355 (state s) (inputs i) = Zmod.unsigned (N.v21355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21355 s i)) at 1.
  unfold R.v21355, N.v21355.
  unfold R.v6, N.v6.
  rewrite !state_r546_nr_5F546.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r546_nr_5F546 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21356 (s : N.State) (i : N.Inputs) :
  R.v21356 (state s) (inputs i) = Zmod.unsigned (N.v21356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21356 s i)) at 1.
  unfold R.v21356, N.v21356.
  unfold R.v6, N.v6.
  rewrite ?node_7516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21357 (s : N.State) (i : N.Inputs) :
  R.v21357 (state s) (inputs i) = Zmod.unsigned (N.v21357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21357 s i)) at 1.
  unfold R.v21357, N.v21357.
  rewrite ?node_21355.
  rewrite ?node_21356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21358 (s : N.State) (i : N.Inputs) :
  R.v21358 (state s) (inputs i) = Zmod.unsigned (N.v21358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21358 s i)) at 1.
  unfold R.v21358, N.v21358.
  unfold R.v16484, N.v16484.
  rewrite ?node_21357.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21359 (s : N.State) (i : N.Inputs) :
  R.v21359 (state s) (inputs i) = Zmod.unsigned (N.v21359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21359 s i)) at 1.
  unfold R.v21359, N.v21359.
  rewrite ?node_21354.
  rewrite ?node_21358.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21360 (s : N.State) (i : N.Inputs) :
  R.v21360 (state s) (inputs i) = Zmod.unsigned (N.v21360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21360 s i)) at 1.
  unfold R.v21360, N.v21360.
  unfold R.v6, N.v6.
  rewrite ?node_21359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21361 (s : N.State) (i : N.Inputs) :
  R.v21361 (state s) (inputs i) = Zmod.unsigned (N.v21361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21361 s i)) at 1.
  unfold R.v21361, N.v21361.
  rewrite ?node_7521.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21362 (s : N.State) (i : N.Inputs) :
  R.v21362 (state s) (inputs i) = Zmod.unsigned (N.v21362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21362 s i)) at 1.
  unfold R.v21362, N.v21362.
  unfold R.v6, N.v6.
  rewrite ?node_7659.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21363 (s : N.State) (i : N.Inputs) :
  R.v21363 (state s) (inputs i) = Zmod.unsigned (N.v21363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21363 s i)) at 1.
  unfold R.v21363, N.v21363.
  rewrite ?node_21361.
  rewrite ?node_21362.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21364 (s : N.State) (i : N.Inputs) :
  R.v21364 (state s) (inputs i) = Zmod.unsigned (N.v21364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21364 s i)) at 1.
  unfold R.v21364, N.v21364.
  rewrite ?node_21360.
  rewrite ?node_21363.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21365 (s : N.State) (i : N.Inputs) :
  R.v21365 (state s) (inputs i) = Zmod.unsigned (N.v21365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21365 s i)) at 1.
  unfold R.v21365, N.v21365.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21366 (s : N.State) (i : N.Inputs) :
  R.v21366 (state s) (inputs i) = Zmod.unsigned (N.v21366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21366 s i)) at 1.
  unfold R.v21366, N.v21366.
  unfold R.v16463, N.v16463.
  rewrite !state_r549_nr_5F549.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r549_nr_5F549 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21367 (s : N.State) (i : N.Inputs) :
  R.v21367 (state s) (inputs i) = Zmod.unsigned (N.v21367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21367 s i)) at 1.
  unfold R.v21367, N.v21367.
  unfold R.v6, N.v6.
  rewrite !state_r548_nr_5F548.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r548_nr_5F548 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21368 (s : N.State) (i : N.Inputs) :
  R.v21368 (state s) (inputs i) = Zmod.unsigned (N.v21368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21368 s i)) at 1.
  unfold R.v21368, N.v21368.
  unfold R.v6, N.v6.
  rewrite !state_r547_nr_5F547.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r547_nr_5F547 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21369 (s : N.State) (i : N.Inputs) :
  R.v21369 (state s) (inputs i) = Zmod.unsigned (N.v21369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21369 s i)) at 1.
  unfold R.v21369, N.v21369.
  rewrite ?node_21367.
  rewrite ?node_21368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21370 (s : N.State) (i : N.Inputs) :
  R.v21370 (state s) (inputs i) = Zmod.unsigned (N.v21370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21370 s i)) at 1.
  unfold R.v21370, N.v21370.
  unfold R.v16484, N.v16484.
  rewrite ?node_21369.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21371 (s : N.State) (i : N.Inputs) :
  R.v21371 (state s) (inputs i) = Zmod.unsigned (N.v21371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21371 s i)) at 1.
  unfold R.v21371, N.v21371.
  rewrite ?node_21366.
  rewrite ?node_21370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21372 (s : N.State) (i : N.Inputs) :
  R.v21372 (state s) (inputs i) = Zmod.unsigned (N.v21372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21372 s i)) at 1.
  unfold R.v21372, N.v21372.
  unfold R.v6, N.v6.
  rewrite ?node_21371.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21373 (s : N.State) (i : N.Inputs) :
  R.v21373 (state s) (inputs i) = Zmod.unsigned (N.v21373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21373 s i)) at 1.
  unfold R.v21373, N.v21373.
  rewrite ?node_7523.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21374 (s : N.State) (i : N.Inputs) :
  R.v21374 (state s) (inputs i) = Zmod.unsigned (N.v21374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21374 s i)) at 1.
  unfold R.v21374, N.v21374.
  unfold R.v6, N.v6.
  rewrite ?node_7663.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21375 (s : N.State) (i : N.Inputs) :
  R.v21375 (state s) (inputs i) = Zmod.unsigned (N.v21375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21375 s i)) at 1.
  unfold R.v21375, N.v21375.
  rewrite ?node_21373.
  rewrite ?node_21374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21376 (s : N.State) (i : N.Inputs) :
  R.v21376 (state s) (inputs i) = Zmod.unsigned (N.v21376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21376 s i)) at 1.
  unfold R.v21376, N.v21376.
  rewrite ?node_21372.
  rewrite ?node_21375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21377 (s : N.State) (i : N.Inputs) :
  R.v21377 (state s) (inputs i) = Zmod.unsigned (N.v21377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21377 s i)) at 1.
  unfold R.v21377, N.v21377.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21378 (s : N.State) (i : N.Inputs) :
  R.v21378 (state s) (inputs i) = Zmod.unsigned (N.v21378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21378 s i)) at 1.
  unfold R.v21378, N.v21378.
  rewrite ?node_7596.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21379 (s : N.State) (i : N.Inputs) :
  R.v21379 (state s) (inputs i) = Zmod.unsigned (N.v21379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21379 s i)) at 1.
  unfold R.v21379, N.v21379.
  unfold R.v16463, N.v16463.
  rewrite !state_r553_nr_5F553.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r553_nr_5F553 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21380 (s : N.State) (i : N.Inputs) :
  R.v21380 (state s) (inputs i) = Zmod.unsigned (N.v21380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21380 s i)) at 1.
  unfold R.v21380, N.v21380.
  unfold R.v16463, N.v16463.
  rewrite !state_r552_nr_5F552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r552_nr_5F552 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21381 (s : N.State) (i : N.Inputs) :
  R.v21381 (state s) (inputs i) = Zmod.unsigned (N.v21381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21381 s i)) at 1.
  unfold R.v21381, N.v21381.
  unfold R.v6, N.v6.
  rewrite !state_r551_nr_5F551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r551_nr_5F551 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21382 (s : N.State) (i : N.Inputs) :
  R.v21382 (state s) (inputs i) = Zmod.unsigned (N.v21382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21382 s i)) at 1.
  unfold R.v21382, N.v21382.
  unfold R.v6, N.v6.
  rewrite !state_r550_nr_5F550.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r550_nr_5F550 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21383 (s : N.State) (i : N.Inputs) :
  R.v21383 (state s) (inputs i) = Zmod.unsigned (N.v21383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21383 s i)) at 1.
  unfold R.v21383, N.v21383.
  rewrite ?node_21381.
  rewrite ?node_21382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21384 (s : N.State) (i : N.Inputs) :
  R.v21384 (state s) (inputs i) = Zmod.unsigned (N.v21384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21384 s i)) at 1.
  unfold R.v21384, N.v21384.
  unfold R.v16484, N.v16484.
  rewrite ?node_21383.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21385 (s : N.State) (i : N.Inputs) :
  R.v21385 (state s) (inputs i) = Zmod.unsigned (N.v21385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21385 s i)) at 1.
  unfold R.v21385, N.v21385.
  rewrite ?node_21378.
  rewrite ?node_21379.
  rewrite ?node_21380.
  rewrite ?node_21384.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21386 (s : N.State) (i : N.Inputs) :
  R.v21386 (state s) (inputs i) = Zmod.unsigned (N.v21386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21386 s i)) at 1.
  unfold R.v21386, N.v21386.
  unfold R.v6, N.v6.
  rewrite ?node_21385.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21387 (s : N.State) (i : N.Inputs) :
  R.v21387 (state s) (inputs i) = Zmod.unsigned (N.v21387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21387 s i)) at 1.
  unfold R.v21387, N.v21387.
  rewrite ?node_7597.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21388 (s : N.State) (i : N.Inputs) :
  R.v21388 (state s) (inputs i) = Zmod.unsigned (N.v21388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21388 s i)) at 1.
  unfold R.v21388, N.v21388.
  unfold R.v6, N.v6.
  rewrite ?node_7708.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21389 (s : N.State) (i : N.Inputs) :
  R.v21389 (state s) (inputs i) = Zmod.unsigned (N.v21389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21389 s i)) at 1.
  unfold R.v21389, N.v21389.
  unfold R.v6, N.v6.
  rewrite ?node_7755.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21390 (s : N.State) (i : N.Inputs) :
  R.v21390 (state s) (inputs i) = Zmod.unsigned (N.v21390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21390 s i)) at 1.
  unfold R.v21390, N.v21390.
  rewrite ?node_21387.
  rewrite ?node_21388.
  rewrite ?node_21389.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21391 (s : N.State) (i : N.Inputs) :
  R.v21391 (state s) (inputs i) = Zmod.unsigned (N.v21391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21391 s i)) at 1.
  unfold R.v21391, N.v21391.
  rewrite ?node_21386.
  rewrite ?node_21390.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21392 (s : N.State) (i : N.Inputs) :
  R.v21392 (state s) (inputs i) = Zmod.unsigned (N.v21392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21392 s i)) at 1.
  unfold R.v21392, N.v21392.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21393 (s : N.State) (i : N.Inputs) :
  R.v21393 (state s) (inputs i) = Zmod.unsigned (N.v21393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21393 s i)) at 1.
  unfold R.v21393, N.v21393.
  unfold R.v16463, N.v16463.
  rewrite !state_r552_nr_5F552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r552_nr_5F552 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21394 (s : N.State) (i : N.Inputs) :
  R.v21394 (state s) (inputs i) = Zmod.unsigned (N.v21394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21394 s i)) at 1.
  unfold R.v21394, N.v21394.
  unfold R.v6, N.v6.
  rewrite !state_r551_nr_5F551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r551_nr_5F551 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21395 (s : N.State) (i : N.Inputs) :
  R.v21395 (state s) (inputs i) = Zmod.unsigned (N.v21395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21395 s i)) at 1.
  unfold R.v21395, N.v21395.
  unfold R.v6, N.v6.
  rewrite !state_r550_nr_5F550.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r550_nr_5F550 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21396 (s : N.State) (i : N.Inputs) :
  R.v21396 (state s) (inputs i) = Zmod.unsigned (N.v21396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21396 s i)) at 1.
  unfold R.v21396, N.v21396.
  rewrite ?node_21394.
  rewrite ?node_21395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21397 (s : N.State) (i : N.Inputs) :
  R.v21397 (state s) (inputs i) = Zmod.unsigned (N.v21397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21397 s i)) at 1.
  unfold R.v21397, N.v21397.
  unfold R.v16484, N.v16484.
  rewrite ?node_21396.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21398 (s : N.State) (i : N.Inputs) :
  R.v21398 (state s) (inputs i) = Zmod.unsigned (N.v21398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21398 s i)) at 1.
  unfold R.v21398, N.v21398.
  rewrite ?node_21393.
  rewrite ?node_21397.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21399 (s : N.State) (i : N.Inputs) :
  R.v21399 (state s) (inputs i) = Zmod.unsigned (N.v21399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21399 s i)) at 1.
  unfold R.v21399, N.v21399.
  unfold R.v6, N.v6.
  rewrite ?node_21398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21400 (s : N.State) (i : N.Inputs) :
  R.v21400 (state s) (inputs i) = Zmod.unsigned (N.v21400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21400 s i)) at 1.
  unfold R.v21400, N.v21400.
  rewrite ?node_7592.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21401 (s : N.State) (i : N.Inputs) :
  R.v21401 (state s) (inputs i) = Zmod.unsigned (N.v21401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21401 s i)) at 1.
  unfold R.v21401, N.v21401.
  unfold R.v6, N.v6.
  rewrite ?node_7708.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21402 (s : N.State) (i : N.Inputs) :
  R.v21402 (state s) (inputs i) = Zmod.unsigned (N.v21402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21402 s i)) at 1.
  unfold R.v21402, N.v21402.
  rewrite ?node_21400.
  rewrite ?node_21401.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21403 (s : N.State) (i : N.Inputs) :
  R.v21403 (state s) (inputs i) = Zmod.unsigned (N.v21403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21403 s i)) at 1.
  unfold R.v21403, N.v21403.
  rewrite ?node_21399.
  rewrite ?node_21402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21404 (s : N.State) (i : N.Inputs) :
  R.v21404 (state s) (inputs i) = Zmod.unsigned (N.v21404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21404 s i)) at 1.
  unfold R.v21404, N.v21404.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21405 (s : N.State) (i : N.Inputs) :
  R.v21405 (state s) (inputs i) = Zmod.unsigned (N.v21405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21405 s i)) at 1.
  unfold R.v21405, N.v21405.
  rewrite ?node_7596.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21406 (s : N.State) (i : N.Inputs) :
  R.v21406 (state s) (inputs i) = Zmod.unsigned (N.v21406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21406 s i)) at 1.
  unfold R.v21406, N.v21406.
  unfold R.v6, N.v6.
  rewrite !state_r553_nr_5F553.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r553_nr_5F553 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21407 (s : N.State) (i : N.Inputs) :
  R.v21407 (state s) (inputs i) = Zmod.unsigned (N.v21407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21407 s i)) at 1.
  unfold R.v21407, N.v21407.
  unfold R.v6, N.v6.
  rewrite ?node_7592.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21408 (s : N.State) (i : N.Inputs) :
  R.v21408 (state s) (inputs i) = Zmod.unsigned (N.v21408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21408 s i)) at 1.
  unfold R.v21408, N.v21408.
  rewrite ?node_21406.
  rewrite ?node_21407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21409 (s : N.State) (i : N.Inputs) :
  R.v21409 (state s) (inputs i) = Zmod.unsigned (N.v21409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21409 s i)) at 1.
  unfold R.v21409, N.v21409.
  unfold R.v16484, N.v16484.
  rewrite ?node_21408.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21410 (s : N.State) (i : N.Inputs) :
  R.v21410 (state s) (inputs i) = Zmod.unsigned (N.v21410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21410 s i)) at 1.
  unfold R.v21410, N.v21410.
  rewrite ?node_21405.
  rewrite ?node_21409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21411 (s : N.State) (i : N.Inputs) :
  R.v21411 (state s) (inputs i) = Zmod.unsigned (N.v21411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21411 s i)) at 1.
  unfold R.v21411, N.v21411.
  unfold R.v6, N.v6.
  rewrite ?node_21410.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21412 (s : N.State) (i : N.Inputs) :
  R.v21412 (state s) (inputs i) = Zmod.unsigned (N.v21412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21412 s i)) at 1.
  unfold R.v21412, N.v21412.
  rewrite ?node_7597.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21413 (s : N.State) (i : N.Inputs) :
  R.v21413 (state s) (inputs i) = Zmod.unsigned (N.v21413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21413 s i)) at 1.
  unfold R.v21413, N.v21413.
  unfold R.v6, N.v6.
  rewrite ?node_7755.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21414 (s : N.State) (i : N.Inputs) :
  R.v21414 (state s) (inputs i) = Zmod.unsigned (N.v21414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21414 s i)) at 1.
  unfold R.v21414, N.v21414.
  rewrite ?node_21412.
  rewrite ?node_21413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21415 (s : N.State) (i : N.Inputs) :
  R.v21415 (state s) (inputs i) = Zmod.unsigned (N.v21415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21415 s i)) at 1.
  unfold R.v21415, N.v21415.
  rewrite ?node_21411.
  rewrite ?node_21414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21416 (s : N.State) (i : N.Inputs) :
  R.v21416 (state s) (inputs i) = Zmod.unsigned (N.v21416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21416 s i)) at 1.
  unfold R.v21416, N.v21416.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21417 (s : N.State) (i : N.Inputs) :
  R.v21417 (state s) (inputs i) = Zmod.unsigned (N.v21417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21417 s i)) at 1.
  unfold R.v21417, N.v21417.
  rewrite ?node_7603.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21418 (s : N.State) (i : N.Inputs) :
  R.v21418 (state s) (inputs i) = Zmod.unsigned (N.v21418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21418 s i)) at 1.
  unfold R.v21418, N.v21418.
  unfold R.v16463, N.v16463.
  rewrite !state_r557_nr_5F557.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r557_nr_5F557 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21419 (s : N.State) (i : N.Inputs) :
  R.v21419 (state s) (inputs i) = Zmod.unsigned (N.v21419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21419 s i)) at 1.
  unfold R.v21419, N.v21419.
  unfold R.v16463, N.v16463.
  rewrite !state_r556_nr_5F556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r556_nr_5F556 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21420 (s : N.State) (i : N.Inputs) :
  R.v21420 (state s) (inputs i) = Zmod.unsigned (N.v21420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21420 s i)) at 1.
  unfold R.v21420, N.v21420.
  unfold R.v6, N.v6.
  rewrite !state_r555_nr_5F555.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r555_nr_5F555 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21421 (s : N.State) (i : N.Inputs) :
  R.v21421 (state s) (inputs i) = Zmod.unsigned (N.v21421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21421 s i)) at 1.
  unfold R.v21421, N.v21421.
  unfold R.v6, N.v6.
  rewrite !state_r554_nr_5F554.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r554_nr_5F554 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21422 (s : N.State) (i : N.Inputs) :
  R.v21422 (state s) (inputs i) = Zmod.unsigned (N.v21422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21422 s i)) at 1.
  unfold R.v21422, N.v21422.
  rewrite ?node_21420.
  rewrite ?node_21421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21423 (s : N.State) (i : N.Inputs) :
  R.v21423 (state s) (inputs i) = Zmod.unsigned (N.v21423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21423 s i)) at 1.
  unfold R.v21423, N.v21423.
  unfold R.v16484, N.v16484.
  rewrite ?node_21422.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21424 (s : N.State) (i : N.Inputs) :
  R.v21424 (state s) (inputs i) = Zmod.unsigned (N.v21424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21424 s i)) at 1.
  unfold R.v21424, N.v21424.
  rewrite ?node_21417.
  rewrite ?node_21418.
  rewrite ?node_21419.
  rewrite ?node_21423.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21425 (s : N.State) (i : N.Inputs) :
  R.v21425 (state s) (inputs i) = Zmod.unsigned (N.v21425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21425 s i)) at 1.
  unfold R.v21425, N.v21425.
  unfold R.v6, N.v6.
  rewrite ?node_21424.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21426 (s : N.State) (i : N.Inputs) :
  R.v21426 (state s) (inputs i) = Zmod.unsigned (N.v21426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21426 s i)) at 1.
  unfold R.v21426, N.v21426.
  rewrite ?node_7604.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21427 (s : N.State) (i : N.Inputs) :
  R.v21427 (state s) (inputs i) = Zmod.unsigned (N.v21427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21427 s i)) at 1.
  unfold R.v21427, N.v21427.
  unfold R.v6, N.v6.
  rewrite ?node_7715.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21428 (s : N.State) (i : N.Inputs) :
  R.v21428 (state s) (inputs i) = Zmod.unsigned (N.v21428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21428 s i)) at 1.
  unfold R.v21428, N.v21428.
  unfold R.v6, N.v6.
  rewrite ?node_7759.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21429 (s : N.State) (i : N.Inputs) :
  R.v21429 (state s) (inputs i) = Zmod.unsigned (N.v21429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21429 s i)) at 1.
  unfold R.v21429, N.v21429.
  rewrite ?node_21426.
  rewrite ?node_21427.
  rewrite ?node_21428.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21430 (s : N.State) (i : N.Inputs) :
  R.v21430 (state s) (inputs i) = Zmod.unsigned (N.v21430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21430 s i)) at 1.
  unfold R.v21430, N.v21430.
  rewrite ?node_21425.
  rewrite ?node_21429.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21431 (s : N.State) (i : N.Inputs) :
  R.v21431 (state s) (inputs i) = Zmod.unsigned (N.v21431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21431 s i)) at 1.
  unfold R.v21431, N.v21431.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21432 (s : N.State) (i : N.Inputs) :
  R.v21432 (state s) (inputs i) = Zmod.unsigned (N.v21432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21432 s i)) at 1.
  unfold R.v21432, N.v21432.
  unfold R.v16463, N.v16463.
  rewrite !state_r556_nr_5F556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r556_nr_5F556 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21433 (s : N.State) (i : N.Inputs) :
  R.v21433 (state s) (inputs i) = Zmod.unsigned (N.v21433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21433 s i)) at 1.
  unfold R.v21433, N.v21433.
  unfold R.v6, N.v6.
  rewrite !state_r555_nr_5F555.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r555_nr_5F555 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21434 (s : N.State) (i : N.Inputs) :
  R.v21434 (state s) (inputs i) = Zmod.unsigned (N.v21434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21434 s i)) at 1.
  unfold R.v21434, N.v21434.
  unfold R.v6, N.v6.
  rewrite !state_r554_nr_5F554.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r554_nr_5F554 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21435 (s : N.State) (i : N.Inputs) :
  R.v21435 (state s) (inputs i) = Zmod.unsigned (N.v21435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21435 s i)) at 1.
  unfold R.v21435, N.v21435.
  rewrite ?node_21433.
  rewrite ?node_21434.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21436 (s : N.State) (i : N.Inputs) :
  R.v21436 (state s) (inputs i) = Zmod.unsigned (N.v21436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21436 s i)) at 1.
  unfold R.v21436, N.v21436.
  unfold R.v16484, N.v16484.
  rewrite ?node_21435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21437 (s : N.State) (i : N.Inputs) :
  R.v21437 (state s) (inputs i) = Zmod.unsigned (N.v21437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21437 s i)) at 1.
  unfold R.v21437, N.v21437.
  rewrite ?node_21432.
  rewrite ?node_21436.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21438 (s : N.State) (i : N.Inputs) :
  R.v21438 (state s) (inputs i) = Zmod.unsigned (N.v21438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21438 s i)) at 1.
  unfold R.v21438, N.v21438.
  unfold R.v6, N.v6.
  rewrite ?node_21437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21439 (s : N.State) (i : N.Inputs) :
  R.v21439 (state s) (inputs i) = Zmod.unsigned (N.v21439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21439 s i)) at 1.
  unfold R.v21439, N.v21439.
  rewrite ?node_7599.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21440 (s : N.State) (i : N.Inputs) :
  R.v21440 (state s) (inputs i) = Zmod.unsigned (N.v21440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21440 s i)) at 1.
  unfold R.v21440, N.v21440.
  unfold R.v6, N.v6.
  rewrite ?node_7715.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21441 (s : N.State) (i : N.Inputs) :
  R.v21441 (state s) (inputs i) = Zmod.unsigned (N.v21441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21441 s i)) at 1.
  unfold R.v21441, N.v21441.
  rewrite ?node_21439.
  rewrite ?node_21440.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21442 (s : N.State) (i : N.Inputs) :
  R.v21442 (state s) (inputs i) = Zmod.unsigned (N.v21442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21442 s i)) at 1.
  unfold R.v21442, N.v21442.
  rewrite ?node_21438.
  rewrite ?node_21441.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21443 (s : N.State) (i : N.Inputs) :
  R.v21443 (state s) (inputs i) = Zmod.unsigned (N.v21443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21443 s i)) at 1.
  unfold R.v21443, N.v21443.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21444 (s : N.State) (i : N.Inputs) :
  R.v21444 (state s) (inputs i) = Zmod.unsigned (N.v21444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21444 s i)) at 1.
  unfold R.v21444, N.v21444.
  rewrite ?node_7603.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21445 (s : N.State) (i : N.Inputs) :
  R.v21445 (state s) (inputs i) = Zmod.unsigned (N.v21445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21445 s i)) at 1.
  unfold R.v21445, N.v21445.
  unfold R.v6, N.v6.
  rewrite !state_r557_nr_5F557.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r557_nr_5F557 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21446 (s : N.State) (i : N.Inputs) :
  R.v21446 (state s) (inputs i) = Zmod.unsigned (N.v21446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21446 s i)) at 1.
  unfold R.v21446, N.v21446.
  unfold R.v6, N.v6.
  rewrite ?node_7599.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21447 (s : N.State) (i : N.Inputs) :
  R.v21447 (state s) (inputs i) = Zmod.unsigned (N.v21447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21447 s i)) at 1.
  unfold R.v21447, N.v21447.
  rewrite ?node_21445.
  rewrite ?node_21446.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21448 (s : N.State) (i : N.Inputs) :
  R.v21448 (state s) (inputs i) = Zmod.unsigned (N.v21448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21448 s i)) at 1.
  unfold R.v21448, N.v21448.
  unfold R.v16484, N.v16484.
  rewrite ?node_21447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21449 (s : N.State) (i : N.Inputs) :
  R.v21449 (state s) (inputs i) = Zmod.unsigned (N.v21449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21449 s i)) at 1.
  unfold R.v21449, N.v21449.
  rewrite ?node_21444.
  rewrite ?node_21448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21450 (s : N.State) (i : N.Inputs) :
  R.v21450 (state s) (inputs i) = Zmod.unsigned (N.v21450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21450 s i)) at 1.
  unfold R.v21450, N.v21450.
  unfold R.v6, N.v6.
  rewrite ?node_21449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21451 (s : N.State) (i : N.Inputs) :
  R.v21451 (state s) (inputs i) = Zmod.unsigned (N.v21451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21451 s i)) at 1.
  unfold R.v21451, N.v21451.
  rewrite ?node_7604.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21452 (s : N.State) (i : N.Inputs) :
  R.v21452 (state s) (inputs i) = Zmod.unsigned (N.v21452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21452 s i)) at 1.
  unfold R.v21452, N.v21452.
  unfold R.v6, N.v6.
  rewrite ?node_7759.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21453 (s : N.State) (i : N.Inputs) :
  R.v21453 (state s) (inputs i) = Zmod.unsigned (N.v21453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21453 s i)) at 1.
  unfold R.v21453, N.v21453.
  rewrite ?node_21451.
  rewrite ?node_21452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21454 (s : N.State) (i : N.Inputs) :
  R.v21454 (state s) (inputs i) = Zmod.unsigned (N.v21454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21454 s i)) at 1.
  unfold R.v21454, N.v21454.
  rewrite ?node_21450.
  rewrite ?node_21453.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21455 (s : N.State) (i : N.Inputs) :
  R.v21455 (state s) (inputs i) = Zmod.unsigned (N.v21455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21455 s i)) at 1.
  unfold R.v21455, N.v21455.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21456 (s : N.State) (i : N.Inputs) :
  R.v21456 (state s) (inputs i) = Zmod.unsigned (N.v21456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21456 s i)) at 1.
  unfold R.v21456, N.v21456.
  rewrite ?node_7611.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21457 (s : N.State) (i : N.Inputs) :
  R.v21457 (state s) (inputs i) = Zmod.unsigned (N.v21457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21457 s i)) at 1.
  unfold R.v21457, N.v21457.
  unfold R.v16463, N.v16463.
  rewrite !state_r561_nr_5F561.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r561_nr_5F561 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21458 (s : N.State) (i : N.Inputs) :
  R.v21458 (state s) (inputs i) = Zmod.unsigned (N.v21458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21458 s i)) at 1.
  unfold R.v21458, N.v21458.
  unfold R.v16463, N.v16463.
  rewrite !state_r560_nr_5F560.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r560_nr_5F560 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21459 (s : N.State) (i : N.Inputs) :
  R.v21459 (state s) (inputs i) = Zmod.unsigned (N.v21459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21459 s i)) at 1.
  unfold R.v21459, N.v21459.
  unfold R.v6, N.v6.
  rewrite !state_r559_nr_5F559.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r559_nr_5F559 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21460 (s : N.State) (i : N.Inputs) :
  R.v21460 (state s) (inputs i) = Zmod.unsigned (N.v21460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21460 s i)) at 1.
  unfold R.v21460, N.v21460.
  unfold R.v6, N.v6.
  rewrite !state_r558_nr_5F558.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r558_nr_5F558 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21461 (s : N.State) (i : N.Inputs) :
  R.v21461 (state s) (inputs i) = Zmod.unsigned (N.v21461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21461 s i)) at 1.
  unfold R.v21461, N.v21461.
  rewrite ?node_21459.
  rewrite ?node_21460.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21462 (s : N.State) (i : N.Inputs) :
  R.v21462 (state s) (inputs i) = Zmod.unsigned (N.v21462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21462 s i)) at 1.
  unfold R.v21462, N.v21462.
  unfold R.v16484, N.v16484.
  rewrite ?node_21461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21463 (s : N.State) (i : N.Inputs) :
  R.v21463 (state s) (inputs i) = Zmod.unsigned (N.v21463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21463 s i)) at 1.
  unfold R.v21463, N.v21463.
  rewrite ?node_21456.
  rewrite ?node_21457.
  rewrite ?node_21458.
  rewrite ?node_21462.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21464 (s : N.State) (i : N.Inputs) :
  R.v21464 (state s) (inputs i) = Zmod.unsigned (N.v21464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21464 s i)) at 1.
  unfold R.v21464, N.v21464.
  unfold R.v6, N.v6.
  rewrite ?node_21463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21465 (s : N.State) (i : N.Inputs) :
  R.v21465 (state s) (inputs i) = Zmod.unsigned (N.v21465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21465 s i)) at 1.
  unfold R.v21465, N.v21465.
  rewrite ?node_7612.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21466 (s : N.State) (i : N.Inputs) :
  R.v21466 (state s) (inputs i) = Zmod.unsigned (N.v21466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21466 s i)) at 1.
  unfold R.v21466, N.v21466.
  unfold R.v6, N.v6.
  rewrite ?node_7723.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21467 (s : N.State) (i : N.Inputs) :
  R.v21467 (state s) (inputs i) = Zmod.unsigned (N.v21467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21467 s i)) at 1.
  unfold R.v21467, N.v21467.
  unfold R.v6, N.v6.
  rewrite ?node_7768.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21468 (s : N.State) (i : N.Inputs) :
  R.v21468 (state s) (inputs i) = Zmod.unsigned (N.v21468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21468 s i)) at 1.
  unfold R.v21468, N.v21468.
  rewrite ?node_21465.
  rewrite ?node_21466.
  rewrite ?node_21467.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21469 (s : N.State) (i : N.Inputs) :
  R.v21469 (state s) (inputs i) = Zmod.unsigned (N.v21469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21469 s i)) at 1.
  unfold R.v21469, N.v21469.
  rewrite ?node_21464.
  rewrite ?node_21468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21470 (s : N.State) (i : N.Inputs) :
  R.v21470 (state s) (inputs i) = Zmod.unsigned (N.v21470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21470 s i)) at 1.
  unfold R.v21470, N.v21470.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21471 (s : N.State) (i : N.Inputs) :
  R.v21471 (state s) (inputs i) = Zmod.unsigned (N.v21471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21471 s i)) at 1.
  unfold R.v21471, N.v21471.
  unfold R.v16463, N.v16463.
  rewrite !state_r560_nr_5F560.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r560_nr_5F560 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21472 (s : N.State) (i : N.Inputs) :
  R.v21472 (state s) (inputs i) = Zmod.unsigned (N.v21472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21472 s i)) at 1.
  unfold R.v21472, N.v21472.
  unfold R.v6, N.v6.
  rewrite !state_r559_nr_5F559.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r559_nr_5F559 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21473 (s : N.State) (i : N.Inputs) :
  R.v21473 (state s) (inputs i) = Zmod.unsigned (N.v21473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21473 s i)) at 1.
  unfold R.v21473, N.v21473.
  unfold R.v6, N.v6.
  rewrite !state_r558_nr_5F558.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r558_nr_5F558 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21474 (s : N.State) (i : N.Inputs) :
  R.v21474 (state s) (inputs i) = Zmod.unsigned (N.v21474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21474 s i)) at 1.
  unfold R.v21474, N.v21474.
  rewrite ?node_21472.
  rewrite ?node_21473.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21475 (s : N.State) (i : N.Inputs) :
  R.v21475 (state s) (inputs i) = Zmod.unsigned (N.v21475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21475 s i)) at 1.
  unfold R.v21475, N.v21475.
  unfold R.v16484, N.v16484.
  rewrite ?node_21474.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21476 (s : N.State) (i : N.Inputs) :
  R.v21476 (state s) (inputs i) = Zmod.unsigned (N.v21476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21476 s i)) at 1.
  unfold R.v21476, N.v21476.
  rewrite ?node_21471.
  rewrite ?node_21475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21477 (s : N.State) (i : N.Inputs) :
  R.v21477 (state s) (inputs i) = Zmod.unsigned (N.v21477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21477 s i)) at 1.
  unfold R.v21477, N.v21477.
  unfold R.v6, N.v6.
  rewrite ?node_21476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21478 (s : N.State) (i : N.Inputs) :
  R.v21478 (state s) (inputs i) = Zmod.unsigned (N.v21478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21478 s i)) at 1.
  unfold R.v21478, N.v21478.
  rewrite ?node_7607.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21479 (s : N.State) (i : N.Inputs) :
  R.v21479 (state s) (inputs i) = Zmod.unsigned (N.v21479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21479 s i)) at 1.
  unfold R.v21479, N.v21479.
  unfold R.v6, N.v6.
  rewrite ?node_7723.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21480 (s : N.State) (i : N.Inputs) :
  R.v21480 (state s) (inputs i) = Zmod.unsigned (N.v21480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21480 s i)) at 1.
  unfold R.v21480, N.v21480.
  rewrite ?node_21478.
  rewrite ?node_21479.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21481 (s : N.State) (i : N.Inputs) :
  R.v21481 (state s) (inputs i) = Zmod.unsigned (N.v21481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21481 s i)) at 1.
  unfold R.v21481, N.v21481.
  rewrite ?node_21477.
  rewrite ?node_21480.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21482 (s : N.State) (i : N.Inputs) :
  R.v21482 (state s) (inputs i) = Zmod.unsigned (N.v21482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21482 s i)) at 1.
  unfold R.v21482, N.v21482.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21483 (s : N.State) (i : N.Inputs) :
  R.v21483 (state s) (inputs i) = Zmod.unsigned (N.v21483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21483 s i)) at 1.
  unfold R.v21483, N.v21483.
  rewrite ?node_7611.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21484 (s : N.State) (i : N.Inputs) :
  R.v21484 (state s) (inputs i) = Zmod.unsigned (N.v21484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21484 s i)) at 1.
  unfold R.v21484, N.v21484.
  unfold R.v6, N.v6.
  rewrite !state_r561_nr_5F561.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r561_nr_5F561 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21485 (s : N.State) (i : N.Inputs) :
  R.v21485 (state s) (inputs i) = Zmod.unsigned (N.v21485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21485 s i)) at 1.
  unfold R.v21485, N.v21485.
  unfold R.v6, N.v6.
  rewrite ?node_7607.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21486 (s : N.State) (i : N.Inputs) :
  R.v21486 (state s) (inputs i) = Zmod.unsigned (N.v21486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21486 s i)) at 1.
  unfold R.v21486, N.v21486.
  rewrite ?node_21484.
  rewrite ?node_21485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21487 (s : N.State) (i : N.Inputs) :
  R.v21487 (state s) (inputs i) = Zmod.unsigned (N.v21487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21487 s i)) at 1.
  unfold R.v21487, N.v21487.
  unfold R.v16484, N.v16484.
  rewrite ?node_21486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21488 (s : N.State) (i : N.Inputs) :
  R.v21488 (state s) (inputs i) = Zmod.unsigned (N.v21488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21488 s i)) at 1.
  unfold R.v21488, N.v21488.
  rewrite ?node_21483.
  rewrite ?node_21487.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21489 (s : N.State) (i : N.Inputs) :
  R.v21489 (state s) (inputs i) = Zmod.unsigned (N.v21489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21489 s i)) at 1.
  unfold R.v21489, N.v21489.
  unfold R.v6, N.v6.
  rewrite ?node_21488.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21490 (s : N.State) (i : N.Inputs) :
  R.v21490 (state s) (inputs i) = Zmod.unsigned (N.v21490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21490 s i)) at 1.
  unfold R.v21490, N.v21490.
  rewrite ?node_7612.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21491 (s : N.State) (i : N.Inputs) :
  R.v21491 (state s) (inputs i) = Zmod.unsigned (N.v21491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21491 s i)) at 1.
  unfold R.v21491, N.v21491.
  unfold R.v6, N.v6.
  rewrite ?node_7768.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21492 (s : N.State) (i : N.Inputs) :
  R.v21492 (state s) (inputs i) = Zmod.unsigned (N.v21492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21492 s i)) at 1.
  unfold R.v21492, N.v21492.
  rewrite ?node_21490.
  rewrite ?node_21491.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21493 (s : N.State) (i : N.Inputs) :
  R.v21493 (state s) (inputs i) = Zmod.unsigned (N.v21493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21493 s i)) at 1.
  unfold R.v21493, N.v21493.
  rewrite ?node_21489.
  rewrite ?node_21492.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21494 (s : N.State) (i : N.Inputs) :
  R.v21494 (state s) (inputs i) = Zmod.unsigned (N.v21494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21494 s i)) at 1.
  unfold R.v21494, N.v21494.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21495 (s : N.State) (i : N.Inputs) :
  R.v21495 (state s) (inputs i) = Zmod.unsigned (N.v21495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21495 s i)) at 1.
  unfold R.v21495, N.v21495.
  rewrite ?node_7619.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21496 (s : N.State) (i : N.Inputs) :
  R.v21496 (state s) (inputs i) = Zmod.unsigned (N.v21496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21496 s i)) at 1.
  unfold R.v21496, N.v21496.
  unfold R.v16463, N.v16463.
  rewrite !state_r565_nr_5F565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r565_nr_5F565 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21497 (s : N.State) (i : N.Inputs) :
  R.v21497 (state s) (inputs i) = Zmod.unsigned (N.v21497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21497 s i)) at 1.
  unfold R.v21497, N.v21497.
  unfold R.v16463, N.v16463.
  rewrite !state_r564_nr_5F564.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r564_nr_5F564 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21498 (s : N.State) (i : N.Inputs) :
  R.v21498 (state s) (inputs i) = Zmod.unsigned (N.v21498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21498 s i)) at 1.
  unfold R.v21498, N.v21498.
  unfold R.v6, N.v6.
  rewrite !state_r563_nr_5F563.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r563_nr_5F563 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21499 (s : N.State) (i : N.Inputs) :
  R.v21499 (state s) (inputs i) = Zmod.unsigned (N.v21499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21499 s i)) at 1.
  unfold R.v21499, N.v21499.
  unfold R.v6, N.v6.
  rewrite !state_r562_nr_5F562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r562_nr_5F562 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21500 (s : N.State) (i : N.Inputs) :
  R.v21500 (state s) (inputs i) = Zmod.unsigned (N.v21500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21500 s i)) at 1.
  unfold R.v21500, N.v21500.
  rewrite ?node_21498.
  rewrite ?node_21499.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21501 (s : N.State) (i : N.Inputs) :
  R.v21501 (state s) (inputs i) = Zmod.unsigned (N.v21501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21501 s i)) at 1.
  unfold R.v21501, N.v21501.
  unfold R.v16484, N.v16484.
  rewrite ?node_21500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21502 (s : N.State) (i : N.Inputs) :
  R.v21502 (state s) (inputs i) = Zmod.unsigned (N.v21502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21502 s i)) at 1.
  unfold R.v21502, N.v21502.
  rewrite ?node_21495.
  rewrite ?node_21496.
  rewrite ?node_21497.
  rewrite ?node_21501.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21503 (s : N.State) (i : N.Inputs) :
  R.v21503 (state s) (inputs i) = Zmod.unsigned (N.v21503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21503 s i)) at 1.
  unfold R.v21503, N.v21503.
  unfold R.v6, N.v6.
  rewrite ?node_21502.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21504 (s : N.State) (i : N.Inputs) :
  R.v21504 (state s) (inputs i) = Zmod.unsigned (N.v21504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21504 s i)) at 1.
  unfold R.v21504, N.v21504.
  rewrite ?node_7620.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21505 (s : N.State) (i : N.Inputs) :
  R.v21505 (state s) (inputs i) = Zmod.unsigned (N.v21505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21505 s i)) at 1.
  unfold R.v21505, N.v21505.
  unfold R.v6, N.v6.
  rewrite ?node_7731.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21506 (s : N.State) (i : N.Inputs) :
  R.v21506 (state s) (inputs i) = Zmod.unsigned (N.v21506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21506 s i)) at 1.
  unfold R.v21506, N.v21506.
  unfold R.v6, N.v6.
  rewrite ?node_7771.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21507 (s : N.State) (i : N.Inputs) :
  R.v21507 (state s) (inputs i) = Zmod.unsigned (N.v21507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21507 s i)) at 1.
  unfold R.v21507, N.v21507.
  rewrite ?node_21504.
  rewrite ?node_21505.
  rewrite ?node_21506.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21508 (s : N.State) (i : N.Inputs) :
  R.v21508 (state s) (inputs i) = Zmod.unsigned (N.v21508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21508 s i)) at 1.
  unfold R.v21508, N.v21508.
  rewrite ?node_21503.
  rewrite ?node_21507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21509 (s : N.State) (i : N.Inputs) :
  R.v21509 (state s) (inputs i) = Zmod.unsigned (N.v21509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21509 s i)) at 1.
  unfold R.v21509, N.v21509.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21510 (s : N.State) (i : N.Inputs) :
  R.v21510 (state s) (inputs i) = Zmod.unsigned (N.v21510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21510 s i)) at 1.
  unfold R.v21510, N.v21510.
  unfold R.v16463, N.v16463.
  rewrite !state_r564_nr_5F564.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r564_nr_5F564 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21511 (s : N.State) (i : N.Inputs) :
  R.v21511 (state s) (inputs i) = Zmod.unsigned (N.v21511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21511 s i)) at 1.
  unfold R.v21511, N.v21511.
  unfold R.v6, N.v6.
  rewrite !state_r563_nr_5F563.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r563_nr_5F563 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21512 (s : N.State) (i : N.Inputs) :
  R.v21512 (state s) (inputs i) = Zmod.unsigned (N.v21512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21512 s i)) at 1.
  unfold R.v21512, N.v21512.
  unfold R.v6, N.v6.
  rewrite !state_r562_nr_5F562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r562_nr_5F562 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21513 (s : N.State) (i : N.Inputs) :
  R.v21513 (state s) (inputs i) = Zmod.unsigned (N.v21513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21513 s i)) at 1.
  unfold R.v21513, N.v21513.
  rewrite ?node_21511.
  rewrite ?node_21512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21514 (s : N.State) (i : N.Inputs) :
  R.v21514 (state s) (inputs i) = Zmod.unsigned (N.v21514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21514 s i)) at 1.
  unfold R.v21514, N.v21514.
  unfold R.v16484, N.v16484.
  rewrite ?node_21513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21515 (s : N.State) (i : N.Inputs) :
  R.v21515 (state s) (inputs i) = Zmod.unsigned (N.v21515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21515 s i)) at 1.
  unfold R.v21515, N.v21515.
  rewrite ?node_21510.
  rewrite ?node_21514.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21516 (s : N.State) (i : N.Inputs) :
  R.v21516 (state s) (inputs i) = Zmod.unsigned (N.v21516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21516 s i)) at 1.
  unfold R.v21516, N.v21516.
  unfold R.v6, N.v6.
  rewrite ?node_21515.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21517 (s : N.State) (i : N.Inputs) :
  R.v21517 (state s) (inputs i) = Zmod.unsigned (N.v21517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21517 s i)) at 1.
  unfold R.v21517, N.v21517.
  rewrite ?node_7615.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21518 (s : N.State) (i : N.Inputs) :
  R.v21518 (state s) (inputs i) = Zmod.unsigned (N.v21518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21518 s i)) at 1.
  unfold R.v21518, N.v21518.
  unfold R.v6, N.v6.
  rewrite ?node_7731.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21519 (s : N.State) (i : N.Inputs) :
  R.v21519 (state s) (inputs i) = Zmod.unsigned (N.v21519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21519 s i)) at 1.
  unfold R.v21519, N.v21519.
  rewrite ?node_21517.
  rewrite ?node_21518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21520 (s : N.State) (i : N.Inputs) :
  R.v21520 (state s) (inputs i) = Zmod.unsigned (N.v21520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21520 s i)) at 1.
  unfold R.v21520, N.v21520.
  rewrite ?node_21516.
  rewrite ?node_21519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21521 (s : N.State) (i : N.Inputs) :
  R.v21521 (state s) (inputs i) = Zmod.unsigned (N.v21521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21521 s i)) at 1.
  unfold R.v21521, N.v21521.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21522 (s : N.State) (i : N.Inputs) :
  R.v21522 (state s) (inputs i) = Zmod.unsigned (N.v21522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21522 s i)) at 1.
  unfold R.v21522, N.v21522.
  rewrite ?node_7619.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21523 (s : N.State) (i : N.Inputs) :
  R.v21523 (state s) (inputs i) = Zmod.unsigned (N.v21523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21523 s i)) at 1.
  unfold R.v21523, N.v21523.
  unfold R.v6, N.v6.
  rewrite !state_r565_nr_5F565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r565_nr_5F565 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21524 (s : N.State) (i : N.Inputs) :
  R.v21524 (state s) (inputs i) = Zmod.unsigned (N.v21524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21524 s i)) at 1.
  unfold R.v21524, N.v21524.
  unfold R.v6, N.v6.
  rewrite ?node_7615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21525 (s : N.State) (i : N.Inputs) :
  R.v21525 (state s) (inputs i) = Zmod.unsigned (N.v21525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21525 s i)) at 1.
  unfold R.v21525, N.v21525.
  rewrite ?node_21523.
  rewrite ?node_21524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21526 (s : N.State) (i : N.Inputs) :
  R.v21526 (state s) (inputs i) = Zmod.unsigned (N.v21526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21526 s i)) at 1.
  unfold R.v21526, N.v21526.
  unfold R.v16484, N.v16484.
  rewrite ?node_21525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21527 (s : N.State) (i : N.Inputs) :
  R.v21527 (state s) (inputs i) = Zmod.unsigned (N.v21527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21527 s i)) at 1.
  unfold R.v21527, N.v21527.
  rewrite ?node_21522.
  rewrite ?node_21526.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21528 (s : N.State) (i : N.Inputs) :
  R.v21528 (state s) (inputs i) = Zmod.unsigned (N.v21528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21528 s i)) at 1.
  unfold R.v21528, N.v21528.
  unfold R.v6, N.v6.
  rewrite ?node_21527.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21529 (s : N.State) (i : N.Inputs) :
  R.v21529 (state s) (inputs i) = Zmod.unsigned (N.v21529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21529 s i)) at 1.
  unfold R.v21529, N.v21529.
  rewrite ?node_7620.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21530 (s : N.State) (i : N.Inputs) :
  R.v21530 (state s) (inputs i) = Zmod.unsigned (N.v21530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21530 s i)) at 1.
  unfold R.v21530, N.v21530.
  unfold R.v6, N.v6.
  rewrite ?node_7771.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21531 (s : N.State) (i : N.Inputs) :
  R.v21531 (state s) (inputs i) = Zmod.unsigned (N.v21531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21531 s i)) at 1.
  unfold R.v21531, N.v21531.
  rewrite ?node_21529.
  rewrite ?node_21530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21532 (s : N.State) (i : N.Inputs) :
  R.v21532 (state s) (inputs i) = Zmod.unsigned (N.v21532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21532 s i)) at 1.
  unfold R.v21532, N.v21532.
  rewrite ?node_21528.
  rewrite ?node_21531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21533 (s : N.State) (i : N.Inputs) :
  R.v21533 (state s) (inputs i) = Zmod.unsigned (N.v21533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21533 s i)) at 1.
  unfold R.v21533, N.v21533.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21534 (s : N.State) (i : N.Inputs) :
  R.v21534 (state s) (inputs i) = Zmod.unsigned (N.v21534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21534 s i)) at 1.
  unfold R.v21534, N.v21534.
  rewrite ?node_7631.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21535 (s : N.State) (i : N.Inputs) :
  R.v21535 (state s) (inputs i) = Zmod.unsigned (N.v21535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21535 s i)) at 1.
  unfold R.v21535, N.v21535.
  unfold R.v16463, N.v16463.
  rewrite !state_r569_nr_5F569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r569_nr_5F569 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21536 (s : N.State) (i : N.Inputs) :
  R.v21536 (state s) (inputs i) = Zmod.unsigned (N.v21536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21536 s i)) at 1.
  unfold R.v21536, N.v21536.
  unfold R.v16463, N.v16463.
  rewrite !state_r568_nr_5F568.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r568_nr_5F568 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21537 (s : N.State) (i : N.Inputs) :
  R.v21537 (state s) (inputs i) = Zmod.unsigned (N.v21537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21537 s i)) at 1.
  unfold R.v21537, N.v21537.
  unfold R.v6, N.v6.
  rewrite !state_r567_nr_5F567.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r567_nr_5F567 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21538 (s : N.State) (i : N.Inputs) :
  R.v21538 (state s) (inputs i) = Zmod.unsigned (N.v21538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21538 s i)) at 1.
  unfold R.v21538, N.v21538.
  unfold R.v6, N.v6.
  rewrite !state_r566_nr_5F566.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r566_nr_5F566 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21539 (s : N.State) (i : N.Inputs) :
  R.v21539 (state s) (inputs i) = Zmod.unsigned (N.v21539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21539 s i)) at 1.
  unfold R.v21539, N.v21539.
  rewrite ?node_21537.
  rewrite ?node_21538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21540 (s : N.State) (i : N.Inputs) :
  R.v21540 (state s) (inputs i) = Zmod.unsigned (N.v21540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21540 s i)) at 1.
  unfold R.v21540, N.v21540.
  unfold R.v16484, N.v16484.
  rewrite ?node_21539.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21541 (s : N.State) (i : N.Inputs) :
  R.v21541 (state s) (inputs i) = Zmod.unsigned (N.v21541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21541 s i)) at 1.
  unfold R.v21541, N.v21541.
  rewrite ?node_21534.
  rewrite ?node_21535.
  rewrite ?node_21536.
  rewrite ?node_21540.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21542 (s : N.State) (i : N.Inputs) :
  R.v21542 (state s) (inputs i) = Zmod.unsigned (N.v21542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21542 s i)) at 1.
  unfold R.v21542, N.v21542.
  unfold R.v6, N.v6.
  rewrite ?node_21541.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21543 (s : N.State) (i : N.Inputs) :
  R.v21543 (state s) (inputs i) = Zmod.unsigned (N.v21543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21543 s i)) at 1.
  unfold R.v21543, N.v21543.
  rewrite ?node_7632.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21544 (s : N.State) (i : N.Inputs) :
  R.v21544 (state s) (inputs i) = Zmod.unsigned (N.v21544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21544 s i)) at 1.
  unfold R.v21544, N.v21544.
  unfold R.v6, N.v6.
  rewrite ?node_7743.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21545 (s : N.State) (i : N.Inputs) :
  R.v21545 (state s) (inputs i) = Zmod.unsigned (N.v21545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21545 s i)) at 1.
  unfold R.v21545, N.v21545.
  unfold R.v6, N.v6.
  rewrite ?node_7775.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21546 (s : N.State) (i : N.Inputs) :
  R.v21546 (state s) (inputs i) = Zmod.unsigned (N.v21546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21546 s i)) at 1.
  unfold R.v21546, N.v21546.
  rewrite ?node_21543.
  rewrite ?node_21544.
  rewrite ?node_21545.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21547 (s : N.State) (i : N.Inputs) :
  R.v21547 (state s) (inputs i) = Zmod.unsigned (N.v21547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21547 s i)) at 1.
  unfold R.v21547, N.v21547.
  rewrite ?node_21542.
  rewrite ?node_21546.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21548 (s : N.State) (i : N.Inputs) :
  R.v21548 (state s) (inputs i) = Zmod.unsigned (N.v21548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21548 s i)) at 1.
  unfold R.v21548, N.v21548.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21549 (s : N.State) (i : N.Inputs) :
  R.v21549 (state s) (inputs i) = Zmod.unsigned (N.v21549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21549 s i)) at 1.
  unfold R.v21549, N.v21549.
  unfold R.v16463, N.v16463.
  rewrite !state_r568_nr_5F568.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r568_nr_5F568 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21550 (s : N.State) (i : N.Inputs) :
  R.v21550 (state s) (inputs i) = Zmod.unsigned (N.v21550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21550 s i)) at 1.
  unfold R.v21550, N.v21550.
  unfold R.v6, N.v6.
  rewrite !state_r567_nr_5F567.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r567_nr_5F567 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21551 (s : N.State) (i : N.Inputs) :
  R.v21551 (state s) (inputs i) = Zmod.unsigned (N.v21551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21551 s i)) at 1.
  unfold R.v21551, N.v21551.
  unfold R.v6, N.v6.
  rewrite !state_r566_nr_5F566.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r566_nr_5F566 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21552 (s : N.State) (i : N.Inputs) :
  R.v21552 (state s) (inputs i) = Zmod.unsigned (N.v21552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21552 s i)) at 1.
  unfold R.v21552, N.v21552.
  rewrite ?node_21550.
  rewrite ?node_21551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21553 (s : N.State) (i : N.Inputs) :
  R.v21553 (state s) (inputs i) = Zmod.unsigned (N.v21553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21553 s i)) at 1.
  unfold R.v21553, N.v21553.
  unfold R.v16484, N.v16484.
  rewrite ?node_21552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21554 (s : N.State) (i : N.Inputs) :
  R.v21554 (state s) (inputs i) = Zmod.unsigned (N.v21554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21554 s i)) at 1.
  unfold R.v21554, N.v21554.
  rewrite ?node_21549.
  rewrite ?node_21553.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21555 (s : N.State) (i : N.Inputs) :
  R.v21555 (state s) (inputs i) = Zmod.unsigned (N.v21555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21555 s i)) at 1.
  unfold R.v21555, N.v21555.
  unfold R.v6, N.v6.
  rewrite ?node_21554.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21556 (s : N.State) (i : N.Inputs) :
  R.v21556 (state s) (inputs i) = Zmod.unsigned (N.v21556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21556 s i)) at 1.
  unfold R.v21556, N.v21556.
  rewrite ?node_7627.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21557 (s : N.State) (i : N.Inputs) :
  R.v21557 (state s) (inputs i) = Zmod.unsigned (N.v21557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21557 s i)) at 1.
  unfold R.v21557, N.v21557.
  unfold R.v6, N.v6.
  rewrite ?node_7743.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21558 (s : N.State) (i : N.Inputs) :
  R.v21558 (state s) (inputs i) = Zmod.unsigned (N.v21558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21558 s i)) at 1.
  unfold R.v21558, N.v21558.
  rewrite ?node_21556.
  rewrite ?node_21557.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21559 (s : N.State) (i : N.Inputs) :
  R.v21559 (state s) (inputs i) = Zmod.unsigned (N.v21559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21559 s i)) at 1.
  unfold R.v21559, N.v21559.
  rewrite ?node_21555.
  rewrite ?node_21558.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21560 (s : N.State) (i : N.Inputs) :
  R.v21560 (state s) (inputs i) = Zmod.unsigned (N.v21560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21560 s i)) at 1.
  unfold R.v21560, N.v21560.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21561 (s : N.State) (i : N.Inputs) :
  R.v21561 (state s) (inputs i) = Zmod.unsigned (N.v21561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21561 s i)) at 1.
  unfold R.v21561, N.v21561.
  rewrite ?node_7631.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21562 (s : N.State) (i : N.Inputs) :
  R.v21562 (state s) (inputs i) = Zmod.unsigned (N.v21562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21562 s i)) at 1.
  unfold R.v21562, N.v21562.
  unfold R.v6, N.v6.
  rewrite !state_r569_nr_5F569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r569_nr_5F569 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21563 (s : N.State) (i : N.Inputs) :
  R.v21563 (state s) (inputs i) = Zmod.unsigned (N.v21563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21563 s i)) at 1.
  unfold R.v21563, N.v21563.
  unfold R.v6, N.v6.
  rewrite ?node_7627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21564 (s : N.State) (i : N.Inputs) :
  R.v21564 (state s) (inputs i) = Zmod.unsigned (N.v21564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21564 s i)) at 1.
  unfold R.v21564, N.v21564.
  rewrite ?node_21562.
  rewrite ?node_21563.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21565 (s : N.State) (i : N.Inputs) :
  R.v21565 (state s) (inputs i) = Zmod.unsigned (N.v21565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21565 s i)) at 1.
  unfold R.v21565, N.v21565.
  unfold R.v16484, N.v16484.
  rewrite ?node_21564.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21566 (s : N.State) (i : N.Inputs) :
  R.v21566 (state s) (inputs i) = Zmod.unsigned (N.v21566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21566 s i)) at 1.
  unfold R.v21566, N.v21566.
  rewrite ?node_21561.
  rewrite ?node_21565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21567 (s : N.State) (i : N.Inputs) :
  R.v21567 (state s) (inputs i) = Zmod.unsigned (N.v21567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21567 s i)) at 1.
  unfold R.v21567, N.v21567.
  unfold R.v6, N.v6.
  rewrite ?node_21566.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21568 (s : N.State) (i : N.Inputs) :
  R.v21568 (state s) (inputs i) = Zmod.unsigned (N.v21568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21568 s i)) at 1.
  unfold R.v21568, N.v21568.
  rewrite ?node_7632.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21569 (s : N.State) (i : N.Inputs) :
  R.v21569 (state s) (inputs i) = Zmod.unsigned (N.v21569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21569 s i)) at 1.
  unfold R.v21569, N.v21569.
  unfold R.v6, N.v6.
  rewrite ?node_7775.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21570 (s : N.State) (i : N.Inputs) :
  R.v21570 (state s) (inputs i) = Zmod.unsigned (N.v21570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21570 s i)) at 1.
  unfold R.v21570, N.v21570.
  rewrite ?node_21568.
  rewrite ?node_21569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21571 (s : N.State) (i : N.Inputs) :
  R.v21571 (state s) (inputs i) = Zmod.unsigned (N.v21571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21571 s i)) at 1.
  unfold R.v21571, N.v21571.
  rewrite ?node_21567.
  rewrite ?node_21570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21572 (s : N.State) (i : N.Inputs) :
  R.v21572 (state s) (inputs i) = Zmod.unsigned (N.v21572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21572 s i)) at 1.
  unfold R.v21572, N.v21572.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21573 (s : N.State) (i : N.Inputs) :
  R.v21573 (state s) (inputs i) = Zmod.unsigned (N.v21573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21573 s i)) at 1.
  unfold R.v21573, N.v21573.
  unfold R.v16463, N.v16463.
  rewrite !state_r573_nr_5F573.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r573_nr_5F573 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21574 (s : N.State) (i : N.Inputs) :
  R.v21574 (state s) (inputs i) = Zmod.unsigned (N.v21574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21574 s i)) at 1.
  unfold R.v21574, N.v21574.
  unfold R.v16463, N.v16463.
  rewrite !state_r572_nr_5F572.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r572_nr_5F572 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21575 (s : N.State) (i : N.Inputs) :
  R.v21575 (state s) (inputs i) = Zmod.unsigned (N.v21575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21575 s i)) at 1.
  unfold R.v21575, N.v21575.
  unfold R.v6, N.v6.
  rewrite !state_r571_nr_5F571.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r571_nr_5F571 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21576 (s : N.State) (i : N.Inputs) :
  R.v21576 (state s) (inputs i) = Zmod.unsigned (N.v21576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21576 s i)) at 1.
  unfold R.v21576, N.v21576.
  unfold R.v6, N.v6.
  rewrite !state_r570_nr_5F570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r570_nr_5F570 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21577 (s : N.State) (i : N.Inputs) :
  R.v21577 (state s) (inputs i) = Zmod.unsigned (N.v21577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21577 s i)) at 1.
  unfold R.v21577, N.v21577.
  rewrite ?node_21575.
  rewrite ?node_21576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21578 (s : N.State) (i : N.Inputs) :
  R.v21578 (state s) (inputs i) = Zmod.unsigned (N.v21578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21578 s i)) at 1.
  unfold R.v21578, N.v21578.
  unfold R.v16484, N.v16484.
  rewrite ?node_21577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21579 (s : N.State) (i : N.Inputs) :
  R.v21579 (state s) (inputs i) = Zmod.unsigned (N.v21579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21579 s i)) at 1.
  unfold R.v21579, N.v21579.
  rewrite ?node_21573.
  rewrite ?node_21574.
  rewrite ?node_21578.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21580 (s : N.State) (i : N.Inputs) :
  R.v21580 (state s) (inputs i) = Zmod.unsigned (N.v21580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21580 s i)) at 1.
  unfold R.v21580, N.v21580.
  unfold R.v6, N.v6.
  rewrite ?node_21579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21581 (s : N.State) (i : N.Inputs) :
  R.v21581 (state s) (inputs i) = Zmod.unsigned (N.v21581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21581 s i)) at 1.
  unfold R.v21581, N.v21581.
  rewrite ?node_7635.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21582 (s : N.State) (i : N.Inputs) :
  R.v21582 (state s) (inputs i) = Zmod.unsigned (N.v21582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21582 s i)) at 1.
  unfold R.v21582, N.v21582.
  unfold R.v6, N.v6.
  rewrite ?node_7750.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21583 (s : N.State) (i : N.Inputs) :
  R.v21583 (state s) (inputs i) = Zmod.unsigned (N.v21583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21583 s i)) at 1.
  unfold R.v21583, N.v21583.
  unfold R.v6, N.v6.
  rewrite ?node_7777.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21584 (s : N.State) (i : N.Inputs) :
  R.v21584 (state s) (inputs i) = Zmod.unsigned (N.v21584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21584 s i)) at 1.
  unfold R.v21584, N.v21584.
  rewrite ?node_21581.
  rewrite ?node_21582.
  rewrite ?node_21583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21585 (s : N.State) (i : N.Inputs) :
  R.v21585 (state s) (inputs i) = Zmod.unsigned (N.v21585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21585 s i)) at 1.
  unfold R.v21585, N.v21585.
  rewrite ?node_21580.
  rewrite ?node_21584.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21586 (s : N.State) (i : N.Inputs) :
  R.v21586 (state s) (inputs i) = Zmod.unsigned (N.v21586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21586 s i)) at 1.
  unfold R.v21586, N.v21586.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21587 (s : N.State) (i : N.Inputs) :
  R.v21587 (state s) (inputs i) = Zmod.unsigned (N.v21587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21587 s i)) at 1.
  unfold R.v21587, N.v21587.
  unfold R.v16463, N.v16463.
  rewrite !state_r572_nr_5F572.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r572_nr_5F572 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21588 (s : N.State) (i : N.Inputs) :
  R.v21588 (state s) (inputs i) = Zmod.unsigned (N.v21588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21588 s i)) at 1.
  unfold R.v21588, N.v21588.
  unfold R.v6, N.v6.
  rewrite !state_r571_nr_5F571.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r571_nr_5F571 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21589 (s : N.State) (i : N.Inputs) :
  R.v21589 (state s) (inputs i) = Zmod.unsigned (N.v21589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21589 s i)) at 1.
  unfold R.v21589, N.v21589.
  unfold R.v6, N.v6.
  rewrite !state_r570_nr_5F570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r570_nr_5F570 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21590 (s : N.State) (i : N.Inputs) :
  R.v21590 (state s) (inputs i) = Zmod.unsigned (N.v21590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21590 s i)) at 1.
  unfold R.v21590, N.v21590.
  rewrite ?node_21588.
  rewrite ?node_21589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21591 (s : N.State) (i : N.Inputs) :
  R.v21591 (state s) (inputs i) = Zmod.unsigned (N.v21591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21591 s i)) at 1.
  unfold R.v21591, N.v21591.
  unfold R.v16484, N.v16484.
  rewrite ?node_21590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21592 (s : N.State) (i : N.Inputs) :
  R.v21592 (state s) (inputs i) = Zmod.unsigned (N.v21592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21592 s i)) at 1.
  unfold R.v21592, N.v21592.
  rewrite ?node_21587.
  rewrite ?node_21591.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21593 (s : N.State) (i : N.Inputs) :
  R.v21593 (state s) (inputs i) = Zmod.unsigned (N.v21593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21593 s i)) at 1.
  unfold R.v21593, N.v21593.
  unfold R.v6, N.v6.
  rewrite ?node_21592.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21594 (s : N.State) (i : N.Inputs) :
  R.v21594 (state s) (inputs i) = Zmod.unsigned (N.v21594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21594 s i)) at 1.
  unfold R.v21594, N.v21594.
  rewrite ?node_7634.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21595 (s : N.State) (i : N.Inputs) :
  R.v21595 (state s) (inputs i) = Zmod.unsigned (N.v21595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21595 s i)) at 1.
  unfold R.v21595, N.v21595.
  unfold R.v6, N.v6.
  rewrite ?node_7750.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21596 (s : N.State) (i : N.Inputs) :
  R.v21596 (state s) (inputs i) = Zmod.unsigned (N.v21596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21596 s i)) at 1.
  unfold R.v21596, N.v21596.
  rewrite ?node_21594.
  rewrite ?node_21595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21597 (s : N.State) (i : N.Inputs) :
  R.v21597 (state s) (inputs i) = Zmod.unsigned (N.v21597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21597 s i)) at 1.
  unfold R.v21597, N.v21597.
  rewrite ?node_21593.
  rewrite ?node_21596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21598 (s : N.State) (i : N.Inputs) :
  R.v21598 (state s) (inputs i) = Zmod.unsigned (N.v21598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21598 s i)) at 1.
  unfold R.v21598, N.v21598.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21599 (s : N.State) (i : N.Inputs) :
  R.v21599 (state s) (inputs i) = Zmod.unsigned (N.v21599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21599 s i)) at 1.
  unfold R.v21599, N.v21599.
  unfold R.v6, N.v6.
  rewrite !state_r573_nr_5F573.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r573_nr_5F573 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21600 (s : N.State) (i : N.Inputs) :
  R.v21600 (state s) (inputs i) = Zmod.unsigned (N.v21600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21600 s i)) at 1.
  unfold R.v21600, N.v21600.
  unfold R.v6, N.v6.
  rewrite ?node_7634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21601 (s : N.State) (i : N.Inputs) :
  R.v21601 (state s) (inputs i) = Zmod.unsigned (N.v21601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21601 s i)) at 1.
  unfold R.v21601, N.v21601.
  rewrite ?node_21599.
  rewrite ?node_21600.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21602 (s : N.State) (i : N.Inputs) :
  R.v21602 (state s) (inputs i) = Zmod.unsigned (N.v21602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21602 s i)) at 1.
  unfold R.v21602, N.v21602.
  unfold R.v16463, N.v16463.
  rewrite ?node_21601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21603 (s : N.State) (i : N.Inputs) :
  R.v21603 (state s) (inputs i) = Zmod.unsigned (N.v21603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21603 s i)) at 1.
  unfold R.v21603, N.v21603.
  rewrite ?node_7635.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21604 (s : N.State) (i : N.Inputs) :
  R.v21604 (state s) (inputs i) = Zmod.unsigned (N.v21604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21604 s i)) at 1.
  unfold R.v21604, N.v21604.
  unfold R.v6, N.v6.
  rewrite ?node_7777.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21605 (s : N.State) (i : N.Inputs) :
  R.v21605 (state s) (inputs i) = Zmod.unsigned (N.v21605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21605 s i)) at 1.
  unfold R.v21605, N.v21605.
  rewrite ?node_21603.
  rewrite ?node_21604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21606 (s : N.State) (i : N.Inputs) :
  R.v21606 (state s) (inputs i) = Zmod.unsigned (N.v21606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21606 s i)) at 1.
  unfold R.v21606, N.v21606.
  rewrite ?node_21602.
  rewrite ?node_21605.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21607 (s : N.State) (i : N.Inputs) :
  R.v21607 (state s) (inputs i) = Zmod.unsigned (N.v21607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21607 s i)) at 1.
  unfold R.v21607, N.v21607.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21608 (s : N.State) (i : N.Inputs) :
  R.v21608 (state s) (inputs i) = Zmod.unsigned (N.v21608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21608 s i)) at 1.
  unfold R.v21608, N.v21608.
  rewrite ?node_7708.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21609 (s : N.State) (i : N.Inputs) :
  R.v21609 (state s) (inputs i) = Zmod.unsigned (N.v21609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21609 s i)) at 1.
  unfold R.v21609, N.v21609.
  unfold R.v16463, N.v16463.
  rewrite !state_r577_nr_5F577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r577_nr_5F577 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21610 (s : N.State) (i : N.Inputs) :
  R.v21610 (state s) (inputs i) = Zmod.unsigned (N.v21610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21610 s i)) at 1.
  unfold R.v21610, N.v21610.
  unfold R.v16463, N.v16463.
  rewrite !state_r576_nr_5F576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r576_nr_5F576 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21611 (s : N.State) (i : N.Inputs) :
  R.v21611 (state s) (inputs i) = Zmod.unsigned (N.v21611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21611 s i)) at 1.
  unfold R.v21611, N.v21611.
  unfold R.v6, N.v6.
  rewrite !state_r575_nr_5F575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r575_nr_5F575 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21612 (s : N.State) (i : N.Inputs) :
  R.v21612 (state s) (inputs i) = Zmod.unsigned (N.v21612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21612 s i)) at 1.
  unfold R.v21612, N.v21612.
  unfold R.v6, N.v6.
  rewrite !state_r574_nr_5F574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r574_nr_5F574 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21613 (s : N.State) (i : N.Inputs) :
  R.v21613 (state s) (inputs i) = Zmod.unsigned (N.v21613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21613 s i)) at 1.
  unfold R.v21613, N.v21613.
  rewrite ?node_21611.
  rewrite ?node_21612.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21614 (s : N.State) (i : N.Inputs) :
  R.v21614 (state s) (inputs i) = Zmod.unsigned (N.v21614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21614 s i)) at 1.
  unfold R.v21614, N.v21614.
  unfold R.v16484, N.v16484.
  rewrite ?node_21613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21615 (s : N.State) (i : N.Inputs) :
  R.v21615 (state s) (inputs i) = Zmod.unsigned (N.v21615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21615 s i)) at 1.
  unfold R.v21615, N.v21615.
  rewrite ?node_21608.
  rewrite ?node_21609.
  rewrite ?node_21610.
  rewrite ?node_21614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21616 (s : N.State) (i : N.Inputs) :
  R.v21616 (state s) (inputs i) = Zmod.unsigned (N.v21616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21616 s i)) at 1.
  unfold R.v21616, N.v21616.
  unfold R.v6, N.v6.
  rewrite ?node_21615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21617 (s : N.State) (i : N.Inputs) :
  R.v21617 (state s) (inputs i) = Zmod.unsigned (N.v21617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21617 s i)) at 1.
  unfold R.v21617, N.v21617.
  rewrite ?node_7709.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21618 (s : N.State) (i : N.Inputs) :
  R.v21618 (state s) (inputs i) = Zmod.unsigned (N.v21618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21618 s i)) at 1.
  unfold R.v21618, N.v21618.
  unfold R.v6, N.v6.
  rewrite ?node_7822.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21619 (s : N.State) (i : N.Inputs) :
  R.v21619 (state s) (inputs i) = Zmod.unsigned (N.v21619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21619 s i)) at 1.
  unfold R.v21619, N.v21619.
  unfold R.v6, N.v6.
  rewrite ?node_7870.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21620 (s : N.State) (i : N.Inputs) :
  R.v21620 (state s) (inputs i) = Zmod.unsigned (N.v21620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21620 s i)) at 1.
  unfold R.v21620, N.v21620.
  rewrite ?node_21617.
  rewrite ?node_21618.
  rewrite ?node_21619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21621 (s : N.State) (i : N.Inputs) :
  R.v21621 (state s) (inputs i) = Zmod.unsigned (N.v21621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21621 s i)) at 1.
  unfold R.v21621, N.v21621.
  rewrite ?node_21616.
  rewrite ?node_21620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21622 (s : N.State) (i : N.Inputs) :
  R.v21622 (state s) (inputs i) = Zmod.unsigned (N.v21622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21622 s i)) at 1.
  unfold R.v21622, N.v21622.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21623 (s : N.State) (i : N.Inputs) :
  R.v21623 (state s) (inputs i) = Zmod.unsigned (N.v21623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21623 s i)) at 1.
  unfold R.v21623, N.v21623.
  unfold R.v16463, N.v16463.
  rewrite !state_r576_nr_5F576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r576_nr_5F576 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21624 (s : N.State) (i : N.Inputs) :
  R.v21624 (state s) (inputs i) = Zmod.unsigned (N.v21624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21624 s i)) at 1.
  unfold R.v21624, N.v21624.
  unfold R.v6, N.v6.
  rewrite !state_r575_nr_5F575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r575_nr_5F575 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21625 (s : N.State) (i : N.Inputs) :
  R.v21625 (state s) (inputs i) = Zmod.unsigned (N.v21625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21625 s i)) at 1.
  unfold R.v21625, N.v21625.
  unfold R.v6, N.v6.
  rewrite !state_r574_nr_5F574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r574_nr_5F574 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21626 (s : N.State) (i : N.Inputs) :
  R.v21626 (state s) (inputs i) = Zmod.unsigned (N.v21626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21626 s i)) at 1.
  unfold R.v21626, N.v21626.
  rewrite ?node_21624.
  rewrite ?node_21625.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21627 (s : N.State) (i : N.Inputs) :
  R.v21627 (state s) (inputs i) = Zmod.unsigned (N.v21627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21627 s i)) at 1.
  unfold R.v21627, N.v21627.
  unfold R.v16484, N.v16484.
  rewrite ?node_21626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21628 (s : N.State) (i : N.Inputs) :
  R.v21628 (state s) (inputs i) = Zmod.unsigned (N.v21628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21628 s i)) at 1.
  unfold R.v21628, N.v21628.
  rewrite ?node_21623.
  rewrite ?node_21627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21629 (s : N.State) (i : N.Inputs) :
  R.v21629 (state s) (inputs i) = Zmod.unsigned (N.v21629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21629 s i)) at 1.
  unfold R.v21629, N.v21629.
  unfold R.v6, N.v6.
  rewrite ?node_21628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21630 (s : N.State) (i : N.Inputs) :
  R.v21630 (state s) (inputs i) = Zmod.unsigned (N.v21630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21630 s i)) at 1.
  unfold R.v21630, N.v21630.
  rewrite ?node_7704.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21631 (s : N.State) (i : N.Inputs) :
  R.v21631 (state s) (inputs i) = Zmod.unsigned (N.v21631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21631 s i)) at 1.
  unfold R.v21631, N.v21631.
  unfold R.v6, N.v6.
  rewrite ?node_7822.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21632 (s : N.State) (i : N.Inputs) :
  R.v21632 (state s) (inputs i) = Zmod.unsigned (N.v21632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21632 s i)) at 1.
  unfold R.v21632, N.v21632.
  rewrite ?node_21630.
  rewrite ?node_21631.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21633 (s : N.State) (i : N.Inputs) :
  R.v21633 (state s) (inputs i) = Zmod.unsigned (N.v21633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21633 s i)) at 1.
  unfold R.v21633, N.v21633.
  rewrite ?node_21629.
  rewrite ?node_21632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21634 (s : N.State) (i : N.Inputs) :
  R.v21634 (state s) (inputs i) = Zmod.unsigned (N.v21634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21634 s i)) at 1.
  unfold R.v21634, N.v21634.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21635 (s : N.State) (i : N.Inputs) :
  R.v21635 (state s) (inputs i) = Zmod.unsigned (N.v21635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21635 s i)) at 1.
  unfold R.v21635, N.v21635.
  rewrite ?node_7708.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21636 (s : N.State) (i : N.Inputs) :
  R.v21636 (state s) (inputs i) = Zmod.unsigned (N.v21636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21636 s i)) at 1.
  unfold R.v21636, N.v21636.
  unfold R.v6, N.v6.
  rewrite !state_r577_nr_5F577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r577_nr_5F577 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21637 (s : N.State) (i : N.Inputs) :
  R.v21637 (state s) (inputs i) = Zmod.unsigned (N.v21637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21637 s i)) at 1.
  unfold R.v21637, N.v21637.
  unfold R.v6, N.v6.
  rewrite ?node_7704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21638 (s : N.State) (i : N.Inputs) :
  R.v21638 (state s) (inputs i) = Zmod.unsigned (N.v21638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21638 s i)) at 1.
  unfold R.v21638, N.v21638.
  rewrite ?node_21636.
  rewrite ?node_21637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21639 (s : N.State) (i : N.Inputs) :
  R.v21639 (state s) (inputs i) = Zmod.unsigned (N.v21639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21639 s i)) at 1.
  unfold R.v21639, N.v21639.
  unfold R.v16484, N.v16484.
  rewrite ?node_21638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21640 (s : N.State) (i : N.Inputs) :
  R.v21640 (state s) (inputs i) = Zmod.unsigned (N.v21640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21640 s i)) at 1.
  unfold R.v21640, N.v21640.
  rewrite ?node_21635.
  rewrite ?node_21639.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21641 (s : N.State) (i : N.Inputs) :
  R.v21641 (state s) (inputs i) = Zmod.unsigned (N.v21641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21641 s i)) at 1.
  unfold R.v21641, N.v21641.
  unfold R.v6, N.v6.
  rewrite ?node_21640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21642 (s : N.State) (i : N.Inputs) :
  R.v21642 (state s) (inputs i) = Zmod.unsigned (N.v21642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21642 s i)) at 1.
  unfold R.v21642, N.v21642.
  rewrite ?node_7709.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21643 (s : N.State) (i : N.Inputs) :
  R.v21643 (state s) (inputs i) = Zmod.unsigned (N.v21643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21643 s i)) at 1.
  unfold R.v21643, N.v21643.
  unfold R.v6, N.v6.
  rewrite ?node_7870.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21644 (s : N.State) (i : N.Inputs) :
  R.v21644 (state s) (inputs i) = Zmod.unsigned (N.v21644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21644 s i)) at 1.
  unfold R.v21644, N.v21644.
  rewrite ?node_21642.
  rewrite ?node_21643.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21645 (s : N.State) (i : N.Inputs) :
  R.v21645 (state s) (inputs i) = Zmod.unsigned (N.v21645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21645 s i)) at 1.
  unfold R.v21645, N.v21645.
  rewrite ?node_21641.
  rewrite ?node_21644.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21646 (s : N.State) (i : N.Inputs) :
  R.v21646 (state s) (inputs i) = Zmod.unsigned (N.v21646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21646 s i)) at 1.
  unfold R.v21646, N.v21646.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21647 (s : N.State) (i : N.Inputs) :
  R.v21647 (state s) (inputs i) = Zmod.unsigned (N.v21647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21647 s i)) at 1.
  unfold R.v21647, N.v21647.
  rewrite ?node_7715.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21648 (s : N.State) (i : N.Inputs) :
  R.v21648 (state s) (inputs i) = Zmod.unsigned (N.v21648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21648 s i)) at 1.
  unfold R.v21648, N.v21648.
  unfold R.v16463, N.v16463.
  rewrite !state_r581_nr_5F581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r581_nr_5F581 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21649 (s : N.State) (i : N.Inputs) :
  R.v21649 (state s) (inputs i) = Zmod.unsigned (N.v21649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21649 s i)) at 1.
  unfold R.v21649, N.v21649.
  unfold R.v16463, N.v16463.
  rewrite !state_r580_nr_5F580.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r580_nr_5F580 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21650 (s : N.State) (i : N.Inputs) :
  R.v21650 (state s) (inputs i) = Zmod.unsigned (N.v21650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21650 s i)) at 1.
  unfold R.v21650, N.v21650.
  unfold R.v6, N.v6.
  rewrite !state_r579_nr_5F579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r579_nr_5F579 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21651 (s : N.State) (i : N.Inputs) :
  R.v21651 (state s) (inputs i) = Zmod.unsigned (N.v21651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21651 s i)) at 1.
  unfold R.v21651, N.v21651.
  unfold R.v6, N.v6.
  rewrite !state_r578_nr_5F578.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r578_nr_5F578 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21652 (s : N.State) (i : N.Inputs) :
  R.v21652 (state s) (inputs i) = Zmod.unsigned (N.v21652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21652 s i)) at 1.
  unfold R.v21652, N.v21652.
  rewrite ?node_21650.
  rewrite ?node_21651.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21653 (s : N.State) (i : N.Inputs) :
  R.v21653 (state s) (inputs i) = Zmod.unsigned (N.v21653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21653 s i)) at 1.
  unfold R.v21653, N.v21653.
  unfold R.v16484, N.v16484.
  rewrite ?node_21652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21654 (s : N.State) (i : N.Inputs) :
  R.v21654 (state s) (inputs i) = Zmod.unsigned (N.v21654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21654 s i)) at 1.
  unfold R.v21654, N.v21654.
  rewrite ?node_21647.
  rewrite ?node_21648.
  rewrite ?node_21649.
  rewrite ?node_21653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21655 (s : N.State) (i : N.Inputs) :
  R.v21655 (state s) (inputs i) = Zmod.unsigned (N.v21655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21655 s i)) at 1.
  unfold R.v21655, N.v21655.
  unfold R.v6, N.v6.
  rewrite ?node_21654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21656 (s : N.State) (i : N.Inputs) :
  R.v21656 (state s) (inputs i) = Zmod.unsigned (N.v21656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21656 s i)) at 1.
  unfold R.v21656, N.v21656.
  rewrite ?node_7716.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21657 (s : N.State) (i : N.Inputs) :
  R.v21657 (state s) (inputs i) = Zmod.unsigned (N.v21657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21657 s i)) at 1.
  unfold R.v21657, N.v21657.
  unfold R.v6, N.v6.
  rewrite ?node_7829.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21658 (s : N.State) (i : N.Inputs) :
  R.v21658 (state s) (inputs i) = Zmod.unsigned (N.v21658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21658 s i)) at 1.
  unfold R.v21658, N.v21658.
  unfold R.v6, N.v6.
  rewrite ?node_7879.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21659 (s : N.State) (i : N.Inputs) :
  R.v21659 (state s) (inputs i) = Zmod.unsigned (N.v21659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21659 s i)) at 1.
  unfold R.v21659, N.v21659.
  rewrite ?node_21656.
  rewrite ?node_21657.
  rewrite ?node_21658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21660 (s : N.State) (i : N.Inputs) :
  R.v21660 (state s) (inputs i) = Zmod.unsigned (N.v21660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21660 s i)) at 1.
  unfold R.v21660, N.v21660.
  rewrite ?node_21655.
  rewrite ?node_21659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21661 (s : N.State) (i : N.Inputs) :
  R.v21661 (state s) (inputs i) = Zmod.unsigned (N.v21661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21661 s i)) at 1.
  unfold R.v21661, N.v21661.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21662 (s : N.State) (i : N.Inputs) :
  R.v21662 (state s) (inputs i) = Zmod.unsigned (N.v21662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21662 s i)) at 1.
  unfold R.v21662, N.v21662.
  unfold R.v16463, N.v16463.
  rewrite !state_r580_nr_5F580.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r580_nr_5F580 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21663 (s : N.State) (i : N.Inputs) :
  R.v21663 (state s) (inputs i) = Zmod.unsigned (N.v21663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21663 s i)) at 1.
  unfold R.v21663, N.v21663.
  unfold R.v6, N.v6.
  rewrite !state_r579_nr_5F579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r579_nr_5F579 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21664 (s : N.State) (i : N.Inputs) :
  R.v21664 (state s) (inputs i) = Zmod.unsigned (N.v21664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21664 s i)) at 1.
  unfold R.v21664, N.v21664.
  unfold R.v6, N.v6.
  rewrite !state_r578_nr_5F578.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r578_nr_5F578 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21665 (s : N.State) (i : N.Inputs) :
  R.v21665 (state s) (inputs i) = Zmod.unsigned (N.v21665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21665 s i)) at 1.
  unfold R.v21665, N.v21665.
  rewrite ?node_21663.
  rewrite ?node_21664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21666 (s : N.State) (i : N.Inputs) :
  R.v21666 (state s) (inputs i) = Zmod.unsigned (N.v21666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21666 s i)) at 1.
  unfold R.v21666, N.v21666.
  unfold R.v16484, N.v16484.
  rewrite ?node_21665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21667 (s : N.State) (i : N.Inputs) :
  R.v21667 (state s) (inputs i) = Zmod.unsigned (N.v21667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21667 s i)) at 1.
  unfold R.v21667, N.v21667.
  rewrite ?node_21662.
  rewrite ?node_21666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21668 (s : N.State) (i : N.Inputs) :
  R.v21668 (state s) (inputs i) = Zmod.unsigned (N.v21668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21668 s i)) at 1.
  unfold R.v21668, N.v21668.
  unfold R.v6, N.v6.
  rewrite ?node_21667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21669 (s : N.State) (i : N.Inputs) :
  R.v21669 (state s) (inputs i) = Zmod.unsigned (N.v21669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21669 s i)) at 1.
  unfold R.v21669, N.v21669.
  rewrite ?node_7711.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21670 (s : N.State) (i : N.Inputs) :
  R.v21670 (state s) (inputs i) = Zmod.unsigned (N.v21670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21670 s i)) at 1.
  unfold R.v21670, N.v21670.
  unfold R.v6, N.v6.
  rewrite ?node_7829.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21671 (s : N.State) (i : N.Inputs) :
  R.v21671 (state s) (inputs i) = Zmod.unsigned (N.v21671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21671 s i)) at 1.
  unfold R.v21671, N.v21671.
  rewrite ?node_21669.
  rewrite ?node_21670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21672 (s : N.State) (i : N.Inputs) :
  R.v21672 (state s) (inputs i) = Zmod.unsigned (N.v21672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21672 s i)) at 1.
  unfold R.v21672, N.v21672.
  rewrite ?node_21668.
  rewrite ?node_21671.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21673 (s : N.State) (i : N.Inputs) :
  R.v21673 (state s) (inputs i) = Zmod.unsigned (N.v21673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21673 s i)) at 1.
  unfold R.v21673, N.v21673.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21674 (s : N.State) (i : N.Inputs) :
  R.v21674 (state s) (inputs i) = Zmod.unsigned (N.v21674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21674 s i)) at 1.
  unfold R.v21674, N.v21674.
  rewrite ?node_7715.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21675 (s : N.State) (i : N.Inputs) :
  R.v21675 (state s) (inputs i) = Zmod.unsigned (N.v21675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21675 s i)) at 1.
  unfold R.v21675, N.v21675.
  unfold R.v6, N.v6.
  rewrite !state_r581_nr_5F581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r581_nr_5F581 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21676 (s : N.State) (i : N.Inputs) :
  R.v21676 (state s) (inputs i) = Zmod.unsigned (N.v21676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21676 s i)) at 1.
  unfold R.v21676, N.v21676.
  unfold R.v6, N.v6.
  rewrite ?node_7711.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21677 (s : N.State) (i : N.Inputs) :
  R.v21677 (state s) (inputs i) = Zmod.unsigned (N.v21677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21677 s i)) at 1.
  unfold R.v21677, N.v21677.
  rewrite ?node_21675.
  rewrite ?node_21676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21678 (s : N.State) (i : N.Inputs) :
  R.v21678 (state s) (inputs i) = Zmod.unsigned (N.v21678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21678 s i)) at 1.
  unfold R.v21678, N.v21678.
  unfold R.v16484, N.v16484.
  rewrite ?node_21677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21679 (s : N.State) (i : N.Inputs) :
  R.v21679 (state s) (inputs i) = Zmod.unsigned (N.v21679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21679 s i)) at 1.
  unfold R.v21679, N.v21679.
  rewrite ?node_21674.
  rewrite ?node_21678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21680 (s : N.State) (i : N.Inputs) :
  R.v21680 (state s) (inputs i) = Zmod.unsigned (N.v21680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21680 s i)) at 1.
  unfold R.v21680, N.v21680.
  unfold R.v6, N.v6.
  rewrite ?node_21679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21681 (s : N.State) (i : N.Inputs) :
  R.v21681 (state s) (inputs i) = Zmod.unsigned (N.v21681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21681 s i)) at 1.
  unfold R.v21681, N.v21681.
  rewrite ?node_7716.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21682 (s : N.State) (i : N.Inputs) :
  R.v21682 (state s) (inputs i) = Zmod.unsigned (N.v21682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21682 s i)) at 1.
  unfold R.v21682, N.v21682.
  unfold R.v6, N.v6.
  rewrite ?node_7879.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21683 (s : N.State) (i : N.Inputs) :
  R.v21683 (state s) (inputs i) = Zmod.unsigned (N.v21683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21683 s i)) at 1.
  unfold R.v21683, N.v21683.
  rewrite ?node_21681.
  rewrite ?node_21682.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21684 (s : N.State) (i : N.Inputs) :
  R.v21684 (state s) (inputs i) = Zmod.unsigned (N.v21684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21684 s i)) at 1.
  unfold R.v21684, N.v21684.
  rewrite ?node_21680.
  rewrite ?node_21683.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21685 (s : N.State) (i : N.Inputs) :
  R.v21685 (state s) (inputs i) = Zmod.unsigned (N.v21685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21685 s i)) at 1.
  unfold R.v21685, N.v21685.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21686 (s : N.State) (i : N.Inputs) :
  R.v21686 (state s) (inputs i) = Zmod.unsigned (N.v21686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21686 s i)) at 1.
  unfold R.v21686, N.v21686.
  rewrite ?node_7723.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21687 (s : N.State) (i : N.Inputs) :
  R.v21687 (state s) (inputs i) = Zmod.unsigned (N.v21687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21687 s i)) at 1.
  unfold R.v21687, N.v21687.
  unfold R.v16463, N.v16463.
  rewrite !state_r585_nr_5F585.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r585_nr_5F585 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21688 (s : N.State) (i : N.Inputs) :
  R.v21688 (state s) (inputs i) = Zmod.unsigned (N.v21688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21688 s i)) at 1.
  unfold R.v21688, N.v21688.
  unfold R.v16463, N.v16463.
  rewrite !state_r584_nr_5F584.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r584_nr_5F584 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21689 (s : N.State) (i : N.Inputs) :
  R.v21689 (state s) (inputs i) = Zmod.unsigned (N.v21689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21689 s i)) at 1.
  unfold R.v21689, N.v21689.
  unfold R.v6, N.v6.
  rewrite !state_r583_nr_5F583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r583_nr_5F583 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21690 (s : N.State) (i : N.Inputs) :
  R.v21690 (state s) (inputs i) = Zmod.unsigned (N.v21690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21690 s i)) at 1.
  unfold R.v21690, N.v21690.
  unfold R.v6, N.v6.
  rewrite !state_r582_nr_5F582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r582_nr_5F582 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21691 (s : N.State) (i : N.Inputs) :
  R.v21691 (state s) (inputs i) = Zmod.unsigned (N.v21691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21691 s i)) at 1.
  unfold R.v21691, N.v21691.
  rewrite ?node_21689.
  rewrite ?node_21690.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21692 (s : N.State) (i : N.Inputs) :
  R.v21692 (state s) (inputs i) = Zmod.unsigned (N.v21692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21692 s i)) at 1.
  unfold R.v21692, N.v21692.
  unfold R.v16484, N.v16484.
  rewrite ?node_21691.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21693 (s : N.State) (i : N.Inputs) :
  R.v21693 (state s) (inputs i) = Zmod.unsigned (N.v21693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21693 s i)) at 1.
  unfold R.v21693, N.v21693.
  rewrite ?node_21686.
  rewrite ?node_21687.
  rewrite ?node_21688.
  rewrite ?node_21692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21694 (s : N.State) (i : N.Inputs) :
  R.v21694 (state s) (inputs i) = Zmod.unsigned (N.v21694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21694 s i)) at 1.
  unfold R.v21694, N.v21694.
  unfold R.v6, N.v6.
  rewrite ?node_21693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21695 (s : N.State) (i : N.Inputs) :
  R.v21695 (state s) (inputs i) = Zmod.unsigned (N.v21695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21695 s i)) at 1.
  unfold R.v21695, N.v21695.
  rewrite ?node_7724.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21696 (s : N.State) (i : N.Inputs) :
  R.v21696 (state s) (inputs i) = Zmod.unsigned (N.v21696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21696 s i)) at 1.
  unfold R.v21696, N.v21696.
  unfold R.v6, N.v6.
  rewrite ?node_7837.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21697 (s : N.State) (i : N.Inputs) :
  R.v21697 (state s) (inputs i) = Zmod.unsigned (N.v21697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21697 s i)) at 1.
  unfold R.v21697, N.v21697.
  unfold R.v6, N.v6.
  rewrite ?node_7882.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21698 (s : N.State) (i : N.Inputs) :
  R.v21698 (state s) (inputs i) = Zmod.unsigned (N.v21698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21698 s i)) at 1.
  unfold R.v21698, N.v21698.
  rewrite ?node_21695.
  rewrite ?node_21696.
  rewrite ?node_21697.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21699 (s : N.State) (i : N.Inputs) :
  R.v21699 (state s) (inputs i) = Zmod.unsigned (N.v21699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21699 s i)) at 1.
  unfold R.v21699, N.v21699.
  rewrite ?node_21694.
  rewrite ?node_21698.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21700 (s : N.State) (i : N.Inputs) :
  R.v21700 (state s) (inputs i) = Zmod.unsigned (N.v21700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21700 s i)) at 1.
  unfold R.v21700, N.v21700.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21701 (s : N.State) (i : N.Inputs) :
  R.v21701 (state s) (inputs i) = Zmod.unsigned (N.v21701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21701 s i)) at 1.
  unfold R.v21701, N.v21701.
  unfold R.v16463, N.v16463.
  rewrite !state_r584_nr_5F584.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r584_nr_5F584 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21702 (s : N.State) (i : N.Inputs) :
  R.v21702 (state s) (inputs i) = Zmod.unsigned (N.v21702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21702 s i)) at 1.
  unfold R.v21702, N.v21702.
  unfold R.v6, N.v6.
  rewrite !state_r583_nr_5F583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r583_nr_5F583 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21703 (s : N.State) (i : N.Inputs) :
  R.v21703 (state s) (inputs i) = Zmod.unsigned (N.v21703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21703 s i)) at 1.
  unfold R.v21703, N.v21703.
  unfold R.v6, N.v6.
  rewrite !state_r582_nr_5F582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r582_nr_5F582 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21704 (s : N.State) (i : N.Inputs) :
  R.v21704 (state s) (inputs i) = Zmod.unsigned (N.v21704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21704 s i)) at 1.
  unfold R.v21704, N.v21704.
  rewrite ?node_21702.
  rewrite ?node_21703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21705 (s : N.State) (i : N.Inputs) :
  R.v21705 (state s) (inputs i) = Zmod.unsigned (N.v21705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21705 s i)) at 1.
  unfold R.v21705, N.v21705.
  unfold R.v16484, N.v16484.
  rewrite ?node_21704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21706 (s : N.State) (i : N.Inputs) :
  R.v21706 (state s) (inputs i) = Zmod.unsigned (N.v21706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21706 s i)) at 1.
  unfold R.v21706, N.v21706.
  rewrite ?node_21701.
  rewrite ?node_21705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21707 (s : N.State) (i : N.Inputs) :
  R.v21707 (state s) (inputs i) = Zmod.unsigned (N.v21707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21707 s i)) at 1.
  unfold R.v21707, N.v21707.
  unfold R.v6, N.v6.
  rewrite ?node_21706.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21708 (s : N.State) (i : N.Inputs) :
  R.v21708 (state s) (inputs i) = Zmod.unsigned (N.v21708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21708 s i)) at 1.
  unfold R.v21708, N.v21708.
  rewrite ?node_7719.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21709 (s : N.State) (i : N.Inputs) :
  R.v21709 (state s) (inputs i) = Zmod.unsigned (N.v21709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21709 s i)) at 1.
  unfold R.v21709, N.v21709.
  unfold R.v6, N.v6.
  rewrite ?node_7837.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21710 (s : N.State) (i : N.Inputs) :
  R.v21710 (state s) (inputs i) = Zmod.unsigned (N.v21710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21710 s i)) at 1.
  unfold R.v21710, N.v21710.
  rewrite ?node_21708.
  rewrite ?node_21709.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21711 (s : N.State) (i : N.Inputs) :
  R.v21711 (state s) (inputs i) = Zmod.unsigned (N.v21711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21711 s i)) at 1.
  unfold R.v21711, N.v21711.
  rewrite ?node_21707.
  rewrite ?node_21710.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21712 (s : N.State) (i : N.Inputs) :
  R.v21712 (state s) (inputs i) = Zmod.unsigned (N.v21712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21712 s i)) at 1.
  unfold R.v21712, N.v21712.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21713 (s : N.State) (i : N.Inputs) :
  R.v21713 (state s) (inputs i) = Zmod.unsigned (N.v21713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21713 s i)) at 1.
  unfold R.v21713, N.v21713.
  rewrite ?node_7723.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21714 (s : N.State) (i : N.Inputs) :
  R.v21714 (state s) (inputs i) = Zmod.unsigned (N.v21714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21714 s i)) at 1.
  unfold R.v21714, N.v21714.
  unfold R.v6, N.v6.
  rewrite !state_r585_nr_5F585.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r585_nr_5F585 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21715 (s : N.State) (i : N.Inputs) :
  R.v21715 (state s) (inputs i) = Zmod.unsigned (N.v21715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21715 s i)) at 1.
  unfold R.v21715, N.v21715.
  unfold R.v6, N.v6.
  rewrite ?node_7719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21716 (s : N.State) (i : N.Inputs) :
  R.v21716 (state s) (inputs i) = Zmod.unsigned (N.v21716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21716 s i)) at 1.
  unfold R.v21716, N.v21716.
  rewrite ?node_21714.
  rewrite ?node_21715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21717 (s : N.State) (i : N.Inputs) :
  R.v21717 (state s) (inputs i) = Zmod.unsigned (N.v21717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21717 s i)) at 1.
  unfold R.v21717, N.v21717.
  unfold R.v16484, N.v16484.
  rewrite ?node_21716.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21718 (s : N.State) (i : N.Inputs) :
  R.v21718 (state s) (inputs i) = Zmod.unsigned (N.v21718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21718 s i)) at 1.
  unfold R.v21718, N.v21718.
  rewrite ?node_21713.
  rewrite ?node_21717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21719 (s : N.State) (i : N.Inputs) :
  R.v21719 (state s) (inputs i) = Zmod.unsigned (N.v21719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21719 s i)) at 1.
  unfold R.v21719, N.v21719.
  unfold R.v6, N.v6.
  rewrite ?node_21718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21720 (s : N.State) (i : N.Inputs) :
  R.v21720 (state s) (inputs i) = Zmod.unsigned (N.v21720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21720 s i)) at 1.
  unfold R.v21720, N.v21720.
  rewrite ?node_7724.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21721 (s : N.State) (i : N.Inputs) :
  R.v21721 (state s) (inputs i) = Zmod.unsigned (N.v21721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21721 s i)) at 1.
  unfold R.v21721, N.v21721.
  unfold R.v6, N.v6.
  rewrite ?node_7882.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21722 (s : N.State) (i : N.Inputs) :
  R.v21722 (state s) (inputs i) = Zmod.unsigned (N.v21722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21722 s i)) at 1.
  unfold R.v21722, N.v21722.
  rewrite ?node_21720.
  rewrite ?node_21721.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21723 (s : N.State) (i : N.Inputs) :
  R.v21723 (state s) (inputs i) = Zmod.unsigned (N.v21723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21723 s i)) at 1.
  unfold R.v21723, N.v21723.
  rewrite ?node_21719.
  rewrite ?node_21722.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21724 (s : N.State) (i : N.Inputs) :
  R.v21724 (state s) (inputs i) = Zmod.unsigned (N.v21724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21724 s i)) at 1.
  unfold R.v21724, N.v21724.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21725 (s : N.State) (i : N.Inputs) :
  R.v21725 (state s) (inputs i) = Zmod.unsigned (N.v21725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21725 s i)) at 1.
  unfold R.v21725, N.v21725.
  rewrite ?node_7731.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21726 (s : N.State) (i : N.Inputs) :
  R.v21726 (state s) (inputs i) = Zmod.unsigned (N.v21726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21726 s i)) at 1.
  unfold R.v21726, N.v21726.
  unfold R.v16463, N.v16463.
  rewrite !state_r589_nr_5F589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r589_nr_5F589 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21727 (s : N.State) (i : N.Inputs) :
  R.v21727 (state s) (inputs i) = Zmod.unsigned (N.v21727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21727 s i)) at 1.
  unfold R.v21727, N.v21727.
  unfold R.v16463, N.v16463.
  rewrite !state_r588_nr_5F588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r588_nr_5F588 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21728 (s : N.State) (i : N.Inputs) :
  R.v21728 (state s) (inputs i) = Zmod.unsigned (N.v21728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21728 s i)) at 1.
  unfold R.v21728, N.v21728.
  unfold R.v6, N.v6.
  rewrite !state_r587_nr_5F587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r587_nr_5F587 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21729 (s : N.State) (i : N.Inputs) :
  R.v21729 (state s) (inputs i) = Zmod.unsigned (N.v21729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21729 s i)) at 1.
  unfold R.v21729, N.v21729.
  unfold R.v6, N.v6.
  rewrite !state_r586_nr_5F586.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r586_nr_5F586 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21730 (s : N.State) (i : N.Inputs) :
  R.v21730 (state s) (inputs i) = Zmod.unsigned (N.v21730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21730 s i)) at 1.
  unfold R.v21730, N.v21730.
  rewrite ?node_21728.
  rewrite ?node_21729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21731 (s : N.State) (i : N.Inputs) :
  R.v21731 (state s) (inputs i) = Zmod.unsigned (N.v21731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21731 s i)) at 1.
  unfold R.v21731, N.v21731.
  unfold R.v16484, N.v16484.
  rewrite ?node_21730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21732 (s : N.State) (i : N.Inputs) :
  R.v21732 (state s) (inputs i) = Zmod.unsigned (N.v21732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21732 s i)) at 1.
  unfold R.v21732, N.v21732.
  rewrite ?node_21725.
  rewrite ?node_21726.
  rewrite ?node_21727.
  rewrite ?node_21731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21733 (s : N.State) (i : N.Inputs) :
  R.v21733 (state s) (inputs i) = Zmod.unsigned (N.v21733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21733 s i)) at 1.
  unfold R.v21733, N.v21733.
  unfold R.v6, N.v6.
  rewrite ?node_21732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21734 (s : N.State) (i : N.Inputs) :
  R.v21734 (state s) (inputs i) = Zmod.unsigned (N.v21734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21734 s i)) at 1.
  unfold R.v21734, N.v21734.
  rewrite ?node_7732.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21735 (s : N.State) (i : N.Inputs) :
  R.v21735 (state s) (inputs i) = Zmod.unsigned (N.v21735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21735 s i)) at 1.
  unfold R.v21735, N.v21735.
  unfold R.v6, N.v6.
  rewrite ?node_7845.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21736 (s : N.State) (i : N.Inputs) :
  R.v21736 (state s) (inputs i) = Zmod.unsigned (N.v21736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21736 s i)) at 1.
  unfold R.v21736, N.v21736.
  unfold R.v6, N.v6.
  rewrite ?node_7886.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21737 (s : N.State) (i : N.Inputs) :
  R.v21737 (state s) (inputs i) = Zmod.unsigned (N.v21737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21737 s i)) at 1.
  unfold R.v21737, N.v21737.
  rewrite ?node_21734.
  rewrite ?node_21735.
  rewrite ?node_21736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21738 (s : N.State) (i : N.Inputs) :
  R.v21738 (state s) (inputs i) = Zmod.unsigned (N.v21738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21738 s i)) at 1.
  unfold R.v21738, N.v21738.
  rewrite ?node_21733.
  rewrite ?node_21737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21739 (s : N.State) (i : N.Inputs) :
  R.v21739 (state s) (inputs i) = Zmod.unsigned (N.v21739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21739 s i)) at 1.
  unfold R.v21739, N.v21739.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21740 (s : N.State) (i : N.Inputs) :
  R.v21740 (state s) (inputs i) = Zmod.unsigned (N.v21740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21740 s i)) at 1.
  unfold R.v21740, N.v21740.
  unfold R.v16463, N.v16463.
  rewrite !state_r588_nr_5F588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r588_nr_5F588 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21741 (s : N.State) (i : N.Inputs) :
  R.v21741 (state s) (inputs i) = Zmod.unsigned (N.v21741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21741 s i)) at 1.
  unfold R.v21741, N.v21741.
  unfold R.v6, N.v6.
  rewrite !state_r587_nr_5F587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r587_nr_5F587 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21742 (s : N.State) (i : N.Inputs) :
  R.v21742 (state s) (inputs i) = Zmod.unsigned (N.v21742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21742 s i)) at 1.
  unfold R.v21742, N.v21742.
  unfold R.v6, N.v6.
  rewrite !state_r586_nr_5F586.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r586_nr_5F586 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21743 (s : N.State) (i : N.Inputs) :
  R.v21743 (state s) (inputs i) = Zmod.unsigned (N.v21743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21743 s i)) at 1.
  unfold R.v21743, N.v21743.
  rewrite ?node_21741.
  rewrite ?node_21742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21744 (s : N.State) (i : N.Inputs) :
  R.v21744 (state s) (inputs i) = Zmod.unsigned (N.v21744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21744 s i)) at 1.
  unfold R.v21744, N.v21744.
  unfold R.v16484, N.v16484.
  rewrite ?node_21743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21745 (s : N.State) (i : N.Inputs) :
  R.v21745 (state s) (inputs i) = Zmod.unsigned (N.v21745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21745 s i)) at 1.
  unfold R.v21745, N.v21745.
  rewrite ?node_21740.
  rewrite ?node_21744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21746 (s : N.State) (i : N.Inputs) :
  R.v21746 (state s) (inputs i) = Zmod.unsigned (N.v21746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21746 s i)) at 1.
  unfold R.v21746, N.v21746.
  unfold R.v6, N.v6.
  rewrite ?node_21745.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21747 (s : N.State) (i : N.Inputs) :
  R.v21747 (state s) (inputs i) = Zmod.unsigned (N.v21747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21747 s i)) at 1.
  unfold R.v21747, N.v21747.
  rewrite ?node_7727.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21748 (s : N.State) (i : N.Inputs) :
  R.v21748 (state s) (inputs i) = Zmod.unsigned (N.v21748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21748 s i)) at 1.
  unfold R.v21748, N.v21748.
  unfold R.v6, N.v6.
  rewrite ?node_7845.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21749 (s : N.State) (i : N.Inputs) :
  R.v21749 (state s) (inputs i) = Zmod.unsigned (N.v21749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21749 s i)) at 1.
  unfold R.v21749, N.v21749.
  rewrite ?node_21747.
  rewrite ?node_21748.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21750 (s : N.State) (i : N.Inputs) :
  R.v21750 (state s) (inputs i) = Zmod.unsigned (N.v21750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21750 s i)) at 1.
  unfold R.v21750, N.v21750.
  rewrite ?node_21746.
  rewrite ?node_21749.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21751 (s : N.State) (i : N.Inputs) :
  R.v21751 (state s) (inputs i) = Zmod.unsigned (N.v21751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21751 s i)) at 1.
  unfold R.v21751, N.v21751.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21752 (s : N.State) (i : N.Inputs) :
  R.v21752 (state s) (inputs i) = Zmod.unsigned (N.v21752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21752 s i)) at 1.
  unfold R.v21752, N.v21752.
  rewrite ?node_7731.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21753 (s : N.State) (i : N.Inputs) :
  R.v21753 (state s) (inputs i) = Zmod.unsigned (N.v21753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21753 s i)) at 1.
  unfold R.v21753, N.v21753.
  unfold R.v6, N.v6.
  rewrite !state_r589_nr_5F589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r589_nr_5F589 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21754 (s : N.State) (i : N.Inputs) :
  R.v21754 (state s) (inputs i) = Zmod.unsigned (N.v21754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21754 s i)) at 1.
  unfold R.v21754, N.v21754.
  unfold R.v6, N.v6.
  rewrite ?node_7727.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21755 (s : N.State) (i : N.Inputs) :
  R.v21755 (state s) (inputs i) = Zmod.unsigned (N.v21755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21755 s i)) at 1.
  unfold R.v21755, N.v21755.
  rewrite ?node_21753.
  rewrite ?node_21754.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21756 (s : N.State) (i : N.Inputs) :
  R.v21756 (state s) (inputs i) = Zmod.unsigned (N.v21756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21756 s i)) at 1.
  unfold R.v21756, N.v21756.
  unfold R.v16484, N.v16484.
  rewrite ?node_21755.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21757 (s : N.State) (i : N.Inputs) :
  R.v21757 (state s) (inputs i) = Zmod.unsigned (N.v21757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21757 s i)) at 1.
  unfold R.v21757, N.v21757.
  rewrite ?node_21752.
  rewrite ?node_21756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21758 (s : N.State) (i : N.Inputs) :
  R.v21758 (state s) (inputs i) = Zmod.unsigned (N.v21758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21758 s i)) at 1.
  unfold R.v21758, N.v21758.
  unfold R.v6, N.v6.
  rewrite ?node_21757.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21759 (s : N.State) (i : N.Inputs) :
  R.v21759 (state s) (inputs i) = Zmod.unsigned (N.v21759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21759 s i)) at 1.
  unfold R.v21759, N.v21759.
  rewrite ?node_7732.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21760 (s : N.State) (i : N.Inputs) :
  R.v21760 (state s) (inputs i) = Zmod.unsigned (N.v21760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21760 s i)) at 1.
  unfold R.v21760, N.v21760.
  unfold R.v6, N.v6.
  rewrite ?node_7886.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21761 (s : N.State) (i : N.Inputs) :
  R.v21761 (state s) (inputs i) = Zmod.unsigned (N.v21761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21761 s i)) at 1.
  unfold R.v21761, N.v21761.
  rewrite ?node_21759.
  rewrite ?node_21760.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21762 (s : N.State) (i : N.Inputs) :
  R.v21762 (state s) (inputs i) = Zmod.unsigned (N.v21762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21762 s i)) at 1.
  unfold R.v21762, N.v21762.
  rewrite ?node_21758.
  rewrite ?node_21761.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21763 (s : N.State) (i : N.Inputs) :
  R.v21763 (state s) (inputs i) = Zmod.unsigned (N.v21763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21763 s i)) at 1.
  unfold R.v21763, N.v21763.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21764 (s : N.State) (i : N.Inputs) :
  R.v21764 (state s) (inputs i) = Zmod.unsigned (N.v21764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21764 s i)) at 1.
  unfold R.v21764, N.v21764.
  rewrite ?node_7743.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21765 (s : N.State) (i : N.Inputs) :
  R.v21765 (state s) (inputs i) = Zmod.unsigned (N.v21765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21765 s i)) at 1.
  unfold R.v21765, N.v21765.
  unfold R.v16463, N.v16463.
  rewrite !state_r593_nr_5F593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r593_nr_5F593 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21766 (s : N.State) (i : N.Inputs) :
  R.v21766 (state s) (inputs i) = Zmod.unsigned (N.v21766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21766 s i)) at 1.
  unfold R.v21766, N.v21766.
  unfold R.v16463, N.v16463.
  rewrite !state_r592_nr_5F592.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r592_nr_5F592 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21767 (s : N.State) (i : N.Inputs) :
  R.v21767 (state s) (inputs i) = Zmod.unsigned (N.v21767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21767 s i)) at 1.
  unfold R.v21767, N.v21767.
  unfold R.v6, N.v6.
  rewrite !state_r591_nr_5F591.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r591_nr_5F591 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21768 (s : N.State) (i : N.Inputs) :
  R.v21768 (state s) (inputs i) = Zmod.unsigned (N.v21768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21768 s i)) at 1.
  unfold R.v21768, N.v21768.
  unfold R.v6, N.v6.
  rewrite !state_r590_nr_5F590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r590_nr_5F590 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21769 (s : N.State) (i : N.Inputs) :
  R.v21769 (state s) (inputs i) = Zmod.unsigned (N.v21769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21769 s i)) at 1.
  unfold R.v21769, N.v21769.
  rewrite ?node_21767.
  rewrite ?node_21768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21770 (s : N.State) (i : N.Inputs) :
  R.v21770 (state s) (inputs i) = Zmod.unsigned (N.v21770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21770 s i)) at 1.
  unfold R.v21770, N.v21770.
  unfold R.v16484, N.v16484.
  rewrite ?node_21769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21771 (s : N.State) (i : N.Inputs) :
  R.v21771 (state s) (inputs i) = Zmod.unsigned (N.v21771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21771 s i)) at 1.
  unfold R.v21771, N.v21771.
  rewrite ?node_21764.
  rewrite ?node_21765.
  rewrite ?node_21766.
  rewrite ?node_21770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21772 (s : N.State) (i : N.Inputs) :
  R.v21772 (state s) (inputs i) = Zmod.unsigned (N.v21772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21772 s i)) at 1.
  unfold R.v21772, N.v21772.
  unfold R.v6, N.v6.
  rewrite ?node_21771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21773 (s : N.State) (i : N.Inputs) :
  R.v21773 (state s) (inputs i) = Zmod.unsigned (N.v21773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21773 s i)) at 1.
  unfold R.v21773, N.v21773.
  rewrite ?node_7744.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21774 (s : N.State) (i : N.Inputs) :
  R.v21774 (state s) (inputs i) = Zmod.unsigned (N.v21774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21774 s i)) at 1.
  unfold R.v21774, N.v21774.
  unfold R.v6, N.v6.
  rewrite ?node_7857.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21775 (s : N.State) (i : N.Inputs) :
  R.v21775 (state s) (inputs i) = Zmod.unsigned (N.v21775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21775 s i)) at 1.
  unfold R.v21775, N.v21775.
  unfold R.v6, N.v6.
  rewrite ?node_7890.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21776 (s : N.State) (i : N.Inputs) :
  R.v21776 (state s) (inputs i) = Zmod.unsigned (N.v21776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21776 s i)) at 1.
  unfold R.v21776, N.v21776.
  rewrite ?node_21773.
  rewrite ?node_21774.
  rewrite ?node_21775.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21777 (s : N.State) (i : N.Inputs) :
  R.v21777 (state s) (inputs i) = Zmod.unsigned (N.v21777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21777 s i)) at 1.
  unfold R.v21777, N.v21777.
  rewrite ?node_21772.
  rewrite ?node_21776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21778 (s : N.State) (i : N.Inputs) :
  R.v21778 (state s) (inputs i) = Zmod.unsigned (N.v21778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21778 s i)) at 1.
  unfold R.v21778, N.v21778.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21779 (s : N.State) (i : N.Inputs) :
  R.v21779 (state s) (inputs i) = Zmod.unsigned (N.v21779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21779 s i)) at 1.
  unfold R.v21779, N.v21779.
  unfold R.v16463, N.v16463.
  rewrite !state_r592_nr_5F592.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r592_nr_5F592 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21780 (s : N.State) (i : N.Inputs) :
  R.v21780 (state s) (inputs i) = Zmod.unsigned (N.v21780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21780 s i)) at 1.
  unfold R.v21780, N.v21780.
  unfold R.v6, N.v6.
  rewrite !state_r591_nr_5F591.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r591_nr_5F591 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21781 (s : N.State) (i : N.Inputs) :
  R.v21781 (state s) (inputs i) = Zmod.unsigned (N.v21781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21781 s i)) at 1.
  unfold R.v21781, N.v21781.
  unfold R.v6, N.v6.
  rewrite !state_r590_nr_5F590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r590_nr_5F590 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21782 (s : N.State) (i : N.Inputs) :
  R.v21782 (state s) (inputs i) = Zmod.unsigned (N.v21782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21782 s i)) at 1.
  unfold R.v21782, N.v21782.
  rewrite ?node_21780.
  rewrite ?node_21781.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21783 (s : N.State) (i : N.Inputs) :
  R.v21783 (state s) (inputs i) = Zmod.unsigned (N.v21783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21783 s i)) at 1.
  unfold R.v21783, N.v21783.
  unfold R.v16484, N.v16484.
  rewrite ?node_21782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21784 (s : N.State) (i : N.Inputs) :
  R.v21784 (state s) (inputs i) = Zmod.unsigned (N.v21784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21784 s i)) at 1.
  unfold R.v21784, N.v21784.
  rewrite ?node_21779.
  rewrite ?node_21783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21785 (s : N.State) (i : N.Inputs) :
  R.v21785 (state s) (inputs i) = Zmod.unsigned (N.v21785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21785 s i)) at 1.
  unfold R.v21785, N.v21785.
  unfold R.v6, N.v6.
  rewrite ?node_21784.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21786 (s : N.State) (i : N.Inputs) :
  R.v21786 (state s) (inputs i) = Zmod.unsigned (N.v21786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21786 s i)) at 1.
  unfold R.v21786, N.v21786.
  rewrite ?node_7739.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21787 (s : N.State) (i : N.Inputs) :
  R.v21787 (state s) (inputs i) = Zmod.unsigned (N.v21787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21787 s i)) at 1.
  unfold R.v21787, N.v21787.
  unfold R.v6, N.v6.
  rewrite ?node_7857.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21788 (s : N.State) (i : N.Inputs) :
  R.v21788 (state s) (inputs i) = Zmod.unsigned (N.v21788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21788 s i)) at 1.
  unfold R.v21788, N.v21788.
  rewrite ?node_21786.
  rewrite ?node_21787.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21789 (s : N.State) (i : N.Inputs) :
  R.v21789 (state s) (inputs i) = Zmod.unsigned (N.v21789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21789 s i)) at 1.
  unfold R.v21789, N.v21789.
  rewrite ?node_21785.
  rewrite ?node_21788.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21790 (s : N.State) (i : N.Inputs) :
  R.v21790 (state s) (inputs i) = Zmod.unsigned (N.v21790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21790 s i)) at 1.
  unfold R.v21790, N.v21790.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21791 (s : N.State) (i : N.Inputs) :
  R.v21791 (state s) (inputs i) = Zmod.unsigned (N.v21791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21791 s i)) at 1.
  unfold R.v21791, N.v21791.
  rewrite ?node_7743.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21792 (s : N.State) (i : N.Inputs) :
  R.v21792 (state s) (inputs i) = Zmod.unsigned (N.v21792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21792 s i)) at 1.
  unfold R.v21792, N.v21792.
  unfold R.v6, N.v6.
  rewrite !state_r593_nr_5F593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r593_nr_5F593 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21793 (s : N.State) (i : N.Inputs) :
  R.v21793 (state s) (inputs i) = Zmod.unsigned (N.v21793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21793 s i)) at 1.
  unfold R.v21793, N.v21793.
  unfold R.v6, N.v6.
  rewrite ?node_7739.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21794 (s : N.State) (i : N.Inputs) :
  R.v21794 (state s) (inputs i) = Zmod.unsigned (N.v21794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21794 s i)) at 1.
  unfold R.v21794, N.v21794.
  rewrite ?node_21792.
  rewrite ?node_21793.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21795 (s : N.State) (i : N.Inputs) :
  R.v21795 (state s) (inputs i) = Zmod.unsigned (N.v21795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21795 s i)) at 1.
  unfold R.v21795, N.v21795.
  unfold R.v16484, N.v16484.
  rewrite ?node_21794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21796 (s : N.State) (i : N.Inputs) :
  R.v21796 (state s) (inputs i) = Zmod.unsigned (N.v21796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21796 s i)) at 1.
  unfold R.v21796, N.v21796.
  rewrite ?node_21791.
  rewrite ?node_21795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21797 (s : N.State) (i : N.Inputs) :
  R.v21797 (state s) (inputs i) = Zmod.unsigned (N.v21797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21797 s i)) at 1.
  unfold R.v21797, N.v21797.
  unfold R.v6, N.v6.
  rewrite ?node_21796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21798 (s : N.State) (i : N.Inputs) :
  R.v21798 (state s) (inputs i) = Zmod.unsigned (N.v21798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21798 s i)) at 1.
  unfold R.v21798, N.v21798.
  rewrite ?node_7744.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21799 (s : N.State) (i : N.Inputs) :
  R.v21799 (state s) (inputs i) = Zmod.unsigned (N.v21799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21799 s i)) at 1.
  unfold R.v21799, N.v21799.
  unfold R.v6, N.v6.
  rewrite ?node_7890.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21800 (s : N.State) (i : N.Inputs) :
  R.v21800 (state s) (inputs i) = Zmod.unsigned (N.v21800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21800 s i)) at 1.
  unfold R.v21800, N.v21800.
  rewrite ?node_21798.
  rewrite ?node_21799.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21801 (s : N.State) (i : N.Inputs) :
  R.v21801 (state s) (inputs i) = Zmod.unsigned (N.v21801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21801 s i)) at 1.
  unfold R.v21801, N.v21801.
  rewrite ?node_21797.
  rewrite ?node_21800.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21802 (s : N.State) (i : N.Inputs) :
  R.v21802 (state s) (inputs i) = Zmod.unsigned (N.v21802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21802 s i)) at 1.
  unfold R.v21802, N.v21802.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21803 (s : N.State) (i : N.Inputs) :
  R.v21803 (state s) (inputs i) = Zmod.unsigned (N.v21803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21803 s i)) at 1.
  unfold R.v21803, N.v21803.
  rewrite ?node_7750.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21804 (s : N.State) (i : N.Inputs) :
  R.v21804 (state s) (inputs i) = Zmod.unsigned (N.v21804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21804 s i)) at 1.
  unfold R.v21804, N.v21804.
  unfold R.v16463, N.v16463.
  rewrite !state_r597_nr_5F597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r597_nr_5F597 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21805 (s : N.State) (i : N.Inputs) :
  R.v21805 (state s) (inputs i) = Zmod.unsigned (N.v21805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21805 s i)) at 1.
  unfold R.v21805, N.v21805.
  unfold R.v16463, N.v16463.
  rewrite !state_r596_nr_5F596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r596_nr_5F596 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21806 (s : N.State) (i : N.Inputs) :
  R.v21806 (state s) (inputs i) = Zmod.unsigned (N.v21806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21806 s i)) at 1.
  unfold R.v21806, N.v21806.
  unfold R.v6, N.v6.
  rewrite !state_r595_nr_5F595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r595_nr_5F595 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21807 (s : N.State) (i : N.Inputs) :
  R.v21807 (state s) (inputs i) = Zmod.unsigned (N.v21807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21807 s i)) at 1.
  unfold R.v21807, N.v21807.
  unfold R.v6, N.v6.
  rewrite !state_r594_nr_5F594.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r594_nr_5F594 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21808 (s : N.State) (i : N.Inputs) :
  R.v21808 (state s) (inputs i) = Zmod.unsigned (N.v21808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21808 s i)) at 1.
  unfold R.v21808, N.v21808.
  rewrite ?node_21806.
  rewrite ?node_21807.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21809 (s : N.State) (i : N.Inputs) :
  R.v21809 (state s) (inputs i) = Zmod.unsigned (N.v21809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21809 s i)) at 1.
  unfold R.v21809, N.v21809.
  unfold R.v16484, N.v16484.
  rewrite ?node_21808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21810 (s : N.State) (i : N.Inputs) :
  R.v21810 (state s) (inputs i) = Zmod.unsigned (N.v21810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21810 s i)) at 1.
  unfold R.v21810, N.v21810.
  rewrite ?node_21803.
  rewrite ?node_21804.
  rewrite ?node_21805.
  rewrite ?node_21809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21811 (s : N.State) (i : N.Inputs) :
  R.v21811 (state s) (inputs i) = Zmod.unsigned (N.v21811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21811 s i)) at 1.
  unfold R.v21811, N.v21811.
  unfold R.v6, N.v6.
  rewrite ?node_21810.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21812 (s : N.State) (i : N.Inputs) :
  R.v21812 (state s) (inputs i) = Zmod.unsigned (N.v21812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21812 s i)) at 1.
  unfold R.v21812, N.v21812.
  rewrite ?node_7751.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21813 (s : N.State) (i : N.Inputs) :
  R.v21813 (state s) (inputs i) = Zmod.unsigned (N.v21813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21813 s i)) at 1.
  unfold R.v21813, N.v21813.
  unfold R.v6, N.v6.
  rewrite ?node_7864.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21814 (s : N.State) (i : N.Inputs) :
  R.v21814 (state s) (inputs i) = Zmod.unsigned (N.v21814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21814 s i)) at 1.
  unfold R.v21814, N.v21814.
  unfold R.v6, N.v6.
  rewrite ?node_7899.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21815 (s : N.State) (i : N.Inputs) :
  R.v21815 (state s) (inputs i) = Zmod.unsigned (N.v21815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21815 s i)) at 1.
  unfold R.v21815, N.v21815.
  rewrite ?node_21812.
  rewrite ?node_21813.
  rewrite ?node_21814.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21816 (s : N.State) (i : N.Inputs) :
  R.v21816 (state s) (inputs i) = Zmod.unsigned (N.v21816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21816 s i)) at 1.
  unfold R.v21816, N.v21816.
  rewrite ?node_21811.
  rewrite ?node_21815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21817 (s : N.State) (i : N.Inputs) :
  R.v21817 (state s) (inputs i) = Zmod.unsigned (N.v21817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21817 s i)) at 1.
  unfold R.v21817, N.v21817.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21818 (s : N.State) (i : N.Inputs) :
  R.v21818 (state s) (inputs i) = Zmod.unsigned (N.v21818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21818 s i)) at 1.
  unfold R.v21818, N.v21818.
  unfold R.v16463, N.v16463.
  rewrite !state_r596_nr_5F596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r596_nr_5F596 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21819 (s : N.State) (i : N.Inputs) :
  R.v21819 (state s) (inputs i) = Zmod.unsigned (N.v21819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21819 s i)) at 1.
  unfold R.v21819, N.v21819.
  unfold R.v6, N.v6.
  rewrite !state_r595_nr_5F595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r595_nr_5F595 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21820 (s : N.State) (i : N.Inputs) :
  R.v21820 (state s) (inputs i) = Zmod.unsigned (N.v21820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21820 s i)) at 1.
  unfold R.v21820, N.v21820.
  unfold R.v6, N.v6.
  rewrite !state_r594_nr_5F594.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r594_nr_5F594 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21821 (s : N.State) (i : N.Inputs) :
  R.v21821 (state s) (inputs i) = Zmod.unsigned (N.v21821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21821 s i)) at 1.
  unfold R.v21821, N.v21821.
  rewrite ?node_21819.
  rewrite ?node_21820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21822 (s : N.State) (i : N.Inputs) :
  R.v21822 (state s) (inputs i) = Zmod.unsigned (N.v21822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21822 s i)) at 1.
  unfold R.v21822, N.v21822.
  unfold R.v16484, N.v16484.
  rewrite ?node_21821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21823 (s : N.State) (i : N.Inputs) :
  R.v21823 (state s) (inputs i) = Zmod.unsigned (N.v21823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21823 s i)) at 1.
  unfold R.v21823, N.v21823.
  rewrite ?node_21818.
  rewrite ?node_21822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21824 (s : N.State) (i : N.Inputs) :
  R.v21824 (state s) (inputs i) = Zmod.unsigned (N.v21824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21824 s i)) at 1.
  unfold R.v21824, N.v21824.
  unfold R.v6, N.v6.
  rewrite ?node_21823.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21825 (s : N.State) (i : N.Inputs) :
  R.v21825 (state s) (inputs i) = Zmod.unsigned (N.v21825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21825 s i)) at 1.
  unfold R.v21825, N.v21825.
  rewrite ?node_7746.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21826 (s : N.State) (i : N.Inputs) :
  R.v21826 (state s) (inputs i) = Zmod.unsigned (N.v21826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21826 s i)) at 1.
  unfold R.v21826, N.v21826.
  unfold R.v6, N.v6.
  rewrite ?node_7864.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21827 (s : N.State) (i : N.Inputs) :
  R.v21827 (state s) (inputs i) = Zmod.unsigned (N.v21827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21827 s i)) at 1.
  unfold R.v21827, N.v21827.
  rewrite ?node_21825.
  rewrite ?node_21826.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21828 (s : N.State) (i : N.Inputs) :
  R.v21828 (state s) (inputs i) = Zmod.unsigned (N.v21828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21828 s i)) at 1.
  unfold R.v21828, N.v21828.
  rewrite ?node_21824.
  rewrite ?node_21827.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21829 (s : N.State) (i : N.Inputs) :
  R.v21829 (state s) (inputs i) = Zmod.unsigned (N.v21829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21829 s i)) at 1.
  unfold R.v21829, N.v21829.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21830 (s : N.State) (i : N.Inputs) :
  R.v21830 (state s) (inputs i) = Zmod.unsigned (N.v21830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21830 s i)) at 1.
  unfold R.v21830, N.v21830.
  rewrite ?node_7750.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21831 (s : N.State) (i : N.Inputs) :
  R.v21831 (state s) (inputs i) = Zmod.unsigned (N.v21831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21831 s i)) at 1.
  unfold R.v21831, N.v21831.
  unfold R.v6, N.v6.
  rewrite !state_r597_nr_5F597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r597_nr_5F597 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21832 (s : N.State) (i : N.Inputs) :
  R.v21832 (state s) (inputs i) = Zmod.unsigned (N.v21832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21832 s i)) at 1.
  unfold R.v21832, N.v21832.
  unfold R.v6, N.v6.
  rewrite ?node_7746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21833 (s : N.State) (i : N.Inputs) :
  R.v21833 (state s) (inputs i) = Zmod.unsigned (N.v21833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21833 s i)) at 1.
  unfold R.v21833, N.v21833.
  rewrite ?node_21831.
  rewrite ?node_21832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21834 (s : N.State) (i : N.Inputs) :
  R.v21834 (state s) (inputs i) = Zmod.unsigned (N.v21834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21834 s i)) at 1.
  unfold R.v21834, N.v21834.
  unfold R.v16484, N.v16484.
  rewrite ?node_21833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21835 (s : N.State) (i : N.Inputs) :
  R.v21835 (state s) (inputs i) = Zmod.unsigned (N.v21835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21835 s i)) at 1.
  unfold R.v21835, N.v21835.
  rewrite ?node_21830.
  rewrite ?node_21834.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21836 (s : N.State) (i : N.Inputs) :
  R.v21836 (state s) (inputs i) = Zmod.unsigned (N.v21836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21836 s i)) at 1.
  unfold R.v21836, N.v21836.
  unfold R.v6, N.v6.
  rewrite ?node_21835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21837 (s : N.State) (i : N.Inputs) :
  R.v21837 (state s) (inputs i) = Zmod.unsigned (N.v21837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21837 s i)) at 1.
  unfold R.v21837, N.v21837.
  rewrite ?node_7751.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21838 (s : N.State) (i : N.Inputs) :
  R.v21838 (state s) (inputs i) = Zmod.unsigned (N.v21838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21838 s i)) at 1.
  unfold R.v21838, N.v21838.
  unfold R.v6, N.v6.
  rewrite ?node_7899.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21839 (s : N.State) (i : N.Inputs) :
  R.v21839 (state s) (inputs i) = Zmod.unsigned (N.v21839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21839 s i)) at 1.
  unfold R.v21839, N.v21839.
  rewrite ?node_21837.
  rewrite ?node_21838.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21840 (s : N.State) (i : N.Inputs) :
  R.v21840 (state s) (inputs i) = Zmod.unsigned (N.v21840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21840 s i)) at 1.
  unfold R.v21840, N.v21840.
  rewrite ?node_21836.
  rewrite ?node_21839.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21841 (s : N.State) (i : N.Inputs) :
  R.v21841 (state s) (inputs i) = Zmod.unsigned (N.v21841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21841 s i)) at 1.
  unfold R.v21841, N.v21841.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21842 (s : N.State) (i : N.Inputs) :
  R.v21842 (state s) (inputs i) = Zmod.unsigned (N.v21842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21842 s i)) at 1.
  unfold R.v21842, N.v21842.
  rewrite ?node_7822.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21843 (s : N.State) (i : N.Inputs) :
  R.v21843 (state s) (inputs i) = Zmod.unsigned (N.v21843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21843 s i)) at 1.
  unfold R.v21843, N.v21843.
  unfold R.v16463, N.v16463.
  rewrite !state_r601_nr_5F601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r601_nr_5F601 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21844 (s : N.State) (i : N.Inputs) :
  R.v21844 (state s) (inputs i) = Zmod.unsigned (N.v21844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21844 s i)) at 1.
  unfold R.v21844, N.v21844.
  unfold R.v16463, N.v16463.
  rewrite !state_r600_nr_5F600.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r600_nr_5F600 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21845 (s : N.State) (i : N.Inputs) :
  R.v21845 (state s) (inputs i) = Zmod.unsigned (N.v21845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21845 s i)) at 1.
  unfold R.v21845, N.v21845.
  unfold R.v6, N.v6.
  rewrite !state_r599_nr_5F599.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r599_nr_5F599 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21846 (s : N.State) (i : N.Inputs) :
  R.v21846 (state s) (inputs i) = Zmod.unsigned (N.v21846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21846 s i)) at 1.
  unfold R.v21846, N.v21846.
  unfold R.v6, N.v6.
  rewrite !state_r598_nr_5F598.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r598_nr_5F598 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21847 (s : N.State) (i : N.Inputs) :
  R.v21847 (state s) (inputs i) = Zmod.unsigned (N.v21847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21847 s i)) at 1.
  unfold R.v21847, N.v21847.
  rewrite ?node_21845.
  rewrite ?node_21846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21848 (s : N.State) (i : N.Inputs) :
  R.v21848 (state s) (inputs i) = Zmod.unsigned (N.v21848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21848 s i)) at 1.
  unfold R.v21848, N.v21848.
  unfold R.v16484, N.v16484.
  rewrite ?node_21847.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21849 (s : N.State) (i : N.Inputs) :
  R.v21849 (state s) (inputs i) = Zmod.unsigned (N.v21849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21849 s i)) at 1.
  unfold R.v21849, N.v21849.
  rewrite ?node_21842.
  rewrite ?node_21843.
  rewrite ?node_21844.
  rewrite ?node_21848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21850 (s : N.State) (i : N.Inputs) :
  R.v21850 (state s) (inputs i) = Zmod.unsigned (N.v21850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21850 s i)) at 1.
  unfold R.v21850, N.v21850.
  unfold R.v6, N.v6.
  rewrite ?node_21849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21851 (s : N.State) (i : N.Inputs) :
  R.v21851 (state s) (inputs i) = Zmod.unsigned (N.v21851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21851 s i)) at 1.
  unfold R.v21851, N.v21851.
  rewrite ?node_7823.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21852 (s : N.State) (i : N.Inputs) :
  R.v21852 (state s) (inputs i) = Zmod.unsigned (N.v21852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21852 s i)) at 1.
  unfold R.v21852, N.v21852.
  unfold R.v6, N.v6.
  rewrite ?node_7939.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21853 (s : N.State) (i : N.Inputs) :
  R.v21853 (state s) (inputs i) = Zmod.unsigned (N.v21853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21853 s i)) at 1.
  unfold R.v21853, N.v21853.
  unfold R.v6, N.v6.
  rewrite ?node_7987.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21854 (s : N.State) (i : N.Inputs) :
  R.v21854 (state s) (inputs i) = Zmod.unsigned (N.v21854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21854 s i)) at 1.
  unfold R.v21854, N.v21854.
  rewrite ?node_21851.
  rewrite ?node_21852.
  rewrite ?node_21853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21855 (s : N.State) (i : N.Inputs) :
  R.v21855 (state s) (inputs i) = Zmod.unsigned (N.v21855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21855 s i)) at 1.
  unfold R.v21855, N.v21855.
  rewrite ?node_21850.
  rewrite ?node_21854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21856 (s : N.State) (i : N.Inputs) :
  R.v21856 (state s) (inputs i) = Zmod.unsigned (N.v21856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21856 s i)) at 1.
  unfold R.v21856, N.v21856.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21857 (s : N.State) (i : N.Inputs) :
  R.v21857 (state s) (inputs i) = Zmod.unsigned (N.v21857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21857 s i)) at 1.
  unfold R.v21857, N.v21857.
  unfold R.v16463, N.v16463.
  rewrite !state_r600_nr_5F600.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r600_nr_5F600 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21858 (s : N.State) (i : N.Inputs) :
  R.v21858 (state s) (inputs i) = Zmod.unsigned (N.v21858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21858 s i)) at 1.
  unfold R.v21858, N.v21858.
  unfold R.v6, N.v6.
  rewrite !state_r599_nr_5F599.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r599_nr_5F599 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21859 (s : N.State) (i : N.Inputs) :
  R.v21859 (state s) (inputs i) = Zmod.unsigned (N.v21859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21859 s i)) at 1.
  unfold R.v21859, N.v21859.
  unfold R.v6, N.v6.
  rewrite !state_r598_nr_5F598.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r598_nr_5F598 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21860 (s : N.State) (i : N.Inputs) :
  R.v21860 (state s) (inputs i) = Zmod.unsigned (N.v21860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21860 s i)) at 1.
  unfold R.v21860, N.v21860.
  rewrite ?node_21858.
  rewrite ?node_21859.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21861 (s : N.State) (i : N.Inputs) :
  R.v21861 (state s) (inputs i) = Zmod.unsigned (N.v21861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21861 s i)) at 1.
  unfold R.v21861, N.v21861.
  unfold R.v16484, N.v16484.
  rewrite ?node_21860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21862 (s : N.State) (i : N.Inputs) :
  R.v21862 (state s) (inputs i) = Zmod.unsigned (N.v21862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21862 s i)) at 1.
  unfold R.v21862, N.v21862.
  rewrite ?node_21857.
  rewrite ?node_21861.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21863 (s : N.State) (i : N.Inputs) :
  R.v21863 (state s) (inputs i) = Zmod.unsigned (N.v21863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21863 s i)) at 1.
  unfold R.v21863, N.v21863.
  unfold R.v6, N.v6.
  rewrite ?node_21862.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21864 (s : N.State) (i : N.Inputs) :
  R.v21864 (state s) (inputs i) = Zmod.unsigned (N.v21864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21864 s i)) at 1.
  unfold R.v21864, N.v21864.
  rewrite ?node_7818.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21865 (s : N.State) (i : N.Inputs) :
  R.v21865 (state s) (inputs i) = Zmod.unsigned (N.v21865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21865 s i)) at 1.
  unfold R.v21865, N.v21865.
  unfold R.v6, N.v6.
  rewrite ?node_7939.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21866 (s : N.State) (i : N.Inputs) :
  R.v21866 (state s) (inputs i) = Zmod.unsigned (N.v21866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21866 s i)) at 1.
  unfold R.v21866, N.v21866.
  rewrite ?node_21864.
  rewrite ?node_21865.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21867 (s : N.State) (i : N.Inputs) :
  R.v21867 (state s) (inputs i) = Zmod.unsigned (N.v21867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21867 s i)) at 1.
  unfold R.v21867, N.v21867.
  rewrite ?node_21863.
  rewrite ?node_21866.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21868 (s : N.State) (i : N.Inputs) :
  R.v21868 (state s) (inputs i) = Zmod.unsigned (N.v21868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21868 s i)) at 1.
  unfold R.v21868, N.v21868.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21869 (s : N.State) (i : N.Inputs) :
  R.v21869 (state s) (inputs i) = Zmod.unsigned (N.v21869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21869 s i)) at 1.
  unfold R.v21869, N.v21869.
  rewrite ?node_7822.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21870 (s : N.State) (i : N.Inputs) :
  R.v21870 (state s) (inputs i) = Zmod.unsigned (N.v21870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21870 s i)) at 1.
  unfold R.v21870, N.v21870.
  unfold R.v6, N.v6.
  rewrite !state_r601_nr_5F601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r601_nr_5F601 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21871 (s : N.State) (i : N.Inputs) :
  R.v21871 (state s) (inputs i) = Zmod.unsigned (N.v21871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21871 s i)) at 1.
  unfold R.v21871, N.v21871.
  unfold R.v6, N.v6.
  rewrite ?node_7818.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21872 (s : N.State) (i : N.Inputs) :
  R.v21872 (state s) (inputs i) = Zmod.unsigned (N.v21872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21872 s i)) at 1.
  unfold R.v21872, N.v21872.
  rewrite ?node_21870.
  rewrite ?node_21871.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21873 (s : N.State) (i : N.Inputs) :
  R.v21873 (state s) (inputs i) = Zmod.unsigned (N.v21873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21873 s i)) at 1.
  unfold R.v21873, N.v21873.
  unfold R.v16484, N.v16484.
  rewrite ?node_21872.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21874 (s : N.State) (i : N.Inputs) :
  R.v21874 (state s) (inputs i) = Zmod.unsigned (N.v21874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21874 s i)) at 1.
  unfold R.v21874, N.v21874.
  rewrite ?node_21869.
  rewrite ?node_21873.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21875 (s : N.State) (i : N.Inputs) :
  R.v21875 (state s) (inputs i) = Zmod.unsigned (N.v21875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21875 s i)) at 1.
  unfold R.v21875, N.v21875.
  unfold R.v6, N.v6.
  rewrite ?node_21874.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21876 (s : N.State) (i : N.Inputs) :
  R.v21876 (state s) (inputs i) = Zmod.unsigned (N.v21876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21876 s i)) at 1.
  unfold R.v21876, N.v21876.
  rewrite ?node_7823.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21877 (s : N.State) (i : N.Inputs) :
  R.v21877 (state s) (inputs i) = Zmod.unsigned (N.v21877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21877 s i)) at 1.
  unfold R.v21877, N.v21877.
  unfold R.v6, N.v6.
  rewrite ?node_7987.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21878 (s : N.State) (i : N.Inputs) :
  R.v21878 (state s) (inputs i) = Zmod.unsigned (N.v21878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21878 s i)) at 1.
  unfold R.v21878, N.v21878.
  rewrite ?node_21876.
  rewrite ?node_21877.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21879 (s : N.State) (i : N.Inputs) :
  R.v21879 (state s) (inputs i) = Zmod.unsigned (N.v21879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21879 s i)) at 1.
  unfold R.v21879, N.v21879.
  rewrite ?node_21875.
  rewrite ?node_21878.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21880 (s : N.State) (i : N.Inputs) :
  R.v21880 (state s) (inputs i) = Zmod.unsigned (N.v21880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21880 s i)) at 1.
  unfold R.v21880, N.v21880.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21881 (s : N.State) (i : N.Inputs) :
  R.v21881 (state s) (inputs i) = Zmod.unsigned (N.v21881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21881 s i)) at 1.
  unfold R.v21881, N.v21881.
  rewrite ?node_7829.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21882 (s : N.State) (i : N.Inputs) :
  R.v21882 (state s) (inputs i) = Zmod.unsigned (N.v21882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21882 s i)) at 1.
  unfold R.v21882, N.v21882.
  unfold R.v16463, N.v16463.
  rewrite !state_r605_nr_5F605.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r605_nr_5F605 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21883 (s : N.State) (i : N.Inputs) :
  R.v21883 (state s) (inputs i) = Zmod.unsigned (N.v21883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21883 s i)) at 1.
  unfold R.v21883, N.v21883.
  unfold R.v16463, N.v16463.
  rewrite !state_r604_nr_5F604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r604_nr_5F604 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21884 (s : N.State) (i : N.Inputs) :
  R.v21884 (state s) (inputs i) = Zmod.unsigned (N.v21884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21884 s i)) at 1.
  unfold R.v21884, N.v21884.
  unfold R.v6, N.v6.
  rewrite !state_r603_nr_5F603.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r603_nr_5F603 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21885 (s : N.State) (i : N.Inputs) :
  R.v21885 (state s) (inputs i) = Zmod.unsigned (N.v21885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21885 s i)) at 1.
  unfold R.v21885, N.v21885.
  unfold R.v6, N.v6.
  rewrite !state_r602_nr_5F602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r602_nr_5F602 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21886 (s : N.State) (i : N.Inputs) :
  R.v21886 (state s) (inputs i) = Zmod.unsigned (N.v21886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21886 s i)) at 1.
  unfold R.v21886, N.v21886.
  rewrite ?node_21884.
  rewrite ?node_21885.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21887 (s : N.State) (i : N.Inputs) :
  R.v21887 (state s) (inputs i) = Zmod.unsigned (N.v21887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21887 s i)) at 1.
  unfold R.v21887, N.v21887.
  unfold R.v16484, N.v16484.
  rewrite ?node_21886.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21888 (s : N.State) (i : N.Inputs) :
  R.v21888 (state s) (inputs i) = Zmod.unsigned (N.v21888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21888 s i)) at 1.
  unfold R.v21888, N.v21888.
  rewrite ?node_21881.
  rewrite ?node_21882.
  rewrite ?node_21883.
  rewrite ?node_21887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21889 (s : N.State) (i : N.Inputs) :
  R.v21889 (state s) (inputs i) = Zmod.unsigned (N.v21889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21889 s i)) at 1.
  unfold R.v21889, N.v21889.
  unfold R.v6, N.v6.
  rewrite ?node_21888.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21890 (s : N.State) (i : N.Inputs) :
  R.v21890 (state s) (inputs i) = Zmod.unsigned (N.v21890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21890 s i)) at 1.
  unfold R.v21890, N.v21890.
  rewrite ?node_7830.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21891 (s : N.State) (i : N.Inputs) :
  R.v21891 (state s) (inputs i) = Zmod.unsigned (N.v21891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21891 s i)) at 1.
  unfold R.v21891, N.v21891.
  unfold R.v6, N.v6.
  rewrite ?node_7946.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21892 (s : N.State) (i : N.Inputs) :
  R.v21892 (state s) (inputs i) = Zmod.unsigned (N.v21892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21892 s i)) at 1.
  unfold R.v21892, N.v21892.
  unfold R.v6, N.v6.
  rewrite ?node_7996.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21893 (s : N.State) (i : N.Inputs) :
  R.v21893 (state s) (inputs i) = Zmod.unsigned (N.v21893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21893 s i)) at 1.
  unfold R.v21893, N.v21893.
  rewrite ?node_21890.
  rewrite ?node_21891.
  rewrite ?node_21892.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21894 (s : N.State) (i : N.Inputs) :
  R.v21894 (state s) (inputs i) = Zmod.unsigned (N.v21894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21894 s i)) at 1.
  unfold R.v21894, N.v21894.
  rewrite ?node_21889.
  rewrite ?node_21893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21895 (s : N.State) (i : N.Inputs) :
  R.v21895 (state s) (inputs i) = Zmod.unsigned (N.v21895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21895 s i)) at 1.
  unfold R.v21895, N.v21895.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21896 (s : N.State) (i : N.Inputs) :
  R.v21896 (state s) (inputs i) = Zmod.unsigned (N.v21896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21896 s i)) at 1.
  unfold R.v21896, N.v21896.
  unfold R.v16463, N.v16463.
  rewrite !state_r604_nr_5F604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r604_nr_5F604 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21897 (s : N.State) (i : N.Inputs) :
  R.v21897 (state s) (inputs i) = Zmod.unsigned (N.v21897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21897 s i)) at 1.
  unfold R.v21897, N.v21897.
  unfold R.v6, N.v6.
  rewrite !state_r603_nr_5F603.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r603_nr_5F603 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21898 (s : N.State) (i : N.Inputs) :
  R.v21898 (state s) (inputs i) = Zmod.unsigned (N.v21898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21898 s i)) at 1.
  unfold R.v21898, N.v21898.
  unfold R.v6, N.v6.
  rewrite !state_r602_nr_5F602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r602_nr_5F602 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21899 (s : N.State) (i : N.Inputs) :
  R.v21899 (state s) (inputs i) = Zmod.unsigned (N.v21899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21899 s i)) at 1.
  unfold R.v21899, N.v21899.
  rewrite ?node_21897.
  rewrite ?node_21898.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21900 (s : N.State) (i : N.Inputs) :
  R.v21900 (state s) (inputs i) = Zmod.unsigned (N.v21900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21900 s i)) at 1.
  unfold R.v21900, N.v21900.
  unfold R.v16484, N.v16484.
  rewrite ?node_21899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21901 (s : N.State) (i : N.Inputs) :
  R.v21901 (state s) (inputs i) = Zmod.unsigned (N.v21901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21901 s i)) at 1.
  unfold R.v21901, N.v21901.
  rewrite ?node_21896.
  rewrite ?node_21900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21902 (s : N.State) (i : N.Inputs) :
  R.v21902 (state s) (inputs i) = Zmod.unsigned (N.v21902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21902 s i)) at 1.
  unfold R.v21902, N.v21902.
  unfold R.v6, N.v6.
  rewrite ?node_21901.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21903 (s : N.State) (i : N.Inputs) :
  R.v21903 (state s) (inputs i) = Zmod.unsigned (N.v21903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21903 s i)) at 1.
  unfold R.v21903, N.v21903.
  rewrite ?node_7825.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21904 (s : N.State) (i : N.Inputs) :
  R.v21904 (state s) (inputs i) = Zmod.unsigned (N.v21904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21904 s i)) at 1.
  unfold R.v21904, N.v21904.
  unfold R.v6, N.v6.
  rewrite ?node_7946.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21905 (s : N.State) (i : N.Inputs) :
  R.v21905 (state s) (inputs i) = Zmod.unsigned (N.v21905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21905 s i)) at 1.
  unfold R.v21905, N.v21905.
  rewrite ?node_21903.
  rewrite ?node_21904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21906 (s : N.State) (i : N.Inputs) :
  R.v21906 (state s) (inputs i) = Zmod.unsigned (N.v21906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21906 s i)) at 1.
  unfold R.v21906, N.v21906.
  rewrite ?node_21902.
  rewrite ?node_21905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21907 (s : N.State) (i : N.Inputs) :
  R.v21907 (state s) (inputs i) = Zmod.unsigned (N.v21907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21907 s i)) at 1.
  unfold R.v21907, N.v21907.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21908 (s : N.State) (i : N.Inputs) :
  R.v21908 (state s) (inputs i) = Zmod.unsigned (N.v21908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21908 s i)) at 1.
  unfold R.v21908, N.v21908.
  rewrite ?node_7829.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21909 (s : N.State) (i : N.Inputs) :
  R.v21909 (state s) (inputs i) = Zmod.unsigned (N.v21909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21909 s i)) at 1.
  unfold R.v21909, N.v21909.
  unfold R.v6, N.v6.
  rewrite !state_r605_nr_5F605.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r605_nr_5F605 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21910 (s : N.State) (i : N.Inputs) :
  R.v21910 (state s) (inputs i) = Zmod.unsigned (N.v21910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21910 s i)) at 1.
  unfold R.v21910, N.v21910.
  unfold R.v6, N.v6.
  rewrite ?node_7825.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21911 (s : N.State) (i : N.Inputs) :
  R.v21911 (state s) (inputs i) = Zmod.unsigned (N.v21911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21911 s i)) at 1.
  unfold R.v21911, N.v21911.
  rewrite ?node_21909.
  rewrite ?node_21910.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21912 (s : N.State) (i : N.Inputs) :
  R.v21912 (state s) (inputs i) = Zmod.unsigned (N.v21912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21912 s i)) at 1.
  unfold R.v21912, N.v21912.
  unfold R.v16484, N.v16484.
  rewrite ?node_21911.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21913 (s : N.State) (i : N.Inputs) :
  R.v21913 (state s) (inputs i) = Zmod.unsigned (N.v21913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21913 s i)) at 1.
  unfold R.v21913, N.v21913.
  rewrite ?node_21908.
  rewrite ?node_21912.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21914 (s : N.State) (i : N.Inputs) :
  R.v21914 (state s) (inputs i) = Zmod.unsigned (N.v21914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21914 s i)) at 1.
  unfold R.v21914, N.v21914.
  unfold R.v6, N.v6.
  rewrite ?node_21913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21915 (s : N.State) (i : N.Inputs) :
  R.v21915 (state s) (inputs i) = Zmod.unsigned (N.v21915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21915 s i)) at 1.
  unfold R.v21915, N.v21915.
  rewrite ?node_7830.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21916 (s : N.State) (i : N.Inputs) :
  R.v21916 (state s) (inputs i) = Zmod.unsigned (N.v21916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21916 s i)) at 1.
  unfold R.v21916, N.v21916.
  unfold R.v6, N.v6.
  rewrite ?node_7996.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21917 (s : N.State) (i : N.Inputs) :
  R.v21917 (state s) (inputs i) = Zmod.unsigned (N.v21917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21917 s i)) at 1.
  unfold R.v21917, N.v21917.
  rewrite ?node_21915.
  rewrite ?node_21916.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21918 (s : N.State) (i : N.Inputs) :
  R.v21918 (state s) (inputs i) = Zmod.unsigned (N.v21918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21918 s i)) at 1.
  unfold R.v21918, N.v21918.
  rewrite ?node_21914.
  rewrite ?node_21917.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21919 (s : N.State) (i : N.Inputs) :
  R.v21919 (state s) (inputs i) = Zmod.unsigned (N.v21919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21919 s i)) at 1.
  unfold R.v21919, N.v21919.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21920 (s : N.State) (i : N.Inputs) :
  R.v21920 (state s) (inputs i) = Zmod.unsigned (N.v21920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21920 s i)) at 1.
  unfold R.v21920, N.v21920.
  rewrite ?node_7837.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21921 (s : N.State) (i : N.Inputs) :
  R.v21921 (state s) (inputs i) = Zmod.unsigned (N.v21921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21921 s i)) at 1.
  unfold R.v21921, N.v21921.
  unfold R.v16463, N.v16463.
  rewrite !state_r609_nr_5F609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r609_nr_5F609 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21922 (s : N.State) (i : N.Inputs) :
  R.v21922 (state s) (inputs i) = Zmod.unsigned (N.v21922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21922 s i)) at 1.
  unfold R.v21922, N.v21922.
  unfold R.v16463, N.v16463.
  rewrite !state_r608_nr_5F608.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r608_nr_5F608 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21923 (s : N.State) (i : N.Inputs) :
  R.v21923 (state s) (inputs i) = Zmod.unsigned (N.v21923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21923 s i)) at 1.
  unfold R.v21923, N.v21923.
  unfold R.v6, N.v6.
  rewrite !state_r607_nr_5F607.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r607_nr_5F607 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21924 (s : N.State) (i : N.Inputs) :
  R.v21924 (state s) (inputs i) = Zmod.unsigned (N.v21924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21924 s i)) at 1.
  unfold R.v21924, N.v21924.
  unfold R.v6, N.v6.
  rewrite !state_r606_nr_5F606.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r606_nr_5F606 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21925 (s : N.State) (i : N.Inputs) :
  R.v21925 (state s) (inputs i) = Zmod.unsigned (N.v21925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21925 s i)) at 1.
  unfold R.v21925, N.v21925.
  rewrite ?node_21923.
  rewrite ?node_21924.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21926 (s : N.State) (i : N.Inputs) :
  R.v21926 (state s) (inputs i) = Zmod.unsigned (N.v21926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21926 s i)) at 1.
  unfold R.v21926, N.v21926.
  unfold R.v16484, N.v16484.
  rewrite ?node_21925.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21927 (s : N.State) (i : N.Inputs) :
  R.v21927 (state s) (inputs i) = Zmod.unsigned (N.v21927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21927 s i)) at 1.
  unfold R.v21927, N.v21927.
  rewrite ?node_21920.
  rewrite ?node_21921.
  rewrite ?node_21922.
  rewrite ?node_21926.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21928 (s : N.State) (i : N.Inputs) :
  R.v21928 (state s) (inputs i) = Zmod.unsigned (N.v21928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21928 s i)) at 1.
  unfold R.v21928, N.v21928.
  unfold R.v6, N.v6.
  rewrite ?node_21927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21929 (s : N.State) (i : N.Inputs) :
  R.v21929 (state s) (inputs i) = Zmod.unsigned (N.v21929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21929 s i)) at 1.
  unfold R.v21929, N.v21929.
  rewrite ?node_7838.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21930 (s : N.State) (i : N.Inputs) :
  R.v21930 (state s) (inputs i) = Zmod.unsigned (N.v21930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21930 s i)) at 1.
  unfold R.v21930, N.v21930.
  unfold R.v6, N.v6.
  rewrite ?node_7954.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21931 (s : N.State) (i : N.Inputs) :
  R.v21931 (state s) (inputs i) = Zmod.unsigned (N.v21931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21931 s i)) at 1.
  unfold R.v21931, N.v21931.
  unfold R.v6, N.v6.
  rewrite ?node_7999.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21932 (s : N.State) (i : N.Inputs) :
  R.v21932 (state s) (inputs i) = Zmod.unsigned (N.v21932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21932 s i)) at 1.
  unfold R.v21932, N.v21932.
  rewrite ?node_21929.
  rewrite ?node_21930.
  rewrite ?node_21931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21933 (s : N.State) (i : N.Inputs) :
  R.v21933 (state s) (inputs i) = Zmod.unsigned (N.v21933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21933 s i)) at 1.
  unfold R.v21933, N.v21933.
  rewrite ?node_21928.
  rewrite ?node_21932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21934 (s : N.State) (i : N.Inputs) :
  R.v21934 (state s) (inputs i) = Zmod.unsigned (N.v21934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21934 s i)) at 1.
  unfold R.v21934, N.v21934.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21935 (s : N.State) (i : N.Inputs) :
  R.v21935 (state s) (inputs i) = Zmod.unsigned (N.v21935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21935 s i)) at 1.
  unfold R.v21935, N.v21935.
  unfold R.v16463, N.v16463.
  rewrite !state_r608_nr_5F608.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r608_nr_5F608 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21936 (s : N.State) (i : N.Inputs) :
  R.v21936 (state s) (inputs i) = Zmod.unsigned (N.v21936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21936 s i)) at 1.
  unfold R.v21936, N.v21936.
  unfold R.v6, N.v6.
  rewrite !state_r607_nr_5F607.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r607_nr_5F607 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21937 (s : N.State) (i : N.Inputs) :
  R.v21937 (state s) (inputs i) = Zmod.unsigned (N.v21937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21937 s i)) at 1.
  unfold R.v21937, N.v21937.
  unfold R.v6, N.v6.
  rewrite !state_r606_nr_5F606.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r606_nr_5F606 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21938 (s : N.State) (i : N.Inputs) :
  R.v21938 (state s) (inputs i) = Zmod.unsigned (N.v21938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21938 s i)) at 1.
  unfold R.v21938, N.v21938.
  rewrite ?node_21936.
  rewrite ?node_21937.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21939 (s : N.State) (i : N.Inputs) :
  R.v21939 (state s) (inputs i) = Zmod.unsigned (N.v21939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21939 s i)) at 1.
  unfold R.v21939, N.v21939.
  unfold R.v16484, N.v16484.
  rewrite ?node_21938.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21940 (s : N.State) (i : N.Inputs) :
  R.v21940 (state s) (inputs i) = Zmod.unsigned (N.v21940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21940 s i)) at 1.
  unfold R.v21940, N.v21940.
  rewrite ?node_21935.
  rewrite ?node_21939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21941 (s : N.State) (i : N.Inputs) :
  R.v21941 (state s) (inputs i) = Zmod.unsigned (N.v21941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21941 s i)) at 1.
  unfold R.v21941, N.v21941.
  unfold R.v6, N.v6.
  rewrite ?node_21940.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21942 (s : N.State) (i : N.Inputs) :
  R.v21942 (state s) (inputs i) = Zmod.unsigned (N.v21942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21942 s i)) at 1.
  unfold R.v21942, N.v21942.
  rewrite ?node_7833.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21943 (s : N.State) (i : N.Inputs) :
  R.v21943 (state s) (inputs i) = Zmod.unsigned (N.v21943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21943 s i)) at 1.
  unfold R.v21943, N.v21943.
  unfold R.v6, N.v6.
  rewrite ?node_7954.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21944 (s : N.State) (i : N.Inputs) :
  R.v21944 (state s) (inputs i) = Zmod.unsigned (N.v21944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21944 s i)) at 1.
  unfold R.v21944, N.v21944.
  rewrite ?node_21942.
  rewrite ?node_21943.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21945 (s : N.State) (i : N.Inputs) :
  R.v21945 (state s) (inputs i) = Zmod.unsigned (N.v21945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21945 s i)) at 1.
  unfold R.v21945, N.v21945.
  rewrite ?node_21941.
  rewrite ?node_21944.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21946 (s : N.State) (i : N.Inputs) :
  R.v21946 (state s) (inputs i) = Zmod.unsigned (N.v21946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21946 s i)) at 1.
  unfold R.v21946, N.v21946.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21947 (s : N.State) (i : N.Inputs) :
  R.v21947 (state s) (inputs i) = Zmod.unsigned (N.v21947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21947 s i)) at 1.
  unfold R.v21947, N.v21947.
  rewrite ?node_7837.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21948 (s : N.State) (i : N.Inputs) :
  R.v21948 (state s) (inputs i) = Zmod.unsigned (N.v21948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21948 s i)) at 1.
  unfold R.v21948, N.v21948.
  unfold R.v6, N.v6.
  rewrite !state_r609_nr_5F609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r609_nr_5F609 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21949 (s : N.State) (i : N.Inputs) :
  R.v21949 (state s) (inputs i) = Zmod.unsigned (N.v21949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21949 s i)) at 1.
  unfold R.v21949, N.v21949.
  unfold R.v6, N.v6.
  rewrite ?node_7833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21950 (s : N.State) (i : N.Inputs) :
  R.v21950 (state s) (inputs i) = Zmod.unsigned (N.v21950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21950 s i)) at 1.
  unfold R.v21950, N.v21950.
  rewrite ?node_21948.
  rewrite ?node_21949.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21951 (s : N.State) (i : N.Inputs) :
  R.v21951 (state s) (inputs i) = Zmod.unsigned (N.v21951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21951 s i)) at 1.
  unfold R.v21951, N.v21951.
  unfold R.v16484, N.v16484.
  rewrite ?node_21950.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21952 (s : N.State) (i : N.Inputs) :
  R.v21952 (state s) (inputs i) = Zmod.unsigned (N.v21952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21952 s i)) at 1.
  unfold R.v21952, N.v21952.
  rewrite ?node_21947.
  rewrite ?node_21951.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21953 (s : N.State) (i : N.Inputs) :
  R.v21953 (state s) (inputs i) = Zmod.unsigned (N.v21953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21953 s i)) at 1.
  unfold R.v21953, N.v21953.
  unfold R.v6, N.v6.
  rewrite ?node_21952.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21954 (s : N.State) (i : N.Inputs) :
  R.v21954 (state s) (inputs i) = Zmod.unsigned (N.v21954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21954 s i)) at 1.
  unfold R.v21954, N.v21954.
  rewrite ?node_7838.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21955 (s : N.State) (i : N.Inputs) :
  R.v21955 (state s) (inputs i) = Zmod.unsigned (N.v21955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21955 s i)) at 1.
  unfold R.v21955, N.v21955.
  unfold R.v6, N.v6.
  rewrite ?node_7999.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21956 (s : N.State) (i : N.Inputs) :
  R.v21956 (state s) (inputs i) = Zmod.unsigned (N.v21956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21956 s i)) at 1.
  unfold R.v21956, N.v21956.
  rewrite ?node_21954.
  rewrite ?node_21955.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21957 (s : N.State) (i : N.Inputs) :
  R.v21957 (state s) (inputs i) = Zmod.unsigned (N.v21957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21957 s i)) at 1.
  unfold R.v21957, N.v21957.
  rewrite ?node_21953.
  rewrite ?node_21956.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21958 (s : N.State) (i : N.Inputs) :
  R.v21958 (state s) (inputs i) = Zmod.unsigned (N.v21958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21958 s i)) at 1.
  unfold R.v21958, N.v21958.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21959 (s : N.State) (i : N.Inputs) :
  R.v21959 (state s) (inputs i) = Zmod.unsigned (N.v21959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21959 s i)) at 1.
  unfold R.v21959, N.v21959.
  rewrite ?node_7845.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21960 (s : N.State) (i : N.Inputs) :
  R.v21960 (state s) (inputs i) = Zmod.unsigned (N.v21960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21960 s i)) at 1.
  unfold R.v21960, N.v21960.
  unfold R.v16463, N.v16463.
  rewrite !state_r613_nr_5F613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r613_nr_5F613 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21961 (s : N.State) (i : N.Inputs) :
  R.v21961 (state s) (inputs i) = Zmod.unsigned (N.v21961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21961 s i)) at 1.
  unfold R.v21961, N.v21961.
  unfold R.v16463, N.v16463.
  rewrite !state_r612_nr_5F612.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r612_nr_5F612 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21962 (s : N.State) (i : N.Inputs) :
  R.v21962 (state s) (inputs i) = Zmod.unsigned (N.v21962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21962 s i)) at 1.
  unfold R.v21962, N.v21962.
  unfold R.v6, N.v6.
  rewrite !state_r611_nr_5F611.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r611_nr_5F611 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21963 (s : N.State) (i : N.Inputs) :
  R.v21963 (state s) (inputs i) = Zmod.unsigned (N.v21963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21963 s i)) at 1.
  unfold R.v21963, N.v21963.
  unfold R.v6, N.v6.
  rewrite !state_r610_nr_5F610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r610_nr_5F610 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21964 (s : N.State) (i : N.Inputs) :
  R.v21964 (state s) (inputs i) = Zmod.unsigned (N.v21964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21964 s i)) at 1.
  unfold R.v21964, N.v21964.
  rewrite ?node_21962.
  rewrite ?node_21963.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21965 (s : N.State) (i : N.Inputs) :
  R.v21965 (state s) (inputs i) = Zmod.unsigned (N.v21965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21965 s i)) at 1.
  unfold R.v21965, N.v21965.
  unfold R.v16484, N.v16484.
  rewrite ?node_21964.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21966 (s : N.State) (i : N.Inputs) :
  R.v21966 (state s) (inputs i) = Zmod.unsigned (N.v21966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21966 s i)) at 1.
  unfold R.v21966, N.v21966.
  rewrite ?node_21959.
  rewrite ?node_21960.
  rewrite ?node_21961.
  rewrite ?node_21965.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21967 (s : N.State) (i : N.Inputs) :
  R.v21967 (state s) (inputs i) = Zmod.unsigned (N.v21967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21967 s i)) at 1.
  unfold R.v21967, N.v21967.
  unfold R.v6, N.v6.
  rewrite ?node_21966.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21968 (s : N.State) (i : N.Inputs) :
  R.v21968 (state s) (inputs i) = Zmod.unsigned (N.v21968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21968 s i)) at 1.
  unfold R.v21968, N.v21968.
  rewrite ?node_7846.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21969 (s : N.State) (i : N.Inputs) :
  R.v21969 (state s) (inputs i) = Zmod.unsigned (N.v21969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21969 s i)) at 1.
  unfold R.v21969, N.v21969.
  unfold R.v6, N.v6.
  rewrite ?node_7962.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21970 (s : N.State) (i : N.Inputs) :
  R.v21970 (state s) (inputs i) = Zmod.unsigned (N.v21970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21970 s i)) at 1.
  unfold R.v21970, N.v21970.
  unfold R.v6, N.v6.
  rewrite ?node_8003.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21971 (s : N.State) (i : N.Inputs) :
  R.v21971 (state s) (inputs i) = Zmod.unsigned (N.v21971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21971 s i)) at 1.
  unfold R.v21971, N.v21971.
  rewrite ?node_21968.
  rewrite ?node_21969.
  rewrite ?node_21970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21972 (s : N.State) (i : N.Inputs) :
  R.v21972 (state s) (inputs i) = Zmod.unsigned (N.v21972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21972 s i)) at 1.
  unfold R.v21972, N.v21972.
  rewrite ?node_21967.
  rewrite ?node_21971.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21973 (s : N.State) (i : N.Inputs) :
  R.v21973 (state s) (inputs i) = Zmod.unsigned (N.v21973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21973 s i)) at 1.
  unfold R.v21973, N.v21973.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21974 (s : N.State) (i : N.Inputs) :
  R.v21974 (state s) (inputs i) = Zmod.unsigned (N.v21974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21974 s i)) at 1.
  unfold R.v21974, N.v21974.
  unfold R.v16463, N.v16463.
  rewrite !state_r612_nr_5F612.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r612_nr_5F612 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21975 (s : N.State) (i : N.Inputs) :
  R.v21975 (state s) (inputs i) = Zmod.unsigned (N.v21975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21975 s i)) at 1.
  unfold R.v21975, N.v21975.
  unfold R.v6, N.v6.
  rewrite !state_r611_nr_5F611.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r611_nr_5F611 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21976 (s : N.State) (i : N.Inputs) :
  R.v21976 (state s) (inputs i) = Zmod.unsigned (N.v21976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21976 s i)) at 1.
  unfold R.v21976, N.v21976.
  unfold R.v6, N.v6.
  rewrite !state_r610_nr_5F610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r610_nr_5F610 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21977 (s : N.State) (i : N.Inputs) :
  R.v21977 (state s) (inputs i) = Zmod.unsigned (N.v21977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21977 s i)) at 1.
  unfold R.v21977, N.v21977.
  rewrite ?node_21975.
  rewrite ?node_21976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21978 (s : N.State) (i : N.Inputs) :
  R.v21978 (state s) (inputs i) = Zmod.unsigned (N.v21978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21978 s i)) at 1.
  unfold R.v21978, N.v21978.
  unfold R.v16484, N.v16484.
  rewrite ?node_21977.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21979 (s : N.State) (i : N.Inputs) :
  R.v21979 (state s) (inputs i) = Zmod.unsigned (N.v21979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21979 s i)) at 1.
  unfold R.v21979, N.v21979.
  rewrite ?node_21974.
  rewrite ?node_21978.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21980 (s : N.State) (i : N.Inputs) :
  R.v21980 (state s) (inputs i) = Zmod.unsigned (N.v21980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21980 s i)) at 1.
  unfold R.v21980, N.v21980.
  unfold R.v6, N.v6.
  rewrite ?node_21979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21981 (s : N.State) (i : N.Inputs) :
  R.v21981 (state s) (inputs i) = Zmod.unsigned (N.v21981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21981 s i)) at 1.
  unfold R.v21981, N.v21981.
  rewrite ?node_7841.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21982 (s : N.State) (i : N.Inputs) :
  R.v21982 (state s) (inputs i) = Zmod.unsigned (N.v21982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21982 s i)) at 1.
  unfold R.v21982, N.v21982.
  unfold R.v6, N.v6.
  rewrite ?node_7962.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21983 (s : N.State) (i : N.Inputs) :
  R.v21983 (state s) (inputs i) = Zmod.unsigned (N.v21983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21983 s i)) at 1.
  unfold R.v21983, N.v21983.
  rewrite ?node_21981.
  rewrite ?node_21982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21984 (s : N.State) (i : N.Inputs) :
  R.v21984 (state s) (inputs i) = Zmod.unsigned (N.v21984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21984 s i)) at 1.
  unfold R.v21984, N.v21984.
  rewrite ?node_21980.
  rewrite ?node_21983.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21985 (s : N.State) (i : N.Inputs) :
  R.v21985 (state s) (inputs i) = Zmod.unsigned (N.v21985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21985 s i)) at 1.
  unfold R.v21985, N.v21985.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21986 (s : N.State) (i : N.Inputs) :
  R.v21986 (state s) (inputs i) = Zmod.unsigned (N.v21986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21986 s i)) at 1.
  unfold R.v21986, N.v21986.
  rewrite ?node_7845.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21987 (s : N.State) (i : N.Inputs) :
  R.v21987 (state s) (inputs i) = Zmod.unsigned (N.v21987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21987 s i)) at 1.
  unfold R.v21987, N.v21987.
  unfold R.v6, N.v6.
  rewrite !state_r613_nr_5F613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r613_nr_5F613 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21988 (s : N.State) (i : N.Inputs) :
  R.v21988 (state s) (inputs i) = Zmod.unsigned (N.v21988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21988 s i)) at 1.
  unfold R.v21988, N.v21988.
  unfold R.v6, N.v6.
  rewrite ?node_7841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21989 (s : N.State) (i : N.Inputs) :
  R.v21989 (state s) (inputs i) = Zmod.unsigned (N.v21989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21989 s i)) at 1.
  unfold R.v21989, N.v21989.
  rewrite ?node_21987.
  rewrite ?node_21988.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21990 (s : N.State) (i : N.Inputs) :
  R.v21990 (state s) (inputs i) = Zmod.unsigned (N.v21990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21990 s i)) at 1.
  unfold R.v21990, N.v21990.
  unfold R.v16484, N.v16484.
  rewrite ?node_21989.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21991 (s : N.State) (i : N.Inputs) :
  R.v21991 (state s) (inputs i) = Zmod.unsigned (N.v21991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21991 s i)) at 1.
  unfold R.v21991, N.v21991.
  rewrite ?node_21986.
  rewrite ?node_21990.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21992 (s : N.State) (i : N.Inputs) :
  R.v21992 (state s) (inputs i) = Zmod.unsigned (N.v21992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21992 s i)) at 1.
  unfold R.v21992, N.v21992.
  unfold R.v6, N.v6.
  rewrite ?node_21991.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21993 (s : N.State) (i : N.Inputs) :
  R.v21993 (state s) (inputs i) = Zmod.unsigned (N.v21993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21993 s i)) at 1.
  unfold R.v21993, N.v21993.
  rewrite ?node_7846.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21994 (s : N.State) (i : N.Inputs) :
  R.v21994 (state s) (inputs i) = Zmod.unsigned (N.v21994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21994 s i)) at 1.
  unfold R.v21994, N.v21994.
  unfold R.v6, N.v6.
  rewrite ?node_8003.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21995 (s : N.State) (i : N.Inputs) :
  R.v21995 (state s) (inputs i) = Zmod.unsigned (N.v21995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21995 s i)) at 1.
  unfold R.v21995, N.v21995.
  rewrite ?node_21993.
  rewrite ?node_21994.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21996 (s : N.State) (i : N.Inputs) :
  R.v21996 (state s) (inputs i) = Zmod.unsigned (N.v21996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21996 s i)) at 1.
  unfold R.v21996, N.v21996.
  rewrite ?node_21992.
  rewrite ?node_21995.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21997 (s : N.State) (i : N.Inputs) :
  R.v21997 (state s) (inputs i) = Zmod.unsigned (N.v21997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21997 s i)) at 1.
  unfold R.v21997, N.v21997.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21998 (s : N.State) (i : N.Inputs) :
  R.v21998 (state s) (inputs i) = Zmod.unsigned (N.v21998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21998 s i)) at 1.
  unfold R.v21998, N.v21998.
  rewrite ?node_7857.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21999 (s : N.State) (i : N.Inputs) :
  R.v21999 (state s) (inputs i) = Zmod.unsigned (N.v21999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21999 s i)) at 1.
  unfold R.v21999, N.v21999.
  unfold R.v16463, N.v16463.
  rewrite !state_r617_nr_5F617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r617_nr_5F617 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
