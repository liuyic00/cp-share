(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes007.
Lemma node_8000 (s : N.State) (i : N.Inputs) :
  R.v8000 (state s) (inputs i) = Zmod.unsigned (N.v8000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8000 s i)) at 1.
  unfold R.v8000, N.v8000.
  rewrite ?node_7996.
  rewrite ?node_7999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8001 (s : N.State) (i : N.Inputs) :
  R.v8001 (state s) (inputs i) = Zmod.unsigned (N.v8001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8001 s i)) at 1.
  unfold R.v8001, N.v8001.
  rewrite ?node_7841.
  rewrite !state_r613_nr_5F613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r613_nr_5F613 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8002 (s : N.State) (i : N.Inputs) :
  R.v8002 (state s) (inputs i) = Zmod.unsigned (N.v8002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8002 s i)) at 1.
  unfold R.v8002, N.v8002.
  rewrite ?node_7842.
  rewrite ?node_7845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8003 (s : N.State) (i : N.Inputs) :
  R.v8003 (state s) (inputs i) = Zmod.unsigned (N.v8003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8003 s i)) at 1.
  unfold R.v8003, N.v8003.
  rewrite ?node_8001.
  rewrite ?node_8002.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8004 (s : N.State) (i : N.Inputs) :
  R.v8004 (state s) (inputs i) = Zmod.unsigned (N.v8004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8004 s i)) at 1.
  unfold R.v8004, N.v8004.
  rewrite ?node_8000.
  rewrite ?node_8003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8005 (s : N.State) (i : N.Inputs) :
  R.v8005 (state s) (inputs i) = Zmod.unsigned (N.v8005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8005 s i)) at 1.
  unfold R.v8005, N.v8005.
  rewrite ?node_7853.
  rewrite !state_r617_nr_5F617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r617_nr_5F617 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8006 (s : N.State) (i : N.Inputs) :
  R.v8006 (state s) (inputs i) = Zmod.unsigned (N.v8006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8006 s i)) at 1.
  unfold R.v8006, N.v8006.
  rewrite ?node_7854.
  rewrite ?node_7857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8007 (s : N.State) (i : N.Inputs) :
  R.v8007 (state s) (inputs i) = Zmod.unsigned (N.v8007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8007 s i)) at 1.
  unfold R.v8007, N.v8007.
  rewrite ?node_8005.
  rewrite ?node_8006.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8008 (s : N.State) (i : N.Inputs) :
  R.v8008 (state s) (inputs i) = Zmod.unsigned (N.v8008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8008 s i)) at 1.
  unfold R.v8008, N.v8008.
  rewrite ?node_8004.
  rewrite ?node_8007.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8009 (s : N.State) (i : N.Inputs) :
  R.v8009 (state s) (inputs i) = Zmod.unsigned (N.v8009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8009 s i)) at 1.
  unfold R.v8009, N.v8009.
  rewrite ?node_7879.
  rewrite ?node_7882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8010 (s : N.State) (i : N.Inputs) :
  R.v8010 (state s) (inputs i) = Zmod.unsigned (N.v8010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8010 s i)) at 1.
  unfold R.v8010, N.v8010.
  rewrite ?node_7883.
  rewrite ?node_7886.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8011 (s : N.State) (i : N.Inputs) :
  R.v8011 (state s) (inputs i) = Zmod.unsigned (N.v8011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8011 s i)) at 1.
  unfold R.v8011, N.v8011.
  rewrite ?node_8009.
  rewrite ?node_8010.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8012 (s : N.State) (i : N.Inputs) :
  R.v8012 (state s) (inputs i) = Zmod.unsigned (N.v8012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8012 s i)) at 1.
  unfold R.v8012, N.v8012.
  rewrite ?node_8008.
  rewrite ?node_8011.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8013 (s : N.State) (i : N.Inputs) :
  R.v8013 (state s) (inputs i) = Zmod.unsigned (N.v8013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8013 s i)) at 1.
  unfold R.v8013, N.v8013.
  rewrite ?node_7993.
  rewrite ?node_8012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8014 (s : N.State) (i : N.Inputs) :
  R.v8014 (state s) (inputs i) = Zmod.unsigned (N.v8014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8014 s i)) at 1.
  unfold R.v8014, N.v8014.
  rewrite ?node_7860.
  rewrite !state_r621_nr_5F621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r621_nr_5F621 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8015 (s : N.State) (i : N.Inputs) :
  R.v8015 (state s) (inputs i) = Zmod.unsigned (N.v8015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8015 s i)) at 1.
  unfold R.v8015, N.v8015.
  rewrite ?node_7861.
  rewrite ?node_7864.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8016 (s : N.State) (i : N.Inputs) :
  R.v8016 (state s) (inputs i) = Zmod.unsigned (N.v8016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8016 s i)) at 1.
  unfold R.v8016, N.v8016.
  rewrite ?node_8014.
  rewrite ?node_8015.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8017 (s : N.State) (i : N.Inputs) :
  R.v8017 (state s) (inputs i) = Zmod.unsigned (N.v8017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8017 s i)) at 1.
  unfold R.v8017, N.v8017.
  rewrite ?node_8013.
  rewrite ?node_8016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8018 (s : N.State) (i : N.Inputs) :
  R.v8018 (state s) (inputs i) = Zmod.unsigned (N.v8018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8018 s i)) at 1.
  unfold R.v8018, N.v8018.
  rewrite ?node_7851.
  rewrite ?node_7875.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8019 (s : N.State) (i : N.Inputs) :
  R.v8019 (state s) (inputs i) = Zmod.unsigned (N.v8019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8019 s i)) at 1.
  unfold R.v8019, N.v8019.
  rewrite ?node_7876.
  rewrite ?node_7895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8020 (s : N.State) (i : N.Inputs) :
  R.v8020 (state s) (inputs i) = Zmod.unsigned (N.v8020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8020 s i)) at 1.
  unfold R.v8020, N.v8020.
  rewrite ?node_8018.
  rewrite ?node_8019.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8021 (s : N.State) (i : N.Inputs) :
  R.v8021 (state s) (inputs i) = Zmod.unsigned (N.v8021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8021 s i)) at 1.
  unfold R.v8021, N.v8021.
  rewrite ?node_8017.
  rewrite ?node_8020.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8022 (s : N.State) (i : N.Inputs) :
  R.v8022 (state s) (inputs i) = Zmod.unsigned (N.v8022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8022 s i)) at 1.
  unfold R.v8022, N.v8022.
  rewrite ?node_7839.
  rewrite ?node_7846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8023 (s : N.State) (i : N.Inputs) :
  R.v8023 (state s) (inputs i) = Zmod.unsigned (N.v8023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8023 s i)) at 1.
  unfold R.v8023, N.v8023.
  rewrite ?node_7847.
  rewrite ?node_7850.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8024 (s : N.State) (i : N.Inputs) :
  R.v8024 (state s) (inputs i) = Zmod.unsigned (N.v8024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8024 s i)) at 1.
  unfold R.v8024, N.v8024.
  rewrite ?node_8022.
  rewrite ?node_8023.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8025 (s : N.State) (i : N.Inputs) :
  R.v8025 (state s) (inputs i) = Zmod.unsigned (N.v8025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8025 s i)) at 1.
  unfold R.v8025, N.v8025.
  rewrite ?node_7867.
  rewrite ?node_7870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8026 (s : N.State) (i : N.Inputs) :
  R.v8026 (state s) (inputs i) = Zmod.unsigned (N.v8026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8026 s i)) at 1.
  unfold R.v8026, N.v8026.
  rewrite ?node_7871.
  rewrite ?node_7874.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8027 (s : N.State) (i : N.Inputs) :
  R.v8027 (state s) (inputs i) = Zmod.unsigned (N.v8027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8027 s i)) at 1.
  unfold R.v8027, N.v8027.
  rewrite ?node_8025.
  rewrite ?node_8026.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8028 (s : N.State) (i : N.Inputs) :
  R.v8028 (state s) (inputs i) = Zmod.unsigned (N.v8028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8028 s i)) at 1.
  unfold R.v8028, N.v8028.
  rewrite ?node_8024.
  rewrite ?node_8027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8029 (s : N.State) (i : N.Inputs) :
  R.v8029 (state s) (inputs i) = Zmod.unsigned (N.v8029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8029 s i)) at 1.
  unfold R.v8029, N.v8029.
  rewrite ?node_7887.
  rewrite ?node_7890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8030 (s : N.State) (i : N.Inputs) :
  R.v8030 (state s) (inputs i) = Zmod.unsigned (N.v8030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8030 s i)) at 1.
  unfold R.v8030, N.v8030.
  rewrite ?node_7891.
  rewrite ?node_7894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8031 (s : N.State) (i : N.Inputs) :
  R.v8031 (state s) (inputs i) = Zmod.unsigned (N.v8031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8031 s i)) at 1.
  unfold R.v8031, N.v8031.
  rewrite ?node_8029.
  rewrite ?node_8030.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8032 (s : N.State) (i : N.Inputs) :
  R.v8032 (state s) (inputs i) = Zmod.unsigned (N.v8032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8032 s i)) at 1.
  unfold R.v8032, N.v8032.
  rewrite ?node_8028.
  rewrite ?node_8031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8033 (s : N.State) (i : N.Inputs) :
  R.v8033 (state s) (inputs i) = Zmod.unsigned (N.v8033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8033 s i)) at 1.
  unfold R.v8033, N.v8033.
  rewrite ?node_8021.
  rewrite ?node_8032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8034 (s : N.State) (i : N.Inputs) :
  R.v8034 (state s) (inputs i) = Zmod.unsigned (N.v8034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8034 s i)) at 1.
  unfold R.v8034, N.v8034.
  rewrite ?node_7896.
  rewrite ?node_7899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8035 (s : N.State) (i : N.Inputs) :
  R.v8035 (state s) (inputs i) = Zmod.unsigned (N.v8035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8035 s i)) at 1.
  unfold R.v8035, N.v8035.
  rewrite ?node_7900.
  rewrite ?node_7903.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8036 (s : N.State) (i : N.Inputs) :
  R.v8036 (state s) (inputs i) = Zmod.unsigned (N.v8036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8036 s i)) at 1.
  unfold R.v8036, N.v8036.
  rewrite ?node_8034.
  rewrite ?node_8035.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8037 (s : N.State) (i : N.Inputs) :
  R.v8037 (state s) (inputs i) = Zmod.unsigned (N.v8037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8037 s i)) at 1.
  unfold R.v8037, N.v8037.
  rewrite ?node_8033.
  rewrite ?node_8036.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8038 (s : N.State) (i : N.Inputs) :
  R.v8038 (state s) (inputs i) = Zmod.unsigned (N.v8038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8038 s i)) at 1.
  unfold R.v8038, N.v8038.
  rewrite ?node_7907.
  rewrite ?node_7910.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8039 (s : N.State) (i : N.Inputs) :
  R.v8039 (state s) (inputs i) = Zmod.unsigned (N.v8039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8039 s i)) at 1.
  unfold R.v8039, N.v8039.
  rewrite ?node_7911.
  rewrite ?node_7914.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8040 (s : N.State) (i : N.Inputs) :
  R.v8040 (state s) (inputs i) = Zmod.unsigned (N.v8040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8040 s i)) at 1.
  unfold R.v8040, N.v8040.
  rewrite ?node_8038.
  rewrite ?node_8039.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8041 (s : N.State) (i : N.Inputs) :
  R.v8041 (state s) (inputs i) = Zmod.unsigned (N.v8041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8041 s i)) at 1.
  unfold R.v8041, N.v8041.
  rewrite ?node_8037.
  rewrite ?node_8040.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8042 (s : N.State) (i : N.Inputs) :
  R.v8042 (state s) (inputs i) = Zmod.unsigned (N.v8042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8042 s i)) at 1.
  unfold R.v8042, N.v8042.
  rewrite ?node_7904.
  rewrite ?node_7915.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8043 (s : N.State) (i : N.Inputs) :
  R.v8043 (state s) (inputs i) = Zmod.unsigned (N.v8043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8043 s i)) at 1.
  unfold R.v8043, N.v8043.
  rewrite ?node_7916.
  rewrite ?node_7919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8044 (s : N.State) (i : N.Inputs) :
  R.v8044 (state s) (inputs i) = Zmod.unsigned (N.v8044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8044 s i)) at 1.
  unfold R.v8044, N.v8044.
  rewrite ?node_8042.
  rewrite ?node_8043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8045 (s : N.State) (i : N.Inputs) :
  R.v8045 (state s) (inputs i) = Zmod.unsigned (N.v8045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8045 s i)) at 1.
  unfold R.v8045, N.v8045.
  rewrite ?node_8041.
  rewrite ?node_8044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8046 (s : N.State) (i : N.Inputs) :
  R.v8046 (state s) (inputs i) = Zmod.unsigned (N.v8046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8046 s i)) at 1.
  unfold R.v8046, N.v8046.
  rewrite ?node_7920.
  rewrite ?node_7921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8047 (s : N.State) (i : N.Inputs) :
  R.v8047 (state s) (inputs i) = Zmod.unsigned (N.v8047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8047 s i)) at 1.
  unfold R.v8047, N.v8047.
  rewrite ?node_7922.
  rewrite ?node_7925.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8048 (s : N.State) (i : N.Inputs) :
  R.v8048 (state s) (inputs i) = Zmod.unsigned (N.v8048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8048 s i)) at 1.
  unfold R.v8048, N.v8048.
  rewrite ?node_8046.
  rewrite ?node_8047.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8049 (s : N.State) (i : N.Inputs) :
  R.v8049 (state s) (inputs i) = Zmod.unsigned (N.v8049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8049 s i)) at 1.
  unfold R.v8049, N.v8049.
  rewrite ?node_8045.
  rewrite ?node_8048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8050 (s : N.State) (i : N.Inputs) :
  R.v8050 (state s) (inputs i) = Zmod.unsigned (N.v8050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8050 s i)) at 1.
  unfold R.v8050, N.v8050.
  rewrite ?node_8049.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2367_nr_5F2398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2367_nr_5F2398 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8051 (s : N.State) (i : N.Inputs) :
  R.v8051 (state s) (inputs i) = Zmod.unsigned (N.v8051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8051 s i)) at 1.
  unfold R.v8051, N.v8051.
  rewrite ?node_7926.
  rewrite ?node_7929.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8052 (s : N.State) (i : N.Inputs) :
  R.v8052 (state s) (inputs i) = Zmod.unsigned (N.v8052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8052 s i)) at 1.
  unfold R.v8052, N.v8052.
  rewrite ?node_8051.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2368_nr_5F2399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2368_nr_5F2399 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8053 (s : N.State) (i : N.Inputs) :
  R.v8053 (state s) (inputs i) = Zmod.unsigned (N.v8053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8053 s i)) at 1.
  unfold R.v8053, N.v8053.
  rewrite !state_r648_nr_5F648.
  rewrite !state_r649_nr_5F649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r648_nr_5F648 s)).
  rewrite ?(bits.mod_to_Z (N.r649_nr_5F649 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8054 (s : N.State) (i : N.Inputs) :
  R.v8054 (state s) (inputs i) = Zmod.unsigned (N.v8054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8054 s i)) at 1.
  unfold R.v8054, N.v8054.
  rewrite ?node_8053.
  rewrite !state_r650_nr_5F650.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r650_nr_5F650 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8055 (s : N.State) (i : N.Inputs) :
  R.v8055 (state s) (inputs i) = Zmod.unsigned (N.v8055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8055 s i)) at 1.
  unfold R.v8055, N.v8055.
  rewrite ?node_8054.
  rewrite !state_r651_nr_5F651.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r651_nr_5F651 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8056 (s : N.State) (i : N.Inputs) :
  R.v8056 (state s) (inputs i) = Zmod.unsigned (N.v8056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8056 s i)) at 1.
  unfold R.v8056, N.v8056.
  rewrite !state_r623_nr_5F623.
  rewrite !state_r624_nr_5F624.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r623_nr_5F623 s)).
  rewrite ?(bits.mod_to_Z (N.r624_nr_5F624 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8057 (s : N.State) (i : N.Inputs) :
  R.v8057 (state s) (inputs i) = Zmod.unsigned (N.v8057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8057 s i)) at 1.
  unfold R.v8057, N.v8057.
  rewrite ?node_7934.
  rewrite !state_r625_nr_5F625.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r625_nr_5F625 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8058 (s : N.State) (i : N.Inputs) :
  R.v8058 (state s) (inputs i) = Zmod.unsigned (N.v8058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8058 s i)) at 1.
  unfold R.v8058, N.v8058.
  rewrite ?node_8056.
  rewrite ?node_8057.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8059 (s : N.State) (i : N.Inputs) :
  R.v8059 (state s) (inputs i) = Zmod.unsigned (N.v8059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8059 s i)) at 1.
  unfold R.v8059, N.v8059.
  rewrite ?node_8055.
  rewrite ?node_8058.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8060 (s : N.State) (i : N.Inputs) :
  R.v8060 (state s) (inputs i) = Zmod.unsigned (N.v8060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8060 s i)) at 1.
  unfold R.v8060, N.v8060.
  rewrite !state_r652_nr_5F652.
  rewrite !state_r653_nr_5F653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r652_nr_5F652 s)).
  rewrite ?(bits.mod_to_Z (N.r653_nr_5F653 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8061 (s : N.State) (i : N.Inputs) :
  R.v8061 (state s) (inputs i) = Zmod.unsigned (N.v8061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8061 s i)) at 1.
  unfold R.v8061, N.v8061.
  rewrite ?node_8060.
  rewrite !state_r654_nr_5F654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r654_nr_5F654 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8062 (s : N.State) (i : N.Inputs) :
  R.v8062 (state s) (inputs i) = Zmod.unsigned (N.v8062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8062 s i)) at 1.
  unfold R.v8062, N.v8062.
  rewrite ?node_8061.
  rewrite !state_r655_nr_5F655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r655_nr_5F655 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8063 (s : N.State) (i : N.Inputs) :
  R.v8063 (state s) (inputs i) = Zmod.unsigned (N.v8063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8063 s i)) at 1.
  unfold R.v8063, N.v8063.
  rewrite !state_r627_nr_5F627.
  rewrite !state_r628_nr_5F628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r627_nr_5F627 s)).
  rewrite ?(bits.mod_to_Z (N.r628_nr_5F628 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8064 (s : N.State) (i : N.Inputs) :
  R.v8064 (state s) (inputs i) = Zmod.unsigned (N.v8064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8064 s i)) at 1.
  unfold R.v8064, N.v8064.
  rewrite ?node_7941.
  rewrite !state_r629_nr_5F629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r629_nr_5F629 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8065 (s : N.State) (i : N.Inputs) :
  R.v8065 (state s) (inputs i) = Zmod.unsigned (N.v8065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8065 s i)) at 1.
  unfold R.v8065, N.v8065.
  rewrite ?node_8063.
  rewrite ?node_8064.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8066 (s : N.State) (i : N.Inputs) :
  R.v8066 (state s) (inputs i) = Zmod.unsigned (N.v8066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8066 s i)) at 1.
  unfold R.v8066, N.v8066.
  rewrite ?node_8062.
  rewrite ?node_8065.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8067 (s : N.State) (i : N.Inputs) :
  R.v8067 (state s) (inputs i) = Zmod.unsigned (N.v8067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8067 s i)) at 1.
  unfold R.v8067, N.v8067.
  rewrite ?node_8059.
  rewrite ?node_8066.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8068 (s : N.State) (i : N.Inputs) :
  R.v8068 (state s) (inputs i) = Zmod.unsigned (N.v8068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8068 s i)) at 1.
  unfold R.v8068, N.v8068.
  rewrite !state_r656_nr_5F656.
  rewrite !state_r657_nr_5F657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r656_nr_5F656 s)).
  rewrite ?(bits.mod_to_Z (N.r657_nr_5F657 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8069 (s : N.State) (i : N.Inputs) :
  R.v8069 (state s) (inputs i) = Zmod.unsigned (N.v8069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8069 s i)) at 1.
  unfold R.v8069, N.v8069.
  rewrite ?node_8068.
  rewrite !state_r658_nr_5F658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r658_nr_5F658 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8070 (s : N.State) (i : N.Inputs) :
  R.v8070 (state s) (inputs i) = Zmod.unsigned (N.v8070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8070 s i)) at 1.
  unfold R.v8070, N.v8070.
  rewrite ?node_8069.
  rewrite !state_r659_nr_5F659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r659_nr_5F659 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8071 (s : N.State) (i : N.Inputs) :
  R.v8071 (state s) (inputs i) = Zmod.unsigned (N.v8071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8071 s i)) at 1.
  unfold R.v8071, N.v8071.
  rewrite !state_r631_nr_5F631.
  rewrite !state_r632_nr_5F632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r631_nr_5F631 s)).
  rewrite ?(bits.mod_to_Z (N.r632_nr_5F632 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8072 (s : N.State) (i : N.Inputs) :
  R.v8072 (state s) (inputs i) = Zmod.unsigned (N.v8072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8072 s i)) at 1.
  unfold R.v8072, N.v8072.
  rewrite ?node_7949.
  rewrite !state_r633_nr_5F633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r633_nr_5F633 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8073 (s : N.State) (i : N.Inputs) :
  R.v8073 (state s) (inputs i) = Zmod.unsigned (N.v8073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8073 s i)) at 1.
  unfold R.v8073, N.v8073.
  rewrite ?node_8071.
  rewrite ?node_8072.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8074 (s : N.State) (i : N.Inputs) :
  R.v8074 (state s) (inputs i) = Zmod.unsigned (N.v8074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8074 s i)) at 1.
  unfold R.v8074, N.v8074.
  rewrite ?node_8070.
  rewrite ?node_8073.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8075 (s : N.State) (i : N.Inputs) :
  R.v8075 (state s) (inputs i) = Zmod.unsigned (N.v8075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8075 s i)) at 1.
  unfold R.v8075, N.v8075.
  rewrite ?node_8067.
  rewrite ?node_8074.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8076 (s : N.State) (i : N.Inputs) :
  R.v8076 (state s) (inputs i) = Zmod.unsigned (N.v8076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8076 s i)) at 1.
  unfold R.v8076, N.v8076.
  rewrite !state_r660_nr_5F660.
  rewrite !state_r661_nr_5F661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r660_nr_5F660 s)).
  rewrite ?(bits.mod_to_Z (N.r661_nr_5F661 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8077 (s : N.State) (i : N.Inputs) :
  R.v8077 (state s) (inputs i) = Zmod.unsigned (N.v8077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8077 s i)) at 1.
  unfold R.v8077, N.v8077.
  rewrite ?node_8076.
  rewrite !state_r662_nr_5F662.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r662_nr_5F662 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8078 (s : N.State) (i : N.Inputs) :
  R.v8078 (state s) (inputs i) = Zmod.unsigned (N.v8078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8078 s i)) at 1.
  unfold R.v8078, N.v8078.
  rewrite ?node_8077.
  rewrite !state_r663_nr_5F663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r663_nr_5F663 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8079 (s : N.State) (i : N.Inputs) :
  R.v8079 (state s) (inputs i) = Zmod.unsigned (N.v8079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8079 s i)) at 1.
  unfold R.v8079, N.v8079.
  rewrite !state_r635_nr_5F635.
  rewrite !state_r636_nr_5F636.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r635_nr_5F635 s)).
  rewrite ?(bits.mod_to_Z (N.r636_nr_5F636 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8080 (s : N.State) (i : N.Inputs) :
  R.v8080 (state s) (inputs i) = Zmod.unsigned (N.v8080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8080 s i)) at 1.
  unfold R.v8080, N.v8080.
  rewrite ?node_7957.
  rewrite !state_r637_nr_5F637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r637_nr_5F637 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8081 (s : N.State) (i : N.Inputs) :
  R.v8081 (state s) (inputs i) = Zmod.unsigned (N.v8081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8081 s i)) at 1.
  unfold R.v8081, N.v8081.
  rewrite ?node_8079.
  rewrite ?node_8080.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8082 (s : N.State) (i : N.Inputs) :
  R.v8082 (state s) (inputs i) = Zmod.unsigned (N.v8082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8082 s i)) at 1.
  unfold R.v8082, N.v8082.
  rewrite ?node_8078.
  rewrite ?node_8081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8083 (s : N.State) (i : N.Inputs) :
  R.v8083 (state s) (inputs i) = Zmod.unsigned (N.v8083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8083 s i)) at 1.
  unfold R.v8083, N.v8083.
  rewrite ?node_8075.
  rewrite ?node_8082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8084 (s : N.State) (i : N.Inputs) :
  R.v8084 (state s) (inputs i) = Zmod.unsigned (N.v8084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8084 s i)) at 1.
  unfold R.v8084, N.v8084.
  rewrite ?node_7940.
  rewrite ?node_7947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8085 (s : N.State) (i : N.Inputs) :
  R.v8085 (state s) (inputs i) = Zmod.unsigned (N.v8085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8085 s i)) at 1.
  unfold R.v8085, N.v8085.
  rewrite ?node_7948.
  rewrite ?node_7955.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8086 (s : N.State) (i : N.Inputs) :
  R.v8086 (state s) (inputs i) = Zmod.unsigned (N.v8086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8086 s i)) at 1.
  unfold R.v8086, N.v8086.
  rewrite ?node_8084.
  rewrite ?node_8085.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8087 (s : N.State) (i : N.Inputs) :
  R.v8087 (state s) (inputs i) = Zmod.unsigned (N.v8087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8087 s i)) at 1.
  unfold R.v8087, N.v8087.
  rewrite ?node_8083.
  rewrite ?node_8086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8088 (s : N.State) (i : N.Inputs) :
  R.v8088 (state s) (inputs i) = Zmod.unsigned (N.v8088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8088 s i)) at 1.
  unfold R.v8088, N.v8088.
  rewrite !state_r664_nr_5F664.
  rewrite !state_r665_nr_5F665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r664_nr_5F664 s)).
  rewrite ?(bits.mod_to_Z (N.r665_nr_5F665 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8089 (s : N.State) (i : N.Inputs) :
  R.v8089 (state s) (inputs i) = Zmod.unsigned (N.v8089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8089 s i)) at 1.
  unfold R.v8089, N.v8089.
  rewrite ?node_8088.
  rewrite !state_r666_nr_5F666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r666_nr_5F666 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8090 (s : N.State) (i : N.Inputs) :
  R.v8090 (state s) (inputs i) = Zmod.unsigned (N.v8090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8090 s i)) at 1.
  unfold R.v8090, N.v8090.
  rewrite ?node_8089.
  rewrite !state_r667_nr_5F667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r667_nr_5F667 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8091 (s : N.State) (i : N.Inputs) :
  R.v8091 (state s) (inputs i) = Zmod.unsigned (N.v8091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8091 s i)) at 1.
  unfold R.v8091, N.v8091.
  rewrite !state_r639_nr_5F639.
  rewrite !state_r640_nr_5F640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r639_nr_5F639 s)).
  rewrite ?(bits.mod_to_Z (N.r640_nr_5F640 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8092 (s : N.State) (i : N.Inputs) :
  R.v8092 (state s) (inputs i) = Zmod.unsigned (N.v8092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8092 s i)) at 1.
  unfold R.v8092, N.v8092.
  rewrite ?node_7969.
  rewrite !state_r641_nr_5F641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r641_nr_5F641 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8093 (s : N.State) (i : N.Inputs) :
  R.v8093 (state s) (inputs i) = Zmod.unsigned (N.v8093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8093 s i)) at 1.
  unfold R.v8093, N.v8093.
  rewrite ?node_8091.
  rewrite ?node_8092.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8094 (s : N.State) (i : N.Inputs) :
  R.v8094 (state s) (inputs i) = Zmod.unsigned (N.v8094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8094 s i)) at 1.
  unfold R.v8094, N.v8094.
  rewrite ?node_8090.
  rewrite ?node_8093.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8095 (s : N.State) (i : N.Inputs) :
  R.v8095 (state s) (inputs i) = Zmod.unsigned (N.v8095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8095 s i)) at 1.
  unfold R.v8095, N.v8095.
  rewrite !state_r668_nr_5F668.
  rewrite !state_r669_nr_5F669.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r668_nr_5F668 s)).
  rewrite ?(bits.mod_to_Z (N.r669_nr_5F669 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8096 (s : N.State) (i : N.Inputs) :
  R.v8096 (state s) (inputs i) = Zmod.unsigned (N.v8096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8096 s i)) at 1.
  unfold R.v8096, N.v8096.
  rewrite ?node_8095.
  rewrite !state_r670_nr_5F670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r670_nr_5F670 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8097 (s : N.State) (i : N.Inputs) :
  R.v8097 (state s) (inputs i) = Zmod.unsigned (N.v8097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8097 s i)) at 1.
  unfold R.v8097, N.v8097.
  rewrite ?node_8096.
  rewrite !state_r671_nr_5F671.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r671_nr_5F671 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8098 (s : N.State) (i : N.Inputs) :
  R.v8098 (state s) (inputs i) = Zmod.unsigned (N.v8098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8098 s i)) at 1.
  unfold R.v8098, N.v8098.
  rewrite !state_r643_nr_5F643.
  rewrite !state_r644_nr_5F644.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r643_nr_5F643 s)).
  rewrite ?(bits.mod_to_Z (N.r644_nr_5F644 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8099 (s : N.State) (i : N.Inputs) :
  R.v8099 (state s) (inputs i) = Zmod.unsigned (N.v8099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8099 s i)) at 1.
  unfold R.v8099, N.v8099.
  rewrite ?node_7976.
  rewrite !state_r645_nr_5F645.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r645_nr_5F645 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8100 (s : N.State) (i : N.Inputs) :
  R.v8100 (state s) (inputs i) = Zmod.unsigned (N.v8100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8100 s i)) at 1.
  unfold R.v8100, N.v8100.
  rewrite ?node_8098.
  rewrite ?node_8099.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8101 (s : N.State) (i : N.Inputs) :
  R.v8101 (state s) (inputs i) = Zmod.unsigned (N.v8101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8101 s i)) at 1.
  unfold R.v8101, N.v8101.
  rewrite ?node_8097.
  rewrite ?node_8100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8102 (s : N.State) (i : N.Inputs) :
  R.v8102 (state s) (inputs i) = Zmod.unsigned (N.v8102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8102 s i)) at 1.
  unfold R.v8102, N.v8102.
  rewrite ?node_8094.
  rewrite ?node_8101.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8103 (s : N.State) (i : N.Inputs) :
  R.v8103 (state s) (inputs i) = Zmod.unsigned (N.v8103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8103 s i)) at 1.
  unfold R.v8103, N.v8103.
  rewrite !state_r672_nr_5F672.
  rewrite !state_r673_nr_5F673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r672_nr_5F672 s)).
  rewrite ?(bits.mod_to_Z (N.r673_nr_5F673 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8104 (s : N.State) (i : N.Inputs) :
  R.v8104 (state s) (inputs i) = Zmod.unsigned (N.v8104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8104 s i)) at 1.
  unfold R.v8104, N.v8104.
  rewrite ?node_8102.
  rewrite ?node_8103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8105 (s : N.State) (i : N.Inputs) :
  R.v8105 (state s) (inputs i) = Zmod.unsigned (N.v8105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8105 s i)) at 1.
  unfold R.v8105, N.v8105.
  rewrite ?node_7935.
  rewrite !state_r626_nr_5F626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r626_nr_5F626 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8106 (s : N.State) (i : N.Inputs) :
  R.v8106 (state s) (inputs i) = Zmod.unsigned (N.v8106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8106 s i)) at 1.
  unfold R.v8106, N.v8106.
  rewrite ?node_7936.
  rewrite ?node_7939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8107 (s : N.State) (i : N.Inputs) :
  R.v8107 (state s) (inputs i) = Zmod.unsigned (N.v8107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8107 s i)) at 1.
  unfold R.v8107, N.v8107.
  rewrite ?node_8105.
  rewrite ?node_8106.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8108 (s : N.State) (i : N.Inputs) :
  R.v8108 (state s) (inputs i) = Zmod.unsigned (N.v8108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8108 s i)) at 1.
  unfold R.v8108, N.v8108.
  rewrite ?node_8104.
  rewrite ?node_8107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8109 (s : N.State) (i : N.Inputs) :
  R.v8109 (state s) (inputs i) = Zmod.unsigned (N.v8109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8109 s i)) at 1.
  unfold R.v8109, N.v8109.
  rewrite ?node_7975.
  rewrite ?node_7982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8110 (s : N.State) (i : N.Inputs) :
  R.v8110 (state s) (inputs i) = Zmod.unsigned (N.v8110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8110 s i)) at 1.
  unfold R.v8110, N.v8110.
  rewrite ?node_7983.
  rewrite !state_r647_nr_5F647.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r647_nr_5F647 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8111 (s : N.State) (i : N.Inputs) :
  R.v8111 (state s) (inputs i) = Zmod.unsigned (N.v8111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8111 s i)) at 1.
  unfold R.v8111, N.v8111.
  rewrite ?node_8109.
  rewrite ?node_8110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8112 (s : N.State) (i : N.Inputs) :
  R.v8112 (state s) (inputs i) = Zmod.unsigned (N.v8112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8112 s i)) at 1.
  unfold R.v8112, N.v8112.
  rewrite ?node_8108.
  rewrite ?node_8111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8113 (s : N.State) (i : N.Inputs) :
  R.v8113 (state s) (inputs i) = Zmod.unsigned (N.v8113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8113 s i)) at 1.
  unfold R.v8113, N.v8113.
  rewrite ?node_8087.
  rewrite ?node_8112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8114 (s : N.State) (i : N.Inputs) :
  R.v8114 (state s) (inputs i) = Zmod.unsigned (N.v8114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8114 s i)) at 1.
  unfold R.v8114, N.v8114.
  rewrite ?node_7942.
  rewrite !state_r630_nr_5F630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r630_nr_5F630 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8115 (s : N.State) (i : N.Inputs) :
  R.v8115 (state s) (inputs i) = Zmod.unsigned (N.v8115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8115 s i)) at 1.
  unfold R.v8115, N.v8115.
  rewrite ?node_7943.
  rewrite ?node_7946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8116 (s : N.State) (i : N.Inputs) :
  R.v8116 (state s) (inputs i) = Zmod.unsigned (N.v8116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8116 s i)) at 1.
  unfold R.v8116, N.v8116.
  rewrite ?node_8114.
  rewrite ?node_8115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8117 (s : N.State) (i : N.Inputs) :
  R.v8117 (state s) (inputs i) = Zmod.unsigned (N.v8117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8117 s i)) at 1.
  unfold R.v8117, N.v8117.
  rewrite ?node_7950.
  rewrite !state_r634_nr_5F634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r634_nr_5F634 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8118 (s : N.State) (i : N.Inputs) :
  R.v8118 (state s) (inputs i) = Zmod.unsigned (N.v8118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8118 s i)) at 1.
  unfold R.v8118, N.v8118.
  rewrite ?node_7951.
  rewrite ?node_7954.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8119 (s : N.State) (i : N.Inputs) :
  R.v8119 (state s) (inputs i) = Zmod.unsigned (N.v8119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8119 s i)) at 1.
  unfold R.v8119, N.v8119.
  rewrite ?node_8117.
  rewrite ?node_8118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8120 (s : N.State) (i : N.Inputs) :
  R.v8120 (state s) (inputs i) = Zmod.unsigned (N.v8120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8120 s i)) at 1.
  unfold R.v8120, N.v8120.
  rewrite ?node_8116.
  rewrite ?node_8119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8121 (s : N.State) (i : N.Inputs) :
  R.v8121 (state s) (inputs i) = Zmod.unsigned (N.v8121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8121 s i)) at 1.
  unfold R.v8121, N.v8121.
  rewrite ?node_7958.
  rewrite !state_r638_nr_5F638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r638_nr_5F638 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8122 (s : N.State) (i : N.Inputs) :
  R.v8122 (state s) (inputs i) = Zmod.unsigned (N.v8122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8122 s i)) at 1.
  unfold R.v8122, N.v8122.
  rewrite ?node_7959.
  rewrite ?node_7962.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8123 (s : N.State) (i : N.Inputs) :
  R.v8123 (state s) (inputs i) = Zmod.unsigned (N.v8123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8123 s i)) at 1.
  unfold R.v8123, N.v8123.
  rewrite ?node_8121.
  rewrite ?node_8122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8124 (s : N.State) (i : N.Inputs) :
  R.v8124 (state s) (inputs i) = Zmod.unsigned (N.v8124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8124 s i)) at 1.
  unfold R.v8124, N.v8124.
  rewrite ?node_8120.
  rewrite ?node_8123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8125 (s : N.State) (i : N.Inputs) :
  R.v8125 (state s) (inputs i) = Zmod.unsigned (N.v8125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8125 s i)) at 1.
  unfold R.v8125, N.v8125.
  rewrite ?node_7970.
  rewrite !state_r642_nr_5F642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r642_nr_5F642 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8126 (s : N.State) (i : N.Inputs) :
  R.v8126 (state s) (inputs i) = Zmod.unsigned (N.v8126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8126 s i)) at 1.
  unfold R.v8126, N.v8126.
  rewrite ?node_7971.
  rewrite ?node_7974.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8127 (s : N.State) (i : N.Inputs) :
  R.v8127 (state s) (inputs i) = Zmod.unsigned (N.v8127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8127 s i)) at 1.
  unfold R.v8127, N.v8127.
  rewrite ?node_8125.
  rewrite ?node_8126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8128 (s : N.State) (i : N.Inputs) :
  R.v8128 (state s) (inputs i) = Zmod.unsigned (N.v8128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8128 s i)) at 1.
  unfold R.v8128, N.v8128.
  rewrite ?node_8124.
  rewrite ?node_8127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8129 (s : N.State) (i : N.Inputs) :
  R.v8129 (state s) (inputs i) = Zmod.unsigned (N.v8129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8129 s i)) at 1.
  unfold R.v8129, N.v8129.
  rewrite ?node_7996.
  rewrite ?node_7999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8130 (s : N.State) (i : N.Inputs) :
  R.v8130 (state s) (inputs i) = Zmod.unsigned (N.v8130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8130 s i)) at 1.
  unfold R.v8130, N.v8130.
  rewrite ?node_8000.
  rewrite ?node_8003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8131 (s : N.State) (i : N.Inputs) :
  R.v8131 (state s) (inputs i) = Zmod.unsigned (N.v8131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8131 s i)) at 1.
  unfold R.v8131, N.v8131.
  rewrite ?node_8129.
  rewrite ?node_8130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8132 (s : N.State) (i : N.Inputs) :
  R.v8132 (state s) (inputs i) = Zmod.unsigned (N.v8132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8132 s i)) at 1.
  unfold R.v8132, N.v8132.
  rewrite ?node_8128.
  rewrite ?node_8131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8133 (s : N.State) (i : N.Inputs) :
  R.v8133 (state s) (inputs i) = Zmod.unsigned (N.v8133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8133 s i)) at 1.
  unfold R.v8133, N.v8133.
  rewrite ?node_8113.
  rewrite ?node_8132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8134 (s : N.State) (i : N.Inputs) :
  R.v8134 (state s) (inputs i) = Zmod.unsigned (N.v8134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8134 s i)) at 1.
  unfold R.v8134, N.v8134.
  rewrite ?node_7977.
  rewrite !state_r646_nr_5F646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r646_nr_5F646 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8135 (s : N.State) (i : N.Inputs) :
  R.v8135 (state s) (inputs i) = Zmod.unsigned (N.v8135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8135 s i)) at 1.
  unfold R.v8135, N.v8135.
  rewrite ?node_7978.
  rewrite ?node_7981.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8136 (s : N.State) (i : N.Inputs) :
  R.v8136 (state s) (inputs i) = Zmod.unsigned (N.v8136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8136 s i)) at 1.
  unfold R.v8136, N.v8136.
  rewrite ?node_8134.
  rewrite ?node_8135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8137 (s : N.State) (i : N.Inputs) :
  R.v8137 (state s) (inputs i) = Zmod.unsigned (N.v8137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8137 s i)) at 1.
  unfold R.v8137, N.v8137.
  rewrite ?node_8133.
  rewrite ?node_8136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8138 (s : N.State) (i : N.Inputs) :
  R.v8138 (state s) (inputs i) = Zmod.unsigned (N.v8138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8138 s i)) at 1.
  unfold R.v8138, N.v8138.
  rewrite ?node_7968.
  rewrite ?node_7992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8139 (s : N.State) (i : N.Inputs) :
  R.v8139 (state s) (inputs i) = Zmod.unsigned (N.v8139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8139 s i)) at 1.
  unfold R.v8139, N.v8139.
  rewrite ?node_7993.
  rewrite ?node_8012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8140 (s : N.State) (i : N.Inputs) :
  R.v8140 (state s) (inputs i) = Zmod.unsigned (N.v8140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8140 s i)) at 1.
  unfold R.v8140, N.v8140.
  rewrite ?node_8138.
  rewrite ?node_8139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8141 (s : N.State) (i : N.Inputs) :
  R.v8141 (state s) (inputs i) = Zmod.unsigned (N.v8141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8141 s i)) at 1.
  unfold R.v8141, N.v8141.
  rewrite ?node_8137.
  rewrite ?node_8140.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8142 (s : N.State) (i : N.Inputs) :
  R.v8142 (state s) (inputs i) = Zmod.unsigned (N.v8142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8142 s i)) at 1.
  unfold R.v8142, N.v8142.
  rewrite ?node_7956.
  rewrite ?node_7963.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8143 (s : N.State) (i : N.Inputs) :
  R.v8143 (state s) (inputs i) = Zmod.unsigned (N.v8143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8143 s i)) at 1.
  unfold R.v8143, N.v8143.
  rewrite ?node_7964.
  rewrite ?node_7967.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8144 (s : N.State) (i : N.Inputs) :
  R.v8144 (state s) (inputs i) = Zmod.unsigned (N.v8144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8144 s i)) at 1.
  unfold R.v8144, N.v8144.
  rewrite ?node_8142.
  rewrite ?node_8143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8145 (s : N.State) (i : N.Inputs) :
  R.v8145 (state s) (inputs i) = Zmod.unsigned (N.v8145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8145 s i)) at 1.
  unfold R.v8145, N.v8145.
  rewrite ?node_7984.
  rewrite ?node_7987.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8146 (s : N.State) (i : N.Inputs) :
  R.v8146 (state s) (inputs i) = Zmod.unsigned (N.v8146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8146 s i)) at 1.
  unfold R.v8146, N.v8146.
  rewrite ?node_7988.
  rewrite ?node_7991.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8147 (s : N.State) (i : N.Inputs) :
  R.v8147 (state s) (inputs i) = Zmod.unsigned (N.v8147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8147 s i)) at 1.
  unfold R.v8147, N.v8147.
  rewrite ?node_8145.
  rewrite ?node_8146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8148 (s : N.State) (i : N.Inputs) :
  R.v8148 (state s) (inputs i) = Zmod.unsigned (N.v8148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8148 s i)) at 1.
  unfold R.v8148, N.v8148.
  rewrite ?node_8144.
  rewrite ?node_8147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8149 (s : N.State) (i : N.Inputs) :
  R.v8149 (state s) (inputs i) = Zmod.unsigned (N.v8149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8149 s i)) at 1.
  unfold R.v8149, N.v8149.
  rewrite ?node_8004.
  rewrite ?node_8007.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8150 (s : N.State) (i : N.Inputs) :
  R.v8150 (state s) (inputs i) = Zmod.unsigned (N.v8150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8150 s i)) at 1.
  unfold R.v8150, N.v8150.
  rewrite ?node_8008.
  rewrite ?node_8011.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8151 (s : N.State) (i : N.Inputs) :
  R.v8151 (state s) (inputs i) = Zmod.unsigned (N.v8151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8151 s i)) at 1.
  unfold R.v8151, N.v8151.
  rewrite ?node_8149.
  rewrite ?node_8150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8152 (s : N.State) (i : N.Inputs) :
  R.v8152 (state s) (inputs i) = Zmod.unsigned (N.v8152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8152 s i)) at 1.
  unfold R.v8152, N.v8152.
  rewrite ?node_8148.
  rewrite ?node_8151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8153 (s : N.State) (i : N.Inputs) :
  R.v8153 (state s) (inputs i) = Zmod.unsigned (N.v8153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8153 s i)) at 1.
  unfold R.v8153, N.v8153.
  rewrite ?node_8141.
  rewrite ?node_8152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8154 (s : N.State) (i : N.Inputs) :
  R.v8154 (state s) (inputs i) = Zmod.unsigned (N.v8154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8154 s i)) at 1.
  unfold R.v8154, N.v8154.
  rewrite ?node_8013.
  rewrite ?node_8016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8155 (s : N.State) (i : N.Inputs) :
  R.v8155 (state s) (inputs i) = Zmod.unsigned (N.v8155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8155 s i)) at 1.
  unfold R.v8155, N.v8155.
  rewrite ?node_8017.
  rewrite ?node_8020.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8156 (s : N.State) (i : N.Inputs) :
  R.v8156 (state s) (inputs i) = Zmod.unsigned (N.v8156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8156 s i)) at 1.
  unfold R.v8156, N.v8156.
  rewrite ?node_8154.
  rewrite ?node_8155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8157 (s : N.State) (i : N.Inputs) :
  R.v8157 (state s) (inputs i) = Zmod.unsigned (N.v8157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8157 s i)) at 1.
  unfold R.v8157, N.v8157.
  rewrite ?node_8153.
  rewrite ?node_8156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8158 (s : N.State) (i : N.Inputs) :
  R.v8158 (state s) (inputs i) = Zmod.unsigned (N.v8158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8158 s i)) at 1.
  unfold R.v8158, N.v8158.
  rewrite ?node_8024.
  rewrite ?node_8027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8159 (s : N.State) (i : N.Inputs) :
  R.v8159 (state s) (inputs i) = Zmod.unsigned (N.v8159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8159 s i)) at 1.
  unfold R.v8159, N.v8159.
  rewrite ?node_8028.
  rewrite ?node_8031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8160 (s : N.State) (i : N.Inputs) :
  R.v8160 (state s) (inputs i) = Zmod.unsigned (N.v8160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8160 s i)) at 1.
  unfold R.v8160, N.v8160.
  rewrite ?node_8158.
  rewrite ?node_8159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8161 (s : N.State) (i : N.Inputs) :
  R.v8161 (state s) (inputs i) = Zmod.unsigned (N.v8161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8161 s i)) at 1.
  unfold R.v8161, N.v8161.
  rewrite ?node_8157.
  rewrite ?node_8160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8162 (s : N.State) (i : N.Inputs) :
  R.v8162 (state s) (inputs i) = Zmod.unsigned (N.v8162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8162 s i)) at 1.
  unfold R.v8162, N.v8162.
  rewrite ?node_8021.
  rewrite ?node_8032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8163 (s : N.State) (i : N.Inputs) :
  R.v8163 (state s) (inputs i) = Zmod.unsigned (N.v8163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8163 s i)) at 1.
  unfold R.v8163, N.v8163.
  rewrite ?node_8033.
  rewrite ?node_8036.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8164 (s : N.State) (i : N.Inputs) :
  R.v8164 (state s) (inputs i) = Zmod.unsigned (N.v8164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8164 s i)) at 1.
  unfold R.v8164, N.v8164.
  rewrite ?node_8162.
  rewrite ?node_8163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8165 (s : N.State) (i : N.Inputs) :
  R.v8165 (state s) (inputs i) = Zmod.unsigned (N.v8165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8165 s i)) at 1.
  unfold R.v8165, N.v8165.
  rewrite ?node_8161.
  rewrite ?node_8164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8166 (s : N.State) (i : N.Inputs) :
  R.v8166 (state s) (inputs i) = Zmod.unsigned (N.v8166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8166 s i)) at 1.
  unfold R.v8166, N.v8166.
  rewrite ?node_8037.
  rewrite ?node_8040.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8167 (s : N.State) (i : N.Inputs) :
  R.v8167 (state s) (inputs i) = Zmod.unsigned (N.v8167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8167 s i)) at 1.
  unfold R.v8167, N.v8167.
  rewrite ?node_8041.
  rewrite ?node_8044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8168 (s : N.State) (i : N.Inputs) :
  R.v8168 (state s) (inputs i) = Zmod.unsigned (N.v8168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8168 s i)) at 1.
  unfold R.v8168, N.v8168.
  rewrite ?node_8166.
  rewrite ?node_8167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8169 (s : N.State) (i : N.Inputs) :
  R.v8169 (state s) (inputs i) = Zmod.unsigned (N.v8169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8169 s i)) at 1.
  unfold R.v8169, N.v8169.
  rewrite ?node_8165.
  rewrite ?node_8168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8170 (s : N.State) (i : N.Inputs) :
  R.v8170 (state s) (inputs i) = Zmod.unsigned (N.v8170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8170 s i)) at 1.
  unfold R.v8170, N.v8170.
  rewrite ?node_8169.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2369_nr_5F2400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2369_nr_5F2400 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8171 (s : N.State) (i : N.Inputs) :
  R.v8171 (state s) (inputs i) = Zmod.unsigned (N.v8171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8171 s i)) at 1.
  unfold R.v8171, N.v8171.
  rewrite ?node_8045.
  rewrite ?node_8048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8172 (s : N.State) (i : N.Inputs) :
  R.v8172 (state s) (inputs i) = Zmod.unsigned (N.v8172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8172 s i)) at 1.
  unfold R.v8172, N.v8172.
  rewrite ?node_8171.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2370_nr_5F2401.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2370_nr_5F2401 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8173 (s : N.State) (i : N.Inputs) :
  R.v8173 (state s) (inputs i) = Zmod.unsigned (N.v8173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8173 s i)) at 1.
  unfold R.v8173, N.v8173.
  rewrite !state_r674_nr_5F674.
  rewrite !state_r675_nr_5F675.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r674_nr_5F674 s)).
  rewrite ?(bits.mod_to_Z (N.r675_nr_5F675 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8174 (s : N.State) (i : N.Inputs) :
  R.v8174 (state s) (inputs i) = Zmod.unsigned (N.v8174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8174 s i)) at 1.
  unfold R.v8174, N.v8174.
  rewrite ?node_8173.
  rewrite !state_r676_nr_5F676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r676_nr_5F676 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8175 (s : N.State) (i : N.Inputs) :
  R.v8175 (state s) (inputs i) = Zmod.unsigned (N.v8175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8175 s i)) at 1.
  unfold R.v8175, N.v8175.
  rewrite ?node_8174.
  rewrite !state_r677_nr_5F677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r677_nr_5F677 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8176 (s : N.State) (i : N.Inputs) :
  R.v8176 (state s) (inputs i) = Zmod.unsigned (N.v8176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8176 s i)) at 1.
  unfold R.v8176, N.v8176.
  rewrite !state_r648_nr_5F648.
  rewrite !state_r649_nr_5F649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r648_nr_5F648 s)).
  rewrite ?(bits.mod_to_Z (N.r649_nr_5F649 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8177 (s : N.State) (i : N.Inputs) :
  R.v8177 (state s) (inputs i) = Zmod.unsigned (N.v8177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8177 s i)) at 1.
  unfold R.v8177, N.v8177.
  rewrite ?node_8053.
  rewrite !state_r650_nr_5F650.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r650_nr_5F650 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8178 (s : N.State) (i : N.Inputs) :
  R.v8178 (state s) (inputs i) = Zmod.unsigned (N.v8178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8178 s i)) at 1.
  unfold R.v8178, N.v8178.
  rewrite ?node_8176.
  rewrite ?node_8177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8179 (s : N.State) (i : N.Inputs) :
  R.v8179 (state s) (inputs i) = Zmod.unsigned (N.v8179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8179 s i)) at 1.
  unfold R.v8179, N.v8179.
  rewrite ?node_8175.
  rewrite ?node_8178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8180 (s : N.State) (i : N.Inputs) :
  R.v8180 (state s) (inputs i) = Zmod.unsigned (N.v8180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8180 s i)) at 1.
  unfold R.v8180, N.v8180.
  rewrite !state_r678_nr_5F678.
  rewrite !state_r679_nr_5F679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r678_nr_5F678 s)).
  rewrite ?(bits.mod_to_Z (N.r679_nr_5F679 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8181 (s : N.State) (i : N.Inputs) :
  R.v8181 (state s) (inputs i) = Zmod.unsigned (N.v8181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8181 s i)) at 1.
  unfold R.v8181, N.v8181.
  rewrite ?node_8180.
  rewrite !state_r680_nr_5F680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r680_nr_5F680 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8182 (s : N.State) (i : N.Inputs) :
  R.v8182 (state s) (inputs i) = Zmod.unsigned (N.v8182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8182 s i)) at 1.
  unfold R.v8182, N.v8182.
  rewrite ?node_8181.
  rewrite !state_r681_nr_5F681.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r681_nr_5F681 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8183 (s : N.State) (i : N.Inputs) :
  R.v8183 (state s) (inputs i) = Zmod.unsigned (N.v8183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8183 s i)) at 1.
  unfold R.v8183, N.v8183.
  rewrite !state_r652_nr_5F652.
  rewrite !state_r653_nr_5F653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r652_nr_5F652 s)).
  rewrite ?(bits.mod_to_Z (N.r653_nr_5F653 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8184 (s : N.State) (i : N.Inputs) :
  R.v8184 (state s) (inputs i) = Zmod.unsigned (N.v8184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8184 s i)) at 1.
  unfold R.v8184, N.v8184.
  rewrite ?node_8060.
  rewrite !state_r654_nr_5F654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r654_nr_5F654 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8185 (s : N.State) (i : N.Inputs) :
  R.v8185 (state s) (inputs i) = Zmod.unsigned (N.v8185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8185 s i)) at 1.
  unfold R.v8185, N.v8185.
  rewrite ?node_8183.
  rewrite ?node_8184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8186 (s : N.State) (i : N.Inputs) :
  R.v8186 (state s) (inputs i) = Zmod.unsigned (N.v8186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8186 s i)) at 1.
  unfold R.v8186, N.v8186.
  rewrite ?node_8182.
  rewrite ?node_8185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8187 (s : N.State) (i : N.Inputs) :
  R.v8187 (state s) (inputs i) = Zmod.unsigned (N.v8187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8187 s i)) at 1.
  unfold R.v8187, N.v8187.
  rewrite ?node_8179.
  rewrite ?node_8186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8188 (s : N.State) (i : N.Inputs) :
  R.v8188 (state s) (inputs i) = Zmod.unsigned (N.v8188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8188 s i)) at 1.
  unfold R.v8188, N.v8188.
  rewrite !state_r682_nr_5F682.
  rewrite !state_r683_nr_5F683.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r682_nr_5F682 s)).
  rewrite ?(bits.mod_to_Z (N.r683_nr_5F683 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8189 (s : N.State) (i : N.Inputs) :
  R.v8189 (state s) (inputs i) = Zmod.unsigned (N.v8189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8189 s i)) at 1.
  unfold R.v8189, N.v8189.
  rewrite ?node_8188.
  rewrite !state_r684_nr_5F684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r684_nr_5F684 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8190 (s : N.State) (i : N.Inputs) :
  R.v8190 (state s) (inputs i) = Zmod.unsigned (N.v8190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8190 s i)) at 1.
  unfold R.v8190, N.v8190.
  rewrite ?node_8189.
  rewrite !state_r685_nr_5F685.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r685_nr_5F685 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8191 (s : N.State) (i : N.Inputs) :
  R.v8191 (state s) (inputs i) = Zmod.unsigned (N.v8191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8191 s i)) at 1.
  unfold R.v8191, N.v8191.
  rewrite !state_r656_nr_5F656.
  rewrite !state_r657_nr_5F657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r656_nr_5F656 s)).
  rewrite ?(bits.mod_to_Z (N.r657_nr_5F657 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8192 (s : N.State) (i : N.Inputs) :
  R.v8192 (state s) (inputs i) = Zmod.unsigned (N.v8192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8192 s i)) at 1.
  unfold R.v8192, N.v8192.
  rewrite ?node_8068.
  rewrite !state_r658_nr_5F658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r658_nr_5F658 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8193 (s : N.State) (i : N.Inputs) :
  R.v8193 (state s) (inputs i) = Zmod.unsigned (N.v8193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8193 s i)) at 1.
  unfold R.v8193, N.v8193.
  rewrite ?node_8191.
  rewrite ?node_8192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8194 (s : N.State) (i : N.Inputs) :
  R.v8194 (state s) (inputs i) = Zmod.unsigned (N.v8194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8194 s i)) at 1.
  unfold R.v8194, N.v8194.
  rewrite ?node_8190.
  rewrite ?node_8193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8195 (s : N.State) (i : N.Inputs) :
  R.v8195 (state s) (inputs i) = Zmod.unsigned (N.v8195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8195 s i)) at 1.
  unfold R.v8195, N.v8195.
  rewrite ?node_8187.
  rewrite ?node_8194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8196 (s : N.State) (i : N.Inputs) :
  R.v8196 (state s) (inputs i) = Zmod.unsigned (N.v8196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8196 s i)) at 1.
  unfold R.v8196, N.v8196.
  rewrite !state_r686_nr_5F686.
  rewrite !state_r687_nr_5F687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r686_nr_5F686 s)).
  rewrite ?(bits.mod_to_Z (N.r687_nr_5F687 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8197 (s : N.State) (i : N.Inputs) :
  R.v8197 (state s) (inputs i) = Zmod.unsigned (N.v8197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8197 s i)) at 1.
  unfold R.v8197, N.v8197.
  rewrite ?node_8196.
  rewrite !state_r688_nr_5F688.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r688_nr_5F688 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8198 (s : N.State) (i : N.Inputs) :
  R.v8198 (state s) (inputs i) = Zmod.unsigned (N.v8198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8198 s i)) at 1.
  unfold R.v8198, N.v8198.
  rewrite ?node_8197.
  rewrite !state_r689_nr_5F689.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r689_nr_5F689 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8199 (s : N.State) (i : N.Inputs) :
  R.v8199 (state s) (inputs i) = Zmod.unsigned (N.v8199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8199 s i)) at 1.
  unfold R.v8199, N.v8199.
  rewrite !state_r660_nr_5F660.
  rewrite !state_r661_nr_5F661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r660_nr_5F660 s)).
  rewrite ?(bits.mod_to_Z (N.r661_nr_5F661 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8200 (s : N.State) (i : N.Inputs) :
  R.v8200 (state s) (inputs i) = Zmod.unsigned (N.v8200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8200 s i)) at 1.
  unfold R.v8200, N.v8200.
  rewrite ?node_8076.
  rewrite !state_r662_nr_5F662.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r662_nr_5F662 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8201 (s : N.State) (i : N.Inputs) :
  R.v8201 (state s) (inputs i) = Zmod.unsigned (N.v8201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8201 s i)) at 1.
  unfold R.v8201, N.v8201.
  rewrite ?node_8199.
  rewrite ?node_8200.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8202 (s : N.State) (i : N.Inputs) :
  R.v8202 (state s) (inputs i) = Zmod.unsigned (N.v8202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8202 s i)) at 1.
  unfold R.v8202, N.v8202.
  rewrite ?node_8198.
  rewrite ?node_8201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8203 (s : N.State) (i : N.Inputs) :
  R.v8203 (state s) (inputs i) = Zmod.unsigned (N.v8203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8203 s i)) at 1.
  unfold R.v8203, N.v8203.
  rewrite ?node_8195.
  rewrite ?node_8202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8204 (s : N.State) (i : N.Inputs) :
  R.v8204 (state s) (inputs i) = Zmod.unsigned (N.v8204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8204 s i)) at 1.
  unfold R.v8204, N.v8204.
  rewrite ?node_8059.
  rewrite ?node_8066.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8205 (s : N.State) (i : N.Inputs) :
  R.v8205 (state s) (inputs i) = Zmod.unsigned (N.v8205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8205 s i)) at 1.
  unfold R.v8205, N.v8205.
  rewrite ?node_8067.
  rewrite ?node_8074.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8206 (s : N.State) (i : N.Inputs) :
  R.v8206 (state s) (inputs i) = Zmod.unsigned (N.v8206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8206 s i)) at 1.
  unfold R.v8206, N.v8206.
  rewrite ?node_8204.
  rewrite ?node_8205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8207 (s : N.State) (i : N.Inputs) :
  R.v8207 (state s) (inputs i) = Zmod.unsigned (N.v8207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8207 s i)) at 1.
  unfold R.v8207, N.v8207.
  rewrite ?node_8203.
  rewrite ?node_8206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8208 (s : N.State) (i : N.Inputs) :
  R.v8208 (state s) (inputs i) = Zmod.unsigned (N.v8208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8208 s i)) at 1.
  unfold R.v8208, N.v8208.
  rewrite !state_r690_nr_5F690.
  rewrite !state_r691_nr_5F691.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r690_nr_5F690 s)).
  rewrite ?(bits.mod_to_Z (N.r691_nr_5F691 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8209 (s : N.State) (i : N.Inputs) :
  R.v8209 (state s) (inputs i) = Zmod.unsigned (N.v8209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8209 s i)) at 1.
  unfold R.v8209, N.v8209.
  rewrite ?node_8208.
  rewrite !state_r692_nr_5F692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r692_nr_5F692 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8210 (s : N.State) (i : N.Inputs) :
  R.v8210 (state s) (inputs i) = Zmod.unsigned (N.v8210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8210 s i)) at 1.
  unfold R.v8210, N.v8210.
  rewrite ?node_8209.
  rewrite !state_r693_nr_5F693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r693_nr_5F693 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8211 (s : N.State) (i : N.Inputs) :
  R.v8211 (state s) (inputs i) = Zmod.unsigned (N.v8211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8211 s i)) at 1.
  unfold R.v8211, N.v8211.
  rewrite !state_r664_nr_5F664.
  rewrite !state_r665_nr_5F665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r664_nr_5F664 s)).
  rewrite ?(bits.mod_to_Z (N.r665_nr_5F665 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8212 (s : N.State) (i : N.Inputs) :
  R.v8212 (state s) (inputs i) = Zmod.unsigned (N.v8212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8212 s i)) at 1.
  unfold R.v8212, N.v8212.
  rewrite ?node_8088.
  rewrite !state_r666_nr_5F666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r666_nr_5F666 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8213 (s : N.State) (i : N.Inputs) :
  R.v8213 (state s) (inputs i) = Zmod.unsigned (N.v8213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8213 s i)) at 1.
  unfold R.v8213, N.v8213.
  rewrite ?node_8211.
  rewrite ?node_8212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8214 (s : N.State) (i : N.Inputs) :
  R.v8214 (state s) (inputs i) = Zmod.unsigned (N.v8214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8214 s i)) at 1.
  unfold R.v8214, N.v8214.
  rewrite ?node_8210.
  rewrite ?node_8213.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8215 (s : N.State) (i : N.Inputs) :
  R.v8215 (state s) (inputs i) = Zmod.unsigned (N.v8215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8215 s i)) at 1.
  unfold R.v8215, N.v8215.
  rewrite !state_r694_nr_5F694.
  rewrite !state_r695_nr_5F695.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r694_nr_5F694 s)).
  rewrite ?(bits.mod_to_Z (N.r695_nr_5F695 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8216 (s : N.State) (i : N.Inputs) :
  R.v8216 (state s) (inputs i) = Zmod.unsigned (N.v8216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8216 s i)) at 1.
  unfold R.v8216, N.v8216.
  rewrite ?node_8215.
  rewrite !state_r696_nr_5F696.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r696_nr_5F696 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8217 (s : N.State) (i : N.Inputs) :
  R.v8217 (state s) (inputs i) = Zmod.unsigned (N.v8217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8217 s i)) at 1.
  unfold R.v8217, N.v8217.
  rewrite ?node_8216.
  rewrite !state_r697_nr_5F697.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r697_nr_5F697 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8218 (s : N.State) (i : N.Inputs) :
  R.v8218 (state s) (inputs i) = Zmod.unsigned (N.v8218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8218 s i)) at 1.
  unfold R.v8218, N.v8218.
  rewrite !state_r668_nr_5F668.
  rewrite !state_r669_nr_5F669.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r668_nr_5F668 s)).
  rewrite ?(bits.mod_to_Z (N.r669_nr_5F669 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8219 (s : N.State) (i : N.Inputs) :
  R.v8219 (state s) (inputs i) = Zmod.unsigned (N.v8219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8219 s i)) at 1.
  unfold R.v8219, N.v8219.
  rewrite ?node_8095.
  rewrite !state_r670_nr_5F670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r670_nr_5F670 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8220 (s : N.State) (i : N.Inputs) :
  R.v8220 (state s) (inputs i) = Zmod.unsigned (N.v8220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8220 s i)) at 1.
  unfold R.v8220, N.v8220.
  rewrite ?node_8218.
  rewrite ?node_8219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8221 (s : N.State) (i : N.Inputs) :
  R.v8221 (state s) (inputs i) = Zmod.unsigned (N.v8221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8221 s i)) at 1.
  unfold R.v8221, N.v8221.
  rewrite ?node_8217.
  rewrite ?node_8220.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8222 (s : N.State) (i : N.Inputs) :
  R.v8222 (state s) (inputs i) = Zmod.unsigned (N.v8222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8222 s i)) at 1.
  unfold R.v8222, N.v8222.
  rewrite ?node_8214.
  rewrite ?node_8221.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8223 (s : N.State) (i : N.Inputs) :
  R.v8223 (state s) (inputs i) = Zmod.unsigned (N.v8223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8223 s i)) at 1.
  unfold R.v8223, N.v8223.
  rewrite !state_r698_nr_5F698.
  rewrite !state_r699_nr_5F699.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r698_nr_5F698 s)).
  rewrite ?(bits.mod_to_Z (N.r699_nr_5F699 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8224 (s : N.State) (i : N.Inputs) :
  R.v8224 (state s) (inputs i) = Zmod.unsigned (N.v8224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8224 s i)) at 1.
  unfold R.v8224, N.v8224.
  rewrite ?node_8222.
  rewrite ?node_8223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8225 (s : N.State) (i : N.Inputs) :
  R.v8225 (state s) (inputs i) = Zmod.unsigned (N.v8225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8225 s i)) at 1.
  unfold R.v8225, N.v8225.
  rewrite ?node_8054.
  rewrite !state_r651_nr_5F651.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r651_nr_5F651 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8226 (s : N.State) (i : N.Inputs) :
  R.v8226 (state s) (inputs i) = Zmod.unsigned (N.v8226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8226 s i)) at 1.
  unfold R.v8226, N.v8226.
  rewrite ?node_8055.
  rewrite ?node_8058.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8227 (s : N.State) (i : N.Inputs) :
  R.v8227 (state s) (inputs i) = Zmod.unsigned (N.v8227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8227 s i)) at 1.
  unfold R.v8227, N.v8227.
  rewrite ?node_8225.
  rewrite ?node_8226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8228 (s : N.State) (i : N.Inputs) :
  R.v8228 (state s) (inputs i) = Zmod.unsigned (N.v8228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8228 s i)) at 1.
  unfold R.v8228, N.v8228.
  rewrite ?node_8224.
  rewrite ?node_8227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8229 (s : N.State) (i : N.Inputs) :
  R.v8229 (state s) (inputs i) = Zmod.unsigned (N.v8229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8229 s i)) at 1.
  unfold R.v8229, N.v8229.
  rewrite ?node_8094.
  rewrite ?node_8101.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8230 (s : N.State) (i : N.Inputs) :
  R.v8230 (state s) (inputs i) = Zmod.unsigned (N.v8230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8230 s i)) at 1.
  unfold R.v8230, N.v8230.
  rewrite ?node_8102.
  rewrite ?node_8103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8231 (s : N.State) (i : N.Inputs) :
  R.v8231 (state s) (inputs i) = Zmod.unsigned (N.v8231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8231 s i)) at 1.
  unfold R.v8231, N.v8231.
  rewrite ?node_8229.
  rewrite ?node_8230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8232 (s : N.State) (i : N.Inputs) :
  R.v8232 (state s) (inputs i) = Zmod.unsigned (N.v8232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8232 s i)) at 1.
  unfold R.v8232, N.v8232.
  rewrite ?node_8228.
  rewrite ?node_8231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8233 (s : N.State) (i : N.Inputs) :
  R.v8233 (state s) (inputs i) = Zmod.unsigned (N.v8233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8233 s i)) at 1.
  unfold R.v8233, N.v8233.
  rewrite ?node_8207.
  rewrite ?node_8232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8234 (s : N.State) (i : N.Inputs) :
  R.v8234 (state s) (inputs i) = Zmod.unsigned (N.v8234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8234 s i)) at 1.
  unfold R.v8234, N.v8234.
  rewrite ?node_8061.
  rewrite !state_r655_nr_5F655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r655_nr_5F655 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8235 (s : N.State) (i : N.Inputs) :
  R.v8235 (state s) (inputs i) = Zmod.unsigned (N.v8235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8235 s i)) at 1.
  unfold R.v8235, N.v8235.
  rewrite ?node_8062.
  rewrite ?node_8065.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8236 (s : N.State) (i : N.Inputs) :
  R.v8236 (state s) (inputs i) = Zmod.unsigned (N.v8236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8236 s i)) at 1.
  unfold R.v8236, N.v8236.
  rewrite ?node_8234.
  rewrite ?node_8235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8237 (s : N.State) (i : N.Inputs) :
  R.v8237 (state s) (inputs i) = Zmod.unsigned (N.v8237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8237 s i)) at 1.
  unfold R.v8237, N.v8237.
  rewrite ?node_8069.
  rewrite !state_r659_nr_5F659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r659_nr_5F659 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8238 (s : N.State) (i : N.Inputs) :
  R.v8238 (state s) (inputs i) = Zmod.unsigned (N.v8238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8238 s i)) at 1.
  unfold R.v8238, N.v8238.
  rewrite ?node_8070.
  rewrite ?node_8073.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8239 (s : N.State) (i : N.Inputs) :
  R.v8239 (state s) (inputs i) = Zmod.unsigned (N.v8239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8239 s i)) at 1.
  unfold R.v8239, N.v8239.
  rewrite ?node_8237.
  rewrite ?node_8238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8240 (s : N.State) (i : N.Inputs) :
  R.v8240 (state s) (inputs i) = Zmod.unsigned (N.v8240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8240 s i)) at 1.
  unfold R.v8240, N.v8240.
  rewrite ?node_8236.
  rewrite ?node_8239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8241 (s : N.State) (i : N.Inputs) :
  R.v8241 (state s) (inputs i) = Zmod.unsigned (N.v8241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8241 s i)) at 1.
  unfold R.v8241, N.v8241.
  rewrite ?node_8077.
  rewrite !state_r663_nr_5F663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r663_nr_5F663 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8242 (s : N.State) (i : N.Inputs) :
  R.v8242 (state s) (inputs i) = Zmod.unsigned (N.v8242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8242 s i)) at 1.
  unfold R.v8242, N.v8242.
  rewrite ?node_8078.
  rewrite ?node_8081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8243 (s : N.State) (i : N.Inputs) :
  R.v8243 (state s) (inputs i) = Zmod.unsigned (N.v8243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8243 s i)) at 1.
  unfold R.v8243, N.v8243.
  rewrite ?node_8241.
  rewrite ?node_8242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8244 (s : N.State) (i : N.Inputs) :
  R.v8244 (state s) (inputs i) = Zmod.unsigned (N.v8244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8244 s i)) at 1.
  unfold R.v8244, N.v8244.
  rewrite ?node_8240.
  rewrite ?node_8243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8245 (s : N.State) (i : N.Inputs) :
  R.v8245 (state s) (inputs i) = Zmod.unsigned (N.v8245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8245 s i)) at 1.
  unfold R.v8245, N.v8245.
  rewrite ?node_8089.
  rewrite !state_r667_nr_5F667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r667_nr_5F667 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8246 (s : N.State) (i : N.Inputs) :
  R.v8246 (state s) (inputs i) = Zmod.unsigned (N.v8246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8246 s i)) at 1.
  unfold R.v8246, N.v8246.
  rewrite ?node_8090.
  rewrite ?node_8093.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8247 (s : N.State) (i : N.Inputs) :
  R.v8247 (state s) (inputs i) = Zmod.unsigned (N.v8247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8247 s i)) at 1.
  unfold R.v8247, N.v8247.
  rewrite ?node_8245.
  rewrite ?node_8246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8248 (s : N.State) (i : N.Inputs) :
  R.v8248 (state s) (inputs i) = Zmod.unsigned (N.v8248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8248 s i)) at 1.
  unfold R.v8248, N.v8248.
  rewrite ?node_8244.
  rewrite ?node_8247.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8249 (s : N.State) (i : N.Inputs) :
  R.v8249 (state s) (inputs i) = Zmod.unsigned (N.v8249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8249 s i)) at 1.
  unfold R.v8249, N.v8249.
  rewrite ?node_8116.
  rewrite ?node_8119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8250 (s : N.State) (i : N.Inputs) :
  R.v8250 (state s) (inputs i) = Zmod.unsigned (N.v8250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8250 s i)) at 1.
  unfold R.v8250, N.v8250.
  rewrite ?node_8120.
  rewrite ?node_8123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8251 (s : N.State) (i : N.Inputs) :
  R.v8251 (state s) (inputs i) = Zmod.unsigned (N.v8251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8251 s i)) at 1.
  unfold R.v8251, N.v8251.
  rewrite ?node_8249.
  rewrite ?node_8250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8252 (s : N.State) (i : N.Inputs) :
  R.v8252 (state s) (inputs i) = Zmod.unsigned (N.v8252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8252 s i)) at 1.
  unfold R.v8252, N.v8252.
  rewrite ?node_8248.
  rewrite ?node_8251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8253 (s : N.State) (i : N.Inputs) :
  R.v8253 (state s) (inputs i) = Zmod.unsigned (N.v8253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8253 s i)) at 1.
  unfold R.v8253, N.v8253.
  rewrite ?node_8233.
  rewrite ?node_8252.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8254 (s : N.State) (i : N.Inputs) :
  R.v8254 (state s) (inputs i) = Zmod.unsigned (N.v8254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8254 s i)) at 1.
  unfold R.v8254, N.v8254.
  rewrite ?node_8096.
  rewrite !state_r671_nr_5F671.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r671_nr_5F671 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8255 (s : N.State) (i : N.Inputs) :
  R.v8255 (state s) (inputs i) = Zmod.unsigned (N.v8255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8255 s i)) at 1.
  unfold R.v8255, N.v8255.
  rewrite ?node_8097.
  rewrite ?node_8100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8256 (s : N.State) (i : N.Inputs) :
  R.v8256 (state s) (inputs i) = Zmod.unsigned (N.v8256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8256 s i)) at 1.
  unfold R.v8256, N.v8256.
  rewrite ?node_8254.
  rewrite ?node_8255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8257 (s : N.State) (i : N.Inputs) :
  R.v8257 (state s) (inputs i) = Zmod.unsigned (N.v8257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8257 s i)) at 1.
  unfold R.v8257, N.v8257.
  rewrite !state_r672_nr_5F672.
  rewrite !state_r673_nr_5F673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r672_nr_5F672 s)).
  rewrite ?(bits.mod_to_Z (N.r673_nr_5F673 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8258 (s : N.State) (i : N.Inputs) :
  R.v8258 (state s) (inputs i) = Zmod.unsigned (N.v8258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8258 s i)) at 1.
  unfold R.v8258, N.v8258.
  rewrite ?node_8256.
  rewrite ?node_8257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8259 (s : N.State) (i : N.Inputs) :
  R.v8259 (state s) (inputs i) = Zmod.unsigned (N.v8259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8259 s i)) at 1.
  unfold R.v8259, N.v8259.
  rewrite ?node_8253.
  rewrite ?node_8258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8260 (s : N.State) (i : N.Inputs) :
  R.v8260 (state s) (inputs i) = Zmod.unsigned (N.v8260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8260 s i)) at 1.
  unfold R.v8260, N.v8260.
  rewrite ?node_8087.
  rewrite ?node_8112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8261 (s : N.State) (i : N.Inputs) :
  R.v8261 (state s) (inputs i) = Zmod.unsigned (N.v8261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8261 s i)) at 1.
  unfold R.v8261, N.v8261.
  rewrite ?node_8113.
  rewrite ?node_8132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8262 (s : N.State) (i : N.Inputs) :
  R.v8262 (state s) (inputs i) = Zmod.unsigned (N.v8262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8262 s i)) at 1.
  unfold R.v8262, N.v8262.
  rewrite ?node_8260.
  rewrite ?node_8261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8263 (s : N.State) (i : N.Inputs) :
  R.v8263 (state s) (inputs i) = Zmod.unsigned (N.v8263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8263 s i)) at 1.
  unfold R.v8263, N.v8263.
  rewrite ?node_8259.
  rewrite ?node_8262.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8264 (s : N.State) (i : N.Inputs) :
  R.v8264 (state s) (inputs i) = Zmod.unsigned (N.v8264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8264 s i)) at 1.
  unfold R.v8264, N.v8264.
  rewrite ?node_8075.
  rewrite ?node_8082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8265 (s : N.State) (i : N.Inputs) :
  R.v8265 (state s) (inputs i) = Zmod.unsigned (N.v8265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8265 s i)) at 1.
  unfold R.v8265, N.v8265.
  rewrite ?node_8083.
  rewrite ?node_8086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8266 (s : N.State) (i : N.Inputs) :
  R.v8266 (state s) (inputs i) = Zmod.unsigned (N.v8266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8266 s i)) at 1.
  unfold R.v8266, N.v8266.
  rewrite ?node_8264.
  rewrite ?node_8265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8267 (s : N.State) (i : N.Inputs) :
  R.v8267 (state s) (inputs i) = Zmod.unsigned (N.v8267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8267 s i)) at 1.
  unfold R.v8267, N.v8267.
  rewrite ?node_8104.
  rewrite ?node_8107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8268 (s : N.State) (i : N.Inputs) :
  R.v8268 (state s) (inputs i) = Zmod.unsigned (N.v8268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8268 s i)) at 1.
  unfold R.v8268, N.v8268.
  rewrite ?node_8108.
  rewrite ?node_8111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8269 (s : N.State) (i : N.Inputs) :
  R.v8269 (state s) (inputs i) = Zmod.unsigned (N.v8269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8269 s i)) at 1.
  unfold R.v8269, N.v8269.
  rewrite ?node_8267.
  rewrite ?node_8268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8270 (s : N.State) (i : N.Inputs) :
  R.v8270 (state s) (inputs i) = Zmod.unsigned (N.v8270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8270 s i)) at 1.
  unfold R.v8270, N.v8270.
  rewrite ?node_8266.
  rewrite ?node_8269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8271 (s : N.State) (i : N.Inputs) :
  R.v8271 (state s) (inputs i) = Zmod.unsigned (N.v8271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8271 s i)) at 1.
  unfold R.v8271, N.v8271.
  rewrite ?node_8124.
  rewrite ?node_8127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8272 (s : N.State) (i : N.Inputs) :
  R.v8272 (state s) (inputs i) = Zmod.unsigned (N.v8272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8272 s i)) at 1.
  unfold R.v8272, N.v8272.
  rewrite ?node_8128.
  rewrite ?node_8131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8273 (s : N.State) (i : N.Inputs) :
  R.v8273 (state s) (inputs i) = Zmod.unsigned (N.v8273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8273 s i)) at 1.
  unfold R.v8273, N.v8273.
  rewrite ?node_8271.
  rewrite ?node_8272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8274 (s : N.State) (i : N.Inputs) :
  R.v8274 (state s) (inputs i) = Zmod.unsigned (N.v8274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8274 s i)) at 1.
  unfold R.v8274, N.v8274.
  rewrite ?node_8270.
  rewrite ?node_8273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8275 (s : N.State) (i : N.Inputs) :
  R.v8275 (state s) (inputs i) = Zmod.unsigned (N.v8275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8275 s i)) at 1.
  unfold R.v8275, N.v8275.
  rewrite ?node_8263.
  rewrite ?node_8274.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8276 (s : N.State) (i : N.Inputs) :
  R.v8276 (state s) (inputs i) = Zmod.unsigned (N.v8276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8276 s i)) at 1.
  unfold R.v8276, N.v8276.
  rewrite ?node_8133.
  rewrite ?node_8136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8277 (s : N.State) (i : N.Inputs) :
  R.v8277 (state s) (inputs i) = Zmod.unsigned (N.v8277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8277 s i)) at 1.
  unfold R.v8277, N.v8277.
  rewrite ?node_8137.
  rewrite ?node_8140.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8278 (s : N.State) (i : N.Inputs) :
  R.v8278 (state s) (inputs i) = Zmod.unsigned (N.v8278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8278 s i)) at 1.
  unfold R.v8278, N.v8278.
  rewrite ?node_8276.
  rewrite ?node_8277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8279 (s : N.State) (i : N.Inputs) :
  R.v8279 (state s) (inputs i) = Zmod.unsigned (N.v8279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8279 s i)) at 1.
  unfold R.v8279, N.v8279.
  rewrite ?node_8275.
  rewrite ?node_8278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8280 (s : N.State) (i : N.Inputs) :
  R.v8280 (state s) (inputs i) = Zmod.unsigned (N.v8280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8280 s i)) at 1.
  unfold R.v8280, N.v8280.
  rewrite ?node_8144.
  rewrite ?node_8147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8281 (s : N.State) (i : N.Inputs) :
  R.v8281 (state s) (inputs i) = Zmod.unsigned (N.v8281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8281 s i)) at 1.
  unfold R.v8281, N.v8281.
  rewrite ?node_8148.
  rewrite ?node_8151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8282 (s : N.State) (i : N.Inputs) :
  R.v8282 (state s) (inputs i) = Zmod.unsigned (N.v8282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8282 s i)) at 1.
  unfold R.v8282, N.v8282.
  rewrite ?node_8280.
  rewrite ?node_8281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8283 (s : N.State) (i : N.Inputs) :
  R.v8283 (state s) (inputs i) = Zmod.unsigned (N.v8283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8283 s i)) at 1.
  unfold R.v8283, N.v8283.
  rewrite ?node_8279.
  rewrite ?node_8282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8284 (s : N.State) (i : N.Inputs) :
  R.v8284 (state s) (inputs i) = Zmod.unsigned (N.v8284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8284 s i)) at 1.
  unfold R.v8284, N.v8284.
  rewrite ?node_8141.
  rewrite ?node_8152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8285 (s : N.State) (i : N.Inputs) :
  R.v8285 (state s) (inputs i) = Zmod.unsigned (N.v8285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8285 s i)) at 1.
  unfold R.v8285, N.v8285.
  rewrite ?node_8153.
  rewrite ?node_8156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8286 (s : N.State) (i : N.Inputs) :
  R.v8286 (state s) (inputs i) = Zmod.unsigned (N.v8286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8286 s i)) at 1.
  unfold R.v8286, N.v8286.
  rewrite ?node_8284.
  rewrite ?node_8285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8287 (s : N.State) (i : N.Inputs) :
  R.v8287 (state s) (inputs i) = Zmod.unsigned (N.v8287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8287 s i)) at 1.
  unfold R.v8287, N.v8287.
  rewrite ?node_8283.
  rewrite ?node_8286.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8288 (s : N.State) (i : N.Inputs) :
  R.v8288 (state s) (inputs i) = Zmod.unsigned (N.v8288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8288 s i)) at 1.
  unfold R.v8288, N.v8288.
  rewrite ?node_8157.
  rewrite ?node_8160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8289 (s : N.State) (i : N.Inputs) :
  R.v8289 (state s) (inputs i) = Zmod.unsigned (N.v8289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8289 s i)) at 1.
  unfold R.v8289, N.v8289.
  rewrite ?node_8161.
  rewrite ?node_8164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8290 (s : N.State) (i : N.Inputs) :
  R.v8290 (state s) (inputs i) = Zmod.unsigned (N.v8290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8290 s i)) at 1.
  unfold R.v8290, N.v8290.
  rewrite ?node_8288.
  rewrite ?node_8289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8291 (s : N.State) (i : N.Inputs) :
  R.v8291 (state s) (inputs i) = Zmod.unsigned (N.v8291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8291 s i)) at 1.
  unfold R.v8291, N.v8291.
  rewrite ?node_8287.
  rewrite ?node_8290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8292 (s : N.State) (i : N.Inputs) :
  R.v8292 (state s) (inputs i) = Zmod.unsigned (N.v8292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8292 s i)) at 1.
  unfold R.v8292, N.v8292.
  rewrite ?node_8291.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2371_nr_5F2402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2371_nr_5F2402 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8293 (s : N.State) (i : N.Inputs) :
  R.v8293 (state s) (inputs i) = Zmod.unsigned (N.v8293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8293 s i)) at 1.
  unfold R.v8293, N.v8293.
  rewrite ?node_8165.
  rewrite ?node_8168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8294 (s : N.State) (i : N.Inputs) :
  R.v8294 (state s) (inputs i) = Zmod.unsigned (N.v8294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8294 s i)) at 1.
  unfold R.v8294, N.v8294.
  rewrite ?node_8293.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2372_nr_5F2403.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2372_nr_5F2403 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8295 (s : N.State) (i : N.Inputs) :
  R.v8295 (state s) (inputs i) = Zmod.unsigned (N.v8295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8295 s i)) at 1.
  unfold R.v8295, N.v8295.
  rewrite !state_r700_nr_5F700.
  rewrite !state_r701_nr_5F701.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r700_nr_5F700 s)).
  rewrite ?(bits.mod_to_Z (N.r701_nr_5F701 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8296 (s : N.State) (i : N.Inputs) :
  R.v8296 (state s) (inputs i) = Zmod.unsigned (N.v8296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8296 s i)) at 1.
  unfold R.v8296, N.v8296.
  rewrite ?node_8295.
  rewrite !state_r702_nr_5F702.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r702_nr_5F702 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8297 (s : N.State) (i : N.Inputs) :
  R.v8297 (state s) (inputs i) = Zmod.unsigned (N.v8297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8297 s i)) at 1.
  unfold R.v8297, N.v8297.
  rewrite ?node_8296.
  rewrite !state_r703_nr_5F703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r703_nr_5F703 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8298 (s : N.State) (i : N.Inputs) :
  R.v8298 (state s) (inputs i) = Zmod.unsigned (N.v8298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8298 s i)) at 1.
  unfold R.v8298, N.v8298.
  rewrite !state_r674_nr_5F674.
  rewrite !state_r675_nr_5F675.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r674_nr_5F674 s)).
  rewrite ?(bits.mod_to_Z (N.r675_nr_5F675 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8299 (s : N.State) (i : N.Inputs) :
  R.v8299 (state s) (inputs i) = Zmod.unsigned (N.v8299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8299 s i)) at 1.
  unfold R.v8299, N.v8299.
  rewrite ?node_8173.
  rewrite !state_r676_nr_5F676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r676_nr_5F676 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8300 (s : N.State) (i : N.Inputs) :
  R.v8300 (state s) (inputs i) = Zmod.unsigned (N.v8300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8300 s i)) at 1.
  unfold R.v8300, N.v8300.
  rewrite ?node_8298.
  rewrite ?node_8299.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8301 (s : N.State) (i : N.Inputs) :
  R.v8301 (state s) (inputs i) = Zmod.unsigned (N.v8301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8301 s i)) at 1.
  unfold R.v8301, N.v8301.
  rewrite ?node_8297.
  rewrite ?node_8300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8302 (s : N.State) (i : N.Inputs) :
  R.v8302 (state s) (inputs i) = Zmod.unsigned (N.v8302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8302 s i)) at 1.
  unfold R.v8302, N.v8302.
  rewrite !state_r704_nr_5F704.
  rewrite !state_r705_nr_5F705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r704_nr_5F704 s)).
  rewrite ?(bits.mod_to_Z (N.r705_nr_5F705 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8303 (s : N.State) (i : N.Inputs) :
  R.v8303 (state s) (inputs i) = Zmod.unsigned (N.v8303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8303 s i)) at 1.
  unfold R.v8303, N.v8303.
  rewrite ?node_8302.
  rewrite !state_r706_nr_5F706.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r706_nr_5F706 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8304 (s : N.State) (i : N.Inputs) :
  R.v8304 (state s) (inputs i) = Zmod.unsigned (N.v8304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8304 s i)) at 1.
  unfold R.v8304, N.v8304.
  rewrite ?node_8303.
  rewrite !state_r707_nr_5F707.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r707_nr_5F707 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8305 (s : N.State) (i : N.Inputs) :
  R.v8305 (state s) (inputs i) = Zmod.unsigned (N.v8305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8305 s i)) at 1.
  unfold R.v8305, N.v8305.
  rewrite !state_r678_nr_5F678.
  rewrite !state_r679_nr_5F679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r678_nr_5F678 s)).
  rewrite ?(bits.mod_to_Z (N.r679_nr_5F679 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8306 (s : N.State) (i : N.Inputs) :
  R.v8306 (state s) (inputs i) = Zmod.unsigned (N.v8306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8306 s i)) at 1.
  unfold R.v8306, N.v8306.
  rewrite ?node_8180.
  rewrite !state_r680_nr_5F680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r680_nr_5F680 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8307 (s : N.State) (i : N.Inputs) :
  R.v8307 (state s) (inputs i) = Zmod.unsigned (N.v8307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8307 s i)) at 1.
  unfold R.v8307, N.v8307.
  rewrite ?node_8305.
  rewrite ?node_8306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8308 (s : N.State) (i : N.Inputs) :
  R.v8308 (state s) (inputs i) = Zmod.unsigned (N.v8308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8308 s i)) at 1.
  unfold R.v8308, N.v8308.
  rewrite ?node_8304.
  rewrite ?node_8307.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8309 (s : N.State) (i : N.Inputs) :
  R.v8309 (state s) (inputs i) = Zmod.unsigned (N.v8309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8309 s i)) at 1.
  unfold R.v8309, N.v8309.
  rewrite ?node_8301.
  rewrite ?node_8308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8310 (s : N.State) (i : N.Inputs) :
  R.v8310 (state s) (inputs i) = Zmod.unsigned (N.v8310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8310 s i)) at 1.
  unfold R.v8310, N.v8310.
  rewrite !state_r708_nr_5F708.
  rewrite !state_r709_nr_5F709.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r708_nr_5F708 s)).
  rewrite ?(bits.mod_to_Z (N.r709_nr_5F709 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8311 (s : N.State) (i : N.Inputs) :
  R.v8311 (state s) (inputs i) = Zmod.unsigned (N.v8311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8311 s i)) at 1.
  unfold R.v8311, N.v8311.
  rewrite ?node_8310.
  rewrite !state_r710_nr_5F710.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r710_nr_5F710 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8312 (s : N.State) (i : N.Inputs) :
  R.v8312 (state s) (inputs i) = Zmod.unsigned (N.v8312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8312 s i)) at 1.
  unfold R.v8312, N.v8312.
  rewrite ?node_8311.
  rewrite !state_r711_nr_5F711.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r711_nr_5F711 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8313 (s : N.State) (i : N.Inputs) :
  R.v8313 (state s) (inputs i) = Zmod.unsigned (N.v8313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8313 s i)) at 1.
  unfold R.v8313, N.v8313.
  rewrite !state_r682_nr_5F682.
  rewrite !state_r683_nr_5F683.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r682_nr_5F682 s)).
  rewrite ?(bits.mod_to_Z (N.r683_nr_5F683 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8314 (s : N.State) (i : N.Inputs) :
  R.v8314 (state s) (inputs i) = Zmod.unsigned (N.v8314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8314 s i)) at 1.
  unfold R.v8314, N.v8314.
  rewrite ?node_8188.
  rewrite !state_r684_nr_5F684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r684_nr_5F684 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8315 (s : N.State) (i : N.Inputs) :
  R.v8315 (state s) (inputs i) = Zmod.unsigned (N.v8315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8315 s i)) at 1.
  unfold R.v8315, N.v8315.
  rewrite ?node_8313.
  rewrite ?node_8314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8316 (s : N.State) (i : N.Inputs) :
  R.v8316 (state s) (inputs i) = Zmod.unsigned (N.v8316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8316 s i)) at 1.
  unfold R.v8316, N.v8316.
  rewrite ?node_8312.
  rewrite ?node_8315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8317 (s : N.State) (i : N.Inputs) :
  R.v8317 (state s) (inputs i) = Zmod.unsigned (N.v8317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8317 s i)) at 1.
  unfold R.v8317, N.v8317.
  rewrite ?node_8309.
  rewrite ?node_8316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8318 (s : N.State) (i : N.Inputs) :
  R.v8318 (state s) (inputs i) = Zmod.unsigned (N.v8318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8318 s i)) at 1.
  unfold R.v8318, N.v8318.
  rewrite !state_r712_nr_5F712.
  rewrite !state_r713_nr_5F713.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r712_nr_5F712 s)).
  rewrite ?(bits.mod_to_Z (N.r713_nr_5F713 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8319 (s : N.State) (i : N.Inputs) :
  R.v8319 (state s) (inputs i) = Zmod.unsigned (N.v8319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8319 s i)) at 1.
  unfold R.v8319, N.v8319.
  rewrite ?node_8318.
  rewrite !state_r714_nr_5F714.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r714_nr_5F714 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8320 (s : N.State) (i : N.Inputs) :
  R.v8320 (state s) (inputs i) = Zmod.unsigned (N.v8320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8320 s i)) at 1.
  unfold R.v8320, N.v8320.
  rewrite ?node_8319.
  rewrite !state_r715_nr_5F715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r715_nr_5F715 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8321 (s : N.State) (i : N.Inputs) :
  R.v8321 (state s) (inputs i) = Zmod.unsigned (N.v8321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8321 s i)) at 1.
  unfold R.v8321, N.v8321.
  rewrite !state_r686_nr_5F686.
  rewrite !state_r687_nr_5F687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r686_nr_5F686 s)).
  rewrite ?(bits.mod_to_Z (N.r687_nr_5F687 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8322 (s : N.State) (i : N.Inputs) :
  R.v8322 (state s) (inputs i) = Zmod.unsigned (N.v8322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8322 s i)) at 1.
  unfold R.v8322, N.v8322.
  rewrite ?node_8196.
  rewrite !state_r688_nr_5F688.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r688_nr_5F688 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8323 (s : N.State) (i : N.Inputs) :
  R.v8323 (state s) (inputs i) = Zmod.unsigned (N.v8323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8323 s i)) at 1.
  unfold R.v8323, N.v8323.
  rewrite ?node_8321.
  rewrite ?node_8322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8324 (s : N.State) (i : N.Inputs) :
  R.v8324 (state s) (inputs i) = Zmod.unsigned (N.v8324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8324 s i)) at 1.
  unfold R.v8324, N.v8324.
  rewrite ?node_8320.
  rewrite ?node_8323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8325 (s : N.State) (i : N.Inputs) :
  R.v8325 (state s) (inputs i) = Zmod.unsigned (N.v8325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8325 s i)) at 1.
  unfold R.v8325, N.v8325.
  rewrite ?node_8317.
  rewrite ?node_8324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8326 (s : N.State) (i : N.Inputs) :
  R.v8326 (state s) (inputs i) = Zmod.unsigned (N.v8326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8326 s i)) at 1.
  unfold R.v8326, N.v8326.
  rewrite ?node_8179.
  rewrite ?node_8186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8327 (s : N.State) (i : N.Inputs) :
  R.v8327 (state s) (inputs i) = Zmod.unsigned (N.v8327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8327 s i)) at 1.
  unfold R.v8327, N.v8327.
  rewrite ?node_8187.
  rewrite ?node_8194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8328 (s : N.State) (i : N.Inputs) :
  R.v8328 (state s) (inputs i) = Zmod.unsigned (N.v8328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8328 s i)) at 1.
  unfold R.v8328, N.v8328.
  rewrite ?node_8326.
  rewrite ?node_8327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8329 (s : N.State) (i : N.Inputs) :
  R.v8329 (state s) (inputs i) = Zmod.unsigned (N.v8329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8329 s i)) at 1.
  unfold R.v8329, N.v8329.
  rewrite ?node_8325.
  rewrite ?node_8328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8330 (s : N.State) (i : N.Inputs) :
  R.v8330 (state s) (inputs i) = Zmod.unsigned (N.v8330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8330 s i)) at 1.
  unfold R.v8330, N.v8330.
  rewrite !state_r716_nr_5F716.
  rewrite !state_r717_nr_5F717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r716_nr_5F716 s)).
  rewrite ?(bits.mod_to_Z (N.r717_nr_5F717 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8331 (s : N.State) (i : N.Inputs) :
  R.v8331 (state s) (inputs i) = Zmod.unsigned (N.v8331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8331 s i)) at 1.
  unfold R.v8331, N.v8331.
  rewrite ?node_8330.
  rewrite !state_r718_nr_5F718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r718_nr_5F718 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8332 (s : N.State) (i : N.Inputs) :
  R.v8332 (state s) (inputs i) = Zmod.unsigned (N.v8332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8332 s i)) at 1.
  unfold R.v8332, N.v8332.
  rewrite ?node_8331.
  rewrite !state_r719_nr_5F719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r719_nr_5F719 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8333 (s : N.State) (i : N.Inputs) :
  R.v8333 (state s) (inputs i) = Zmod.unsigned (N.v8333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8333 s i)) at 1.
  unfold R.v8333, N.v8333.
  rewrite !state_r690_nr_5F690.
  rewrite !state_r691_nr_5F691.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r690_nr_5F690 s)).
  rewrite ?(bits.mod_to_Z (N.r691_nr_5F691 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8334 (s : N.State) (i : N.Inputs) :
  R.v8334 (state s) (inputs i) = Zmod.unsigned (N.v8334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8334 s i)) at 1.
  unfold R.v8334, N.v8334.
  rewrite ?node_8208.
  rewrite !state_r692_nr_5F692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r692_nr_5F692 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8335 (s : N.State) (i : N.Inputs) :
  R.v8335 (state s) (inputs i) = Zmod.unsigned (N.v8335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8335 s i)) at 1.
  unfold R.v8335, N.v8335.
  rewrite ?node_8333.
  rewrite ?node_8334.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8336 (s : N.State) (i : N.Inputs) :
  R.v8336 (state s) (inputs i) = Zmod.unsigned (N.v8336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8336 s i)) at 1.
  unfold R.v8336, N.v8336.
  rewrite ?node_8332.
  rewrite ?node_8335.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8337 (s : N.State) (i : N.Inputs) :
  R.v8337 (state s) (inputs i) = Zmod.unsigned (N.v8337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8337 s i)) at 1.
  unfold R.v8337, N.v8337.
  rewrite !state_r720_nr_5F720.
  rewrite !state_r721_nr_5F721.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r720_nr_5F720 s)).
  rewrite ?(bits.mod_to_Z (N.r721_nr_5F721 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8338 (s : N.State) (i : N.Inputs) :
  R.v8338 (state s) (inputs i) = Zmod.unsigned (N.v8338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8338 s i)) at 1.
  unfold R.v8338, N.v8338.
  rewrite ?node_8337.
  rewrite !state_r722_nr_5F722.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r722_nr_5F722 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8339 (s : N.State) (i : N.Inputs) :
  R.v8339 (state s) (inputs i) = Zmod.unsigned (N.v8339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8339 s i)) at 1.
  unfold R.v8339, N.v8339.
  rewrite ?node_8338.
  rewrite !state_r723_nr_5F723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r723_nr_5F723 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8340 (s : N.State) (i : N.Inputs) :
  R.v8340 (state s) (inputs i) = Zmod.unsigned (N.v8340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8340 s i)) at 1.
  unfold R.v8340, N.v8340.
  rewrite !state_r694_nr_5F694.
  rewrite !state_r695_nr_5F695.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r694_nr_5F694 s)).
  rewrite ?(bits.mod_to_Z (N.r695_nr_5F695 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8341 (s : N.State) (i : N.Inputs) :
  R.v8341 (state s) (inputs i) = Zmod.unsigned (N.v8341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8341 s i)) at 1.
  unfold R.v8341, N.v8341.
  rewrite ?node_8215.
  rewrite !state_r696_nr_5F696.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r696_nr_5F696 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8342 (s : N.State) (i : N.Inputs) :
  R.v8342 (state s) (inputs i) = Zmod.unsigned (N.v8342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8342 s i)) at 1.
  unfold R.v8342, N.v8342.
  rewrite ?node_8340.
  rewrite ?node_8341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8343 (s : N.State) (i : N.Inputs) :
  R.v8343 (state s) (inputs i) = Zmod.unsigned (N.v8343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8343 s i)) at 1.
  unfold R.v8343, N.v8343.
  rewrite ?node_8339.
  rewrite ?node_8342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8344 (s : N.State) (i : N.Inputs) :
  R.v8344 (state s) (inputs i) = Zmod.unsigned (N.v8344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8344 s i)) at 1.
  unfold R.v8344, N.v8344.
  rewrite ?node_8336.
  rewrite ?node_8343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8345 (s : N.State) (i : N.Inputs) :
  R.v8345 (state s) (inputs i) = Zmod.unsigned (N.v8345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8345 s i)) at 1.
  unfold R.v8345, N.v8345.
  rewrite !state_r724_nr_5F724.
  rewrite !state_r725_nr_5F725.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r724_nr_5F724 s)).
  rewrite ?(bits.mod_to_Z (N.r725_nr_5F725 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8346 (s : N.State) (i : N.Inputs) :
  R.v8346 (state s) (inputs i) = Zmod.unsigned (N.v8346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8346 s i)) at 1.
  unfold R.v8346, N.v8346.
  rewrite ?node_8345.
  rewrite !state_r726_nr_5F726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r726_nr_5F726 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8347 (s : N.State) (i : N.Inputs) :
  R.v8347 (state s) (inputs i) = Zmod.unsigned (N.v8347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8347 s i)) at 1.
  unfold R.v8347, N.v8347.
  rewrite ?node_8344.
  rewrite ?node_8346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8348 (s : N.State) (i : N.Inputs) :
  R.v8348 (state s) (inputs i) = Zmod.unsigned (N.v8348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8348 s i)) at 1.
  unfold R.v8348, N.v8348.
  rewrite ?node_8174.
  rewrite !state_r677_nr_5F677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r677_nr_5F677 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8349 (s : N.State) (i : N.Inputs) :
  R.v8349 (state s) (inputs i) = Zmod.unsigned (N.v8349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8349 s i)) at 1.
  unfold R.v8349, N.v8349.
  rewrite ?node_8175.
  rewrite ?node_8178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8350 (s : N.State) (i : N.Inputs) :
  R.v8350 (state s) (inputs i) = Zmod.unsigned (N.v8350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8350 s i)) at 1.
  unfold R.v8350, N.v8350.
  rewrite ?node_8348.
  rewrite ?node_8349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8351 (s : N.State) (i : N.Inputs) :
  R.v8351 (state s) (inputs i) = Zmod.unsigned (N.v8351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8351 s i)) at 1.
  unfold R.v8351, N.v8351.
  rewrite ?node_8347.
  rewrite ?node_8350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8352 (s : N.State) (i : N.Inputs) :
  R.v8352 (state s) (inputs i) = Zmod.unsigned (N.v8352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8352 s i)) at 1.
  unfold R.v8352, N.v8352.
  rewrite ?node_8214.
  rewrite ?node_8221.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8353 (s : N.State) (i : N.Inputs) :
  R.v8353 (state s) (inputs i) = Zmod.unsigned (N.v8353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8353 s i)) at 1.
  unfold R.v8353, N.v8353.
  rewrite ?node_8222.
  rewrite ?node_8223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8354 (s : N.State) (i : N.Inputs) :
  R.v8354 (state s) (inputs i) = Zmod.unsigned (N.v8354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8354 s i)) at 1.
  unfold R.v8354, N.v8354.
  rewrite ?node_8352.
  rewrite ?node_8353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8355 (s : N.State) (i : N.Inputs) :
  R.v8355 (state s) (inputs i) = Zmod.unsigned (N.v8355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8355 s i)) at 1.
  unfold R.v8355, N.v8355.
  rewrite ?node_8351.
  rewrite ?node_8354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8356 (s : N.State) (i : N.Inputs) :
  R.v8356 (state s) (inputs i) = Zmod.unsigned (N.v8356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8356 s i)) at 1.
  unfold R.v8356, N.v8356.
  rewrite ?node_8329.
  rewrite ?node_8355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8357 (s : N.State) (i : N.Inputs) :
  R.v8357 (state s) (inputs i) = Zmod.unsigned (N.v8357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8357 s i)) at 1.
  unfold R.v8357, N.v8357.
  rewrite ?node_8181.
  rewrite !state_r681_nr_5F681.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r681_nr_5F681 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8358 (s : N.State) (i : N.Inputs) :
  R.v8358 (state s) (inputs i) = Zmod.unsigned (N.v8358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8358 s i)) at 1.
  unfold R.v8358, N.v8358.
  rewrite ?node_8182.
  rewrite ?node_8185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8359 (s : N.State) (i : N.Inputs) :
  R.v8359 (state s) (inputs i) = Zmod.unsigned (N.v8359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8359 s i)) at 1.
  unfold R.v8359, N.v8359.
  rewrite ?node_8357.
  rewrite ?node_8358.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8360 (s : N.State) (i : N.Inputs) :
  R.v8360 (state s) (inputs i) = Zmod.unsigned (N.v8360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8360 s i)) at 1.
  unfold R.v8360, N.v8360.
  rewrite ?node_8189.
  rewrite !state_r685_nr_5F685.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r685_nr_5F685 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8361 (s : N.State) (i : N.Inputs) :
  R.v8361 (state s) (inputs i) = Zmod.unsigned (N.v8361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8361 s i)) at 1.
  unfold R.v8361, N.v8361.
  rewrite ?node_8190.
  rewrite ?node_8193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8362 (s : N.State) (i : N.Inputs) :
  R.v8362 (state s) (inputs i) = Zmod.unsigned (N.v8362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8362 s i)) at 1.
  unfold R.v8362, N.v8362.
  rewrite ?node_8360.
  rewrite ?node_8361.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8363 (s : N.State) (i : N.Inputs) :
  R.v8363 (state s) (inputs i) = Zmod.unsigned (N.v8363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8363 s i)) at 1.
  unfold R.v8363, N.v8363.
  rewrite ?node_8359.
  rewrite ?node_8362.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8364 (s : N.State) (i : N.Inputs) :
  R.v8364 (state s) (inputs i) = Zmod.unsigned (N.v8364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8364 s i)) at 1.
  unfold R.v8364, N.v8364.
  rewrite ?node_8197.
  rewrite !state_r689_nr_5F689.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r689_nr_5F689 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8365 (s : N.State) (i : N.Inputs) :
  R.v8365 (state s) (inputs i) = Zmod.unsigned (N.v8365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8365 s i)) at 1.
  unfold R.v8365, N.v8365.
  rewrite ?node_8198.
  rewrite ?node_8201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8366 (s : N.State) (i : N.Inputs) :
  R.v8366 (state s) (inputs i) = Zmod.unsigned (N.v8366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8366 s i)) at 1.
  unfold R.v8366, N.v8366.
  rewrite ?node_8364.
  rewrite ?node_8365.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8367 (s : N.State) (i : N.Inputs) :
  R.v8367 (state s) (inputs i) = Zmod.unsigned (N.v8367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8367 s i)) at 1.
  unfold R.v8367, N.v8367.
  rewrite ?node_8363.
  rewrite ?node_8366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8368 (s : N.State) (i : N.Inputs) :
  R.v8368 (state s) (inputs i) = Zmod.unsigned (N.v8368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8368 s i)) at 1.
  unfold R.v8368, N.v8368.
  rewrite ?node_8209.
  rewrite !state_r693_nr_5F693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r693_nr_5F693 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8369 (s : N.State) (i : N.Inputs) :
  R.v8369 (state s) (inputs i) = Zmod.unsigned (N.v8369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8369 s i)) at 1.
  unfold R.v8369, N.v8369.
  rewrite ?node_8210.
  rewrite ?node_8213.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8370 (s : N.State) (i : N.Inputs) :
  R.v8370 (state s) (inputs i) = Zmod.unsigned (N.v8370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8370 s i)) at 1.
  unfold R.v8370, N.v8370.
  rewrite ?node_8368.
  rewrite ?node_8369.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8371 (s : N.State) (i : N.Inputs) :
  R.v8371 (state s) (inputs i) = Zmod.unsigned (N.v8371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8371 s i)) at 1.
  unfold R.v8371, N.v8371.
  rewrite ?node_8367.
  rewrite ?node_8370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8372 (s : N.State) (i : N.Inputs) :
  R.v8372 (state s) (inputs i) = Zmod.unsigned (N.v8372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8372 s i)) at 1.
  unfold R.v8372, N.v8372.
  rewrite ?node_8236.
  rewrite ?node_8239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8373 (s : N.State) (i : N.Inputs) :
  R.v8373 (state s) (inputs i) = Zmod.unsigned (N.v8373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8373 s i)) at 1.
  unfold R.v8373, N.v8373.
  rewrite ?node_8240.
  rewrite ?node_8243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8374 (s : N.State) (i : N.Inputs) :
  R.v8374 (state s) (inputs i) = Zmod.unsigned (N.v8374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8374 s i)) at 1.
  unfold R.v8374, N.v8374.
  rewrite ?node_8372.
  rewrite ?node_8373.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8375 (s : N.State) (i : N.Inputs) :
  R.v8375 (state s) (inputs i) = Zmod.unsigned (N.v8375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8375 s i)) at 1.
  unfold R.v8375, N.v8375.
  rewrite ?node_8371.
  rewrite ?node_8374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8376 (s : N.State) (i : N.Inputs) :
  R.v8376 (state s) (inputs i) = Zmod.unsigned (N.v8376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8376 s i)) at 1.
  unfold R.v8376, N.v8376.
  rewrite ?node_8356.
  rewrite ?node_8375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8377 (s : N.State) (i : N.Inputs) :
  R.v8377 (state s) (inputs i) = Zmod.unsigned (N.v8377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8377 s i)) at 1.
  unfold R.v8377, N.v8377.
  rewrite ?node_8216.
  rewrite !state_r697_nr_5F697.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r697_nr_5F697 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8378 (s : N.State) (i : N.Inputs) :
  R.v8378 (state s) (inputs i) = Zmod.unsigned (N.v8378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8378 s i)) at 1.
  unfold R.v8378, N.v8378.
  rewrite ?node_8217.
  rewrite ?node_8220.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8379 (s : N.State) (i : N.Inputs) :
  R.v8379 (state s) (inputs i) = Zmod.unsigned (N.v8379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8379 s i)) at 1.
  unfold R.v8379, N.v8379.
  rewrite ?node_8377.
  rewrite ?node_8378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8380 (s : N.State) (i : N.Inputs) :
  R.v8380 (state s) (inputs i) = Zmod.unsigned (N.v8380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8380 s i)) at 1.
  unfold R.v8380, N.v8380.
  rewrite !state_r698_nr_5F698.
  rewrite !state_r699_nr_5F699.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r698_nr_5F698 s)).
  rewrite ?(bits.mod_to_Z (N.r699_nr_5F699 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8381 (s : N.State) (i : N.Inputs) :
  R.v8381 (state s) (inputs i) = Zmod.unsigned (N.v8381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8381 s i)) at 1.
  unfold R.v8381, N.v8381.
  rewrite ?node_8379.
  rewrite ?node_8380.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8382 (s : N.State) (i : N.Inputs) :
  R.v8382 (state s) (inputs i) = Zmod.unsigned (N.v8382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8382 s i)) at 1.
  unfold R.v8382, N.v8382.
  rewrite ?node_8376.
  rewrite ?node_8381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8383 (s : N.State) (i : N.Inputs) :
  R.v8383 (state s) (inputs i) = Zmod.unsigned (N.v8383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8383 s i)) at 1.
  unfold R.v8383, N.v8383.
  rewrite ?node_8207.
  rewrite ?node_8232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8384 (s : N.State) (i : N.Inputs) :
  R.v8384 (state s) (inputs i) = Zmod.unsigned (N.v8384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8384 s i)) at 1.
  unfold R.v8384, N.v8384.
  rewrite ?node_8233.
  rewrite ?node_8252.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8385 (s : N.State) (i : N.Inputs) :
  R.v8385 (state s) (inputs i) = Zmod.unsigned (N.v8385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8385 s i)) at 1.
  unfold R.v8385, N.v8385.
  rewrite ?node_8383.
  rewrite ?node_8384.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8386 (s : N.State) (i : N.Inputs) :
  R.v8386 (state s) (inputs i) = Zmod.unsigned (N.v8386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8386 s i)) at 1.
  unfold R.v8386, N.v8386.
  rewrite ?node_8382.
  rewrite ?node_8385.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8387 (s : N.State) (i : N.Inputs) :
  R.v8387 (state s) (inputs i) = Zmod.unsigned (N.v8387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8387 s i)) at 1.
  unfold R.v8387, N.v8387.
  rewrite ?node_8195.
  rewrite ?node_8202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8388 (s : N.State) (i : N.Inputs) :
  R.v8388 (state s) (inputs i) = Zmod.unsigned (N.v8388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8388 s i)) at 1.
  unfold R.v8388, N.v8388.
  rewrite ?node_8203.
  rewrite ?node_8206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8389 (s : N.State) (i : N.Inputs) :
  R.v8389 (state s) (inputs i) = Zmod.unsigned (N.v8389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8389 s i)) at 1.
  unfold R.v8389, N.v8389.
  rewrite ?node_8387.
  rewrite ?node_8388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8390 (s : N.State) (i : N.Inputs) :
  R.v8390 (state s) (inputs i) = Zmod.unsigned (N.v8390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8390 s i)) at 1.
  unfold R.v8390, N.v8390.
  rewrite ?node_8224.
  rewrite ?node_8227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8391 (s : N.State) (i : N.Inputs) :
  R.v8391 (state s) (inputs i) = Zmod.unsigned (N.v8391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8391 s i)) at 1.
  unfold R.v8391, N.v8391.
  rewrite ?node_8228.
  rewrite ?node_8231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8392 (s : N.State) (i : N.Inputs) :
  R.v8392 (state s) (inputs i) = Zmod.unsigned (N.v8392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8392 s i)) at 1.
  unfold R.v8392, N.v8392.
  rewrite ?node_8390.
  rewrite ?node_8391.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8393 (s : N.State) (i : N.Inputs) :
  R.v8393 (state s) (inputs i) = Zmod.unsigned (N.v8393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8393 s i)) at 1.
  unfold R.v8393, N.v8393.
  rewrite ?node_8389.
  rewrite ?node_8392.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8394 (s : N.State) (i : N.Inputs) :
  R.v8394 (state s) (inputs i) = Zmod.unsigned (N.v8394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8394 s i)) at 1.
  unfold R.v8394, N.v8394.
  rewrite ?node_8244.
  rewrite ?node_8247.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8395 (s : N.State) (i : N.Inputs) :
  R.v8395 (state s) (inputs i) = Zmod.unsigned (N.v8395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8395 s i)) at 1.
  unfold R.v8395, N.v8395.
  rewrite ?node_8248.
  rewrite ?node_8251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8396 (s : N.State) (i : N.Inputs) :
  R.v8396 (state s) (inputs i) = Zmod.unsigned (N.v8396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8396 s i)) at 1.
  unfold R.v8396, N.v8396.
  rewrite ?node_8394.
  rewrite ?node_8395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8397 (s : N.State) (i : N.Inputs) :
  R.v8397 (state s) (inputs i) = Zmod.unsigned (N.v8397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8397 s i)) at 1.
  unfold R.v8397, N.v8397.
  rewrite ?node_8393.
  rewrite ?node_8396.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8398 (s : N.State) (i : N.Inputs) :
  R.v8398 (state s) (inputs i) = Zmod.unsigned (N.v8398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8398 s i)) at 1.
  unfold R.v8398, N.v8398.
  rewrite ?node_8256.
  rewrite ?node_8257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8399 (s : N.State) (i : N.Inputs) :
  R.v8399 (state s) (inputs i) = Zmod.unsigned (N.v8399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8399 s i)) at 1.
  unfold R.v8399, N.v8399.
  rewrite ?node_8397.
  rewrite ?node_8398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8400 (s : N.State) (i : N.Inputs) :
  R.v8400 (state s) (inputs i) = Zmod.unsigned (N.v8400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8400 s i)) at 1.
  unfold R.v8400, N.v8400.
  rewrite ?node_8386.
  rewrite ?node_8399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8401 (s : N.State) (i : N.Inputs) :
  R.v8401 (state s) (inputs i) = Zmod.unsigned (N.v8401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8401 s i)) at 1.
  unfold R.v8401, N.v8401.
  rewrite ?node_8253.
  rewrite ?node_8258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8402 (s : N.State) (i : N.Inputs) :
  R.v8402 (state s) (inputs i) = Zmod.unsigned (N.v8402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8402 s i)) at 1.
  unfold R.v8402, N.v8402.
  rewrite ?node_8259.
  rewrite ?node_8262.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8403 (s : N.State) (i : N.Inputs) :
  R.v8403 (state s) (inputs i) = Zmod.unsigned (N.v8403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8403 s i)) at 1.
  unfold R.v8403, N.v8403.
  rewrite ?node_8401.
  rewrite ?node_8402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8404 (s : N.State) (i : N.Inputs) :
  R.v8404 (state s) (inputs i) = Zmod.unsigned (N.v8404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8404 s i)) at 1.
  unfold R.v8404, N.v8404.
  rewrite ?node_8400.
  rewrite ?node_8403.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8405 (s : N.State) (i : N.Inputs) :
  R.v8405 (state s) (inputs i) = Zmod.unsigned (N.v8405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8405 s i)) at 1.
  unfold R.v8405, N.v8405.
  rewrite ?node_8266.
  rewrite ?node_8269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8406 (s : N.State) (i : N.Inputs) :
  R.v8406 (state s) (inputs i) = Zmod.unsigned (N.v8406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8406 s i)) at 1.
  unfold R.v8406, N.v8406.
  rewrite ?node_8270.
  rewrite ?node_8273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8407 (s : N.State) (i : N.Inputs) :
  R.v8407 (state s) (inputs i) = Zmod.unsigned (N.v8407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8407 s i)) at 1.
  unfold R.v8407, N.v8407.
  rewrite ?node_8405.
  rewrite ?node_8406.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8408 (s : N.State) (i : N.Inputs) :
  R.v8408 (state s) (inputs i) = Zmod.unsigned (N.v8408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8408 s i)) at 1.
  unfold R.v8408, N.v8408.
  rewrite ?node_8404.
  rewrite ?node_8407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8409 (s : N.State) (i : N.Inputs) :
  R.v8409 (state s) (inputs i) = Zmod.unsigned (N.v8409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8409 s i)) at 1.
  unfold R.v8409, N.v8409.
  rewrite ?node_8263.
  rewrite ?node_8274.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8410 (s : N.State) (i : N.Inputs) :
  R.v8410 (state s) (inputs i) = Zmod.unsigned (N.v8410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8410 s i)) at 1.
  unfold R.v8410, N.v8410.
  rewrite ?node_8275.
  rewrite ?node_8278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8411 (s : N.State) (i : N.Inputs) :
  R.v8411 (state s) (inputs i) = Zmod.unsigned (N.v8411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8411 s i)) at 1.
  unfold R.v8411, N.v8411.
  rewrite ?node_8409.
  rewrite ?node_8410.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8412 (s : N.State) (i : N.Inputs) :
  R.v8412 (state s) (inputs i) = Zmod.unsigned (N.v8412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8412 s i)) at 1.
  unfold R.v8412, N.v8412.
  rewrite ?node_8408.
  rewrite ?node_8411.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8413 (s : N.State) (i : N.Inputs) :
  R.v8413 (state s) (inputs i) = Zmod.unsigned (N.v8413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8413 s i)) at 1.
  unfold R.v8413, N.v8413.
  rewrite ?node_8279.
  rewrite ?node_8282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8414 (s : N.State) (i : N.Inputs) :
  R.v8414 (state s) (inputs i) = Zmod.unsigned (N.v8414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8414 s i)) at 1.
  unfold R.v8414, N.v8414.
  rewrite ?node_8283.
  rewrite ?node_8286.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8415 (s : N.State) (i : N.Inputs) :
  R.v8415 (state s) (inputs i) = Zmod.unsigned (N.v8415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8415 s i)) at 1.
  unfold R.v8415, N.v8415.
  rewrite ?node_8413.
  rewrite ?node_8414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8416 (s : N.State) (i : N.Inputs) :
  R.v8416 (state s) (inputs i) = Zmod.unsigned (N.v8416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8416 s i)) at 1.
  unfold R.v8416, N.v8416.
  rewrite ?node_8412.
  rewrite ?node_8415.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8417 (s : N.State) (i : N.Inputs) :
  R.v8417 (state s) (inputs i) = Zmod.unsigned (N.v8417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8417 s i)) at 1.
  unfold R.v8417, N.v8417.
  rewrite ?node_8416.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2373_nr_5F2404.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2373_nr_5F2404 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8418 (s : N.State) (i : N.Inputs) :
  R.v8418 (state s) (inputs i) = Zmod.unsigned (N.v8418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8418 s i)) at 1.
  unfold R.v8418, N.v8418.
  rewrite ?node_8287.
  rewrite ?node_8290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8419 (s : N.State) (i : N.Inputs) :
  R.v8419 (state s) (inputs i) = Zmod.unsigned (N.v8419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8419 s i)) at 1.
  unfold R.v8419, N.v8419.
  rewrite ?node_8418.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2374_nr_5F2405.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2374_nr_5F2405 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8420 (s : N.State) (i : N.Inputs) :
  R.v8420 (state s) (inputs i) = Zmod.unsigned (N.v8420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8420 s i)) at 1.
  unfold R.v8420, N.v8420.
  rewrite !state_r727_nr_5F727.
  rewrite !state_r728_nr_5F728.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r727_nr_5F727 s)).
  rewrite ?(bits.mod_to_Z (N.r728_nr_5F728 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8421 (s : N.State) (i : N.Inputs) :
  R.v8421 (state s) (inputs i) = Zmod.unsigned (N.v8421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8421 s i)) at 1.
  unfold R.v8421, N.v8421.
  rewrite ?node_8420.
  rewrite !state_r729_nr_5F729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r729_nr_5F729 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8422 (s : N.State) (i : N.Inputs) :
  R.v8422 (state s) (inputs i) = Zmod.unsigned (N.v8422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8422 s i)) at 1.
  unfold R.v8422, N.v8422.
  rewrite ?node_8421.
  rewrite !state_r730_nr_5F730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r730_nr_5F730 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8423 (s : N.State) (i : N.Inputs) :
  R.v8423 (state s) (inputs i) = Zmod.unsigned (N.v8423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8423 s i)) at 1.
  unfold R.v8423, N.v8423.
  rewrite !state_r700_nr_5F700.
  rewrite !state_r701_nr_5F701.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r700_nr_5F700 s)).
  rewrite ?(bits.mod_to_Z (N.r701_nr_5F701 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8424 (s : N.State) (i : N.Inputs) :
  R.v8424 (state s) (inputs i) = Zmod.unsigned (N.v8424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8424 s i)) at 1.
  unfold R.v8424, N.v8424.
  rewrite ?node_8295.
  rewrite !state_r702_nr_5F702.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r702_nr_5F702 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8425 (s : N.State) (i : N.Inputs) :
  R.v8425 (state s) (inputs i) = Zmod.unsigned (N.v8425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8425 s i)) at 1.
  unfold R.v8425, N.v8425.
  rewrite ?node_8423.
  rewrite ?node_8424.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8426 (s : N.State) (i : N.Inputs) :
  R.v8426 (state s) (inputs i) = Zmod.unsigned (N.v8426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8426 s i)) at 1.
  unfold R.v8426, N.v8426.
  rewrite ?node_8422.
  rewrite ?node_8425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8427 (s : N.State) (i : N.Inputs) :
  R.v8427 (state s) (inputs i) = Zmod.unsigned (N.v8427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8427 s i)) at 1.
  unfold R.v8427, N.v8427.
  rewrite !state_r731_nr_5F731.
  rewrite !state_r732_nr_5F732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r731_nr_5F731 s)).
  rewrite ?(bits.mod_to_Z (N.r732_nr_5F732 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8428 (s : N.State) (i : N.Inputs) :
  R.v8428 (state s) (inputs i) = Zmod.unsigned (N.v8428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8428 s i)) at 1.
  unfold R.v8428, N.v8428.
  rewrite ?node_8427.
  rewrite !state_r733_nr_5F733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r733_nr_5F733 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8429 (s : N.State) (i : N.Inputs) :
  R.v8429 (state s) (inputs i) = Zmod.unsigned (N.v8429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8429 s i)) at 1.
  unfold R.v8429, N.v8429.
  rewrite ?node_8428.
  rewrite !state_r734_nr_5F734.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r734_nr_5F734 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8430 (s : N.State) (i : N.Inputs) :
  R.v8430 (state s) (inputs i) = Zmod.unsigned (N.v8430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8430 s i)) at 1.
  unfold R.v8430, N.v8430.
  rewrite !state_r704_nr_5F704.
  rewrite !state_r705_nr_5F705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r704_nr_5F704 s)).
  rewrite ?(bits.mod_to_Z (N.r705_nr_5F705 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8431 (s : N.State) (i : N.Inputs) :
  R.v8431 (state s) (inputs i) = Zmod.unsigned (N.v8431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8431 s i)) at 1.
  unfold R.v8431, N.v8431.
  rewrite ?node_8302.
  rewrite !state_r706_nr_5F706.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r706_nr_5F706 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8432 (s : N.State) (i : N.Inputs) :
  R.v8432 (state s) (inputs i) = Zmod.unsigned (N.v8432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8432 s i)) at 1.
  unfold R.v8432, N.v8432.
  rewrite ?node_8430.
  rewrite ?node_8431.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8433 (s : N.State) (i : N.Inputs) :
  R.v8433 (state s) (inputs i) = Zmod.unsigned (N.v8433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8433 s i)) at 1.
  unfold R.v8433, N.v8433.
  rewrite ?node_8429.
  rewrite ?node_8432.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8434 (s : N.State) (i : N.Inputs) :
  R.v8434 (state s) (inputs i) = Zmod.unsigned (N.v8434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8434 s i)) at 1.
  unfold R.v8434, N.v8434.
  rewrite ?node_8426.
  rewrite ?node_8433.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8435 (s : N.State) (i : N.Inputs) :
  R.v8435 (state s) (inputs i) = Zmod.unsigned (N.v8435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8435 s i)) at 1.
  unfold R.v8435, N.v8435.
  rewrite !state_r735_nr_5F735.
  rewrite !state_r736_nr_5F736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r735_nr_5F735 s)).
  rewrite ?(bits.mod_to_Z (N.r736_nr_5F736 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8436 (s : N.State) (i : N.Inputs) :
  R.v8436 (state s) (inputs i) = Zmod.unsigned (N.v8436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8436 s i)) at 1.
  unfold R.v8436, N.v8436.
  rewrite ?node_8435.
  rewrite !state_r737_nr_5F737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r737_nr_5F737 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8437 (s : N.State) (i : N.Inputs) :
  R.v8437 (state s) (inputs i) = Zmod.unsigned (N.v8437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8437 s i)) at 1.
  unfold R.v8437, N.v8437.
  rewrite ?node_8436.
  rewrite !state_r738_nr_5F738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r738_nr_5F738 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8438 (s : N.State) (i : N.Inputs) :
  R.v8438 (state s) (inputs i) = Zmod.unsigned (N.v8438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8438 s i)) at 1.
  unfold R.v8438, N.v8438.
  rewrite !state_r708_nr_5F708.
  rewrite !state_r709_nr_5F709.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r708_nr_5F708 s)).
  rewrite ?(bits.mod_to_Z (N.r709_nr_5F709 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8439 (s : N.State) (i : N.Inputs) :
  R.v8439 (state s) (inputs i) = Zmod.unsigned (N.v8439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8439 s i)) at 1.
  unfold R.v8439, N.v8439.
  rewrite ?node_8310.
  rewrite !state_r710_nr_5F710.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r710_nr_5F710 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8440 (s : N.State) (i : N.Inputs) :
  R.v8440 (state s) (inputs i) = Zmod.unsigned (N.v8440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8440 s i)) at 1.
  unfold R.v8440, N.v8440.
  rewrite ?node_8438.
  rewrite ?node_8439.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8441 (s : N.State) (i : N.Inputs) :
  R.v8441 (state s) (inputs i) = Zmod.unsigned (N.v8441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8441 s i)) at 1.
  unfold R.v8441, N.v8441.
  rewrite ?node_8437.
  rewrite ?node_8440.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8442 (s : N.State) (i : N.Inputs) :
  R.v8442 (state s) (inputs i) = Zmod.unsigned (N.v8442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8442 s i)) at 1.
  unfold R.v8442, N.v8442.
  rewrite ?node_8434.
  rewrite ?node_8441.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8443 (s : N.State) (i : N.Inputs) :
  R.v8443 (state s) (inputs i) = Zmod.unsigned (N.v8443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8443 s i)) at 1.
  unfold R.v8443, N.v8443.
  rewrite !state_r739_nr_5F739.
  rewrite !state_r740_nr_5F740.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r739_nr_5F739 s)).
  rewrite ?(bits.mod_to_Z (N.r740_nr_5F740 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8444 (s : N.State) (i : N.Inputs) :
  R.v8444 (state s) (inputs i) = Zmod.unsigned (N.v8444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8444 s i)) at 1.
  unfold R.v8444, N.v8444.
  rewrite ?node_8443.
  rewrite !state_r741_nr_5F741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r741_nr_5F741 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8445 (s : N.State) (i : N.Inputs) :
  R.v8445 (state s) (inputs i) = Zmod.unsigned (N.v8445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8445 s i)) at 1.
  unfold R.v8445, N.v8445.
  rewrite ?node_8444.
  rewrite !state_r742_nr_5F742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r742_nr_5F742 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8446 (s : N.State) (i : N.Inputs) :
  R.v8446 (state s) (inputs i) = Zmod.unsigned (N.v8446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8446 s i)) at 1.
  unfold R.v8446, N.v8446.
  rewrite !state_r712_nr_5F712.
  rewrite !state_r713_nr_5F713.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r712_nr_5F712 s)).
  rewrite ?(bits.mod_to_Z (N.r713_nr_5F713 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8447 (s : N.State) (i : N.Inputs) :
  R.v8447 (state s) (inputs i) = Zmod.unsigned (N.v8447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8447 s i)) at 1.
  unfold R.v8447, N.v8447.
  rewrite ?node_8318.
  rewrite !state_r714_nr_5F714.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r714_nr_5F714 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8448 (s : N.State) (i : N.Inputs) :
  R.v8448 (state s) (inputs i) = Zmod.unsigned (N.v8448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8448 s i)) at 1.
  unfold R.v8448, N.v8448.
  rewrite ?node_8446.
  rewrite ?node_8447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8449 (s : N.State) (i : N.Inputs) :
  R.v8449 (state s) (inputs i) = Zmod.unsigned (N.v8449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8449 s i)) at 1.
  unfold R.v8449, N.v8449.
  rewrite ?node_8445.
  rewrite ?node_8448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8450 (s : N.State) (i : N.Inputs) :
  R.v8450 (state s) (inputs i) = Zmod.unsigned (N.v8450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8450 s i)) at 1.
  unfold R.v8450, N.v8450.
  rewrite ?node_8442.
  rewrite ?node_8449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8451 (s : N.State) (i : N.Inputs) :
  R.v8451 (state s) (inputs i) = Zmod.unsigned (N.v8451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8451 s i)) at 1.
  unfold R.v8451, N.v8451.
  rewrite ?node_8301.
  rewrite ?node_8308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8452 (s : N.State) (i : N.Inputs) :
  R.v8452 (state s) (inputs i) = Zmod.unsigned (N.v8452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8452 s i)) at 1.
  unfold R.v8452, N.v8452.
  rewrite ?node_8309.
  rewrite ?node_8316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8453 (s : N.State) (i : N.Inputs) :
  R.v8453 (state s) (inputs i) = Zmod.unsigned (N.v8453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8453 s i)) at 1.
  unfold R.v8453, N.v8453.
  rewrite ?node_8451.
  rewrite ?node_8452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8454 (s : N.State) (i : N.Inputs) :
  R.v8454 (state s) (inputs i) = Zmod.unsigned (N.v8454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8454 s i)) at 1.
  unfold R.v8454, N.v8454.
  rewrite ?node_8450.
  rewrite ?node_8453.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8455 (s : N.State) (i : N.Inputs) :
  R.v8455 (state s) (inputs i) = Zmod.unsigned (N.v8455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8455 s i)) at 1.
  unfold R.v8455, N.v8455.
  rewrite !state_r743_nr_5F743.
  rewrite !state_r744_nr_5F744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r743_nr_5F743 s)).
  rewrite ?(bits.mod_to_Z (N.r744_nr_5F744 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8456 (s : N.State) (i : N.Inputs) :
  R.v8456 (state s) (inputs i) = Zmod.unsigned (N.v8456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8456 s i)) at 1.
  unfold R.v8456, N.v8456.
  rewrite ?node_8455.
  rewrite !state_r745_nr_5F745.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r745_nr_5F745 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8457 (s : N.State) (i : N.Inputs) :
  R.v8457 (state s) (inputs i) = Zmod.unsigned (N.v8457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8457 s i)) at 1.
  unfold R.v8457, N.v8457.
  rewrite ?node_8456.
  rewrite !state_r746_nr_5F746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r746_nr_5F746 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8458 (s : N.State) (i : N.Inputs) :
  R.v8458 (state s) (inputs i) = Zmod.unsigned (N.v8458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8458 s i)) at 1.
  unfold R.v8458, N.v8458.
  rewrite !state_r716_nr_5F716.
  rewrite !state_r717_nr_5F717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r716_nr_5F716 s)).
  rewrite ?(bits.mod_to_Z (N.r717_nr_5F717 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8459 (s : N.State) (i : N.Inputs) :
  R.v8459 (state s) (inputs i) = Zmod.unsigned (N.v8459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8459 s i)) at 1.
  unfold R.v8459, N.v8459.
  rewrite ?node_8330.
  rewrite !state_r718_nr_5F718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r718_nr_5F718 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8460 (s : N.State) (i : N.Inputs) :
  R.v8460 (state s) (inputs i) = Zmod.unsigned (N.v8460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8460 s i)) at 1.
  unfold R.v8460, N.v8460.
  rewrite ?node_8458.
  rewrite ?node_8459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8461 (s : N.State) (i : N.Inputs) :
  R.v8461 (state s) (inputs i) = Zmod.unsigned (N.v8461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8461 s i)) at 1.
  unfold R.v8461, N.v8461.
  rewrite ?node_8457.
  rewrite ?node_8460.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8462 (s : N.State) (i : N.Inputs) :
  R.v8462 (state s) (inputs i) = Zmod.unsigned (N.v8462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8462 s i)) at 1.
  unfold R.v8462, N.v8462.
  rewrite !state_r747_nr_5F747.
  rewrite !state_r748_nr_5F748.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r747_nr_5F747 s)).
  rewrite ?(bits.mod_to_Z (N.r748_nr_5F748 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8463 (s : N.State) (i : N.Inputs) :
  R.v8463 (state s) (inputs i) = Zmod.unsigned (N.v8463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8463 s i)) at 1.
  unfold R.v8463, N.v8463.
  rewrite ?node_8462.
  rewrite !state_r749_nr_5F749.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r749_nr_5F749 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8464 (s : N.State) (i : N.Inputs) :
  R.v8464 (state s) (inputs i) = Zmod.unsigned (N.v8464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8464 s i)) at 1.
  unfold R.v8464, N.v8464.
  rewrite ?node_8463.
  rewrite !state_r750_nr_5F750.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r750_nr_5F750 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8465 (s : N.State) (i : N.Inputs) :
  R.v8465 (state s) (inputs i) = Zmod.unsigned (N.v8465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8465 s i)) at 1.
  unfold R.v8465, N.v8465.
  rewrite !state_r720_nr_5F720.
  rewrite !state_r721_nr_5F721.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r720_nr_5F720 s)).
  rewrite ?(bits.mod_to_Z (N.r721_nr_5F721 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8466 (s : N.State) (i : N.Inputs) :
  R.v8466 (state s) (inputs i) = Zmod.unsigned (N.v8466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8466 s i)) at 1.
  unfold R.v8466, N.v8466.
  rewrite ?node_8337.
  rewrite !state_r722_nr_5F722.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r722_nr_5F722 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8467 (s : N.State) (i : N.Inputs) :
  R.v8467 (state s) (inputs i) = Zmod.unsigned (N.v8467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8467 s i)) at 1.
  unfold R.v8467, N.v8467.
  rewrite ?node_8465.
  rewrite ?node_8466.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8468 (s : N.State) (i : N.Inputs) :
  R.v8468 (state s) (inputs i) = Zmod.unsigned (N.v8468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8468 s i)) at 1.
  unfold R.v8468, N.v8468.
  rewrite ?node_8464.
  rewrite ?node_8467.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8469 (s : N.State) (i : N.Inputs) :
  R.v8469 (state s) (inputs i) = Zmod.unsigned (N.v8469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8469 s i)) at 1.
  unfold R.v8469, N.v8469.
  rewrite ?node_8461.
  rewrite ?node_8468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8470 (s : N.State) (i : N.Inputs) :
  R.v8470 (state s) (inputs i) = Zmod.unsigned (N.v8470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8470 s i)) at 1.
  unfold R.v8470, N.v8470.
  rewrite !state_r751_nr_5F751.
  rewrite !state_r752_nr_5F752.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r751_nr_5F751 s)).
  rewrite ?(bits.mod_to_Z (N.r752_nr_5F752 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8471 (s : N.State) (i : N.Inputs) :
  R.v8471 (state s) (inputs i) = Zmod.unsigned (N.v8471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8471 s i)) at 1.
  unfold R.v8471, N.v8471.
  rewrite ?node_8470.
  rewrite !state_r753_nr_5F753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r753_nr_5F753 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8472 (s : N.State) (i : N.Inputs) :
  R.v8472 (state s) (inputs i) = Zmod.unsigned (N.v8472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8472 s i)) at 1.
  unfold R.v8472, N.v8472.
  rewrite ?node_8469.
  rewrite ?node_8471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8473 (s : N.State) (i : N.Inputs) :
  R.v8473 (state s) (inputs i) = Zmod.unsigned (N.v8473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8473 s i)) at 1.
  unfold R.v8473, N.v8473.
  rewrite ?node_8296.
  rewrite !state_r703_nr_5F703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r703_nr_5F703 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8474 (s : N.State) (i : N.Inputs) :
  R.v8474 (state s) (inputs i) = Zmod.unsigned (N.v8474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8474 s i)) at 1.
  unfold R.v8474, N.v8474.
  rewrite ?node_8297.
  rewrite ?node_8300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8475 (s : N.State) (i : N.Inputs) :
  R.v8475 (state s) (inputs i) = Zmod.unsigned (N.v8475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8475 s i)) at 1.
  unfold R.v8475, N.v8475.
  rewrite ?node_8473.
  rewrite ?node_8474.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8476 (s : N.State) (i : N.Inputs) :
  R.v8476 (state s) (inputs i) = Zmod.unsigned (N.v8476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8476 s i)) at 1.
  unfold R.v8476, N.v8476.
  rewrite ?node_8472.
  rewrite ?node_8475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8477 (s : N.State) (i : N.Inputs) :
  R.v8477 (state s) (inputs i) = Zmod.unsigned (N.v8477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8477 s i)) at 1.
  unfold R.v8477, N.v8477.
  rewrite ?node_8336.
  rewrite ?node_8343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8478 (s : N.State) (i : N.Inputs) :
  R.v8478 (state s) (inputs i) = Zmod.unsigned (N.v8478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8478 s i)) at 1.
  unfold R.v8478, N.v8478.
  rewrite ?node_8344.
  rewrite ?node_8346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8479 (s : N.State) (i : N.Inputs) :
  R.v8479 (state s) (inputs i) = Zmod.unsigned (N.v8479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8479 s i)) at 1.
  unfold R.v8479, N.v8479.
  rewrite ?node_8477.
  rewrite ?node_8478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8480 (s : N.State) (i : N.Inputs) :
  R.v8480 (state s) (inputs i) = Zmod.unsigned (N.v8480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8480 s i)) at 1.
  unfold R.v8480, N.v8480.
  rewrite ?node_8476.
  rewrite ?node_8479.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8481 (s : N.State) (i : N.Inputs) :
  R.v8481 (state s) (inputs i) = Zmod.unsigned (N.v8481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8481 s i)) at 1.
  unfold R.v8481, N.v8481.
  rewrite ?node_8454.
  rewrite ?node_8480.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8482 (s : N.State) (i : N.Inputs) :
  R.v8482 (state s) (inputs i) = Zmod.unsigned (N.v8482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8482 s i)) at 1.
  unfold R.v8482, N.v8482.
  rewrite ?node_8303.
  rewrite !state_r707_nr_5F707.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r707_nr_5F707 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8483 (s : N.State) (i : N.Inputs) :
  R.v8483 (state s) (inputs i) = Zmod.unsigned (N.v8483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8483 s i)) at 1.
  unfold R.v8483, N.v8483.
  rewrite ?node_8304.
  rewrite ?node_8307.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8484 (s : N.State) (i : N.Inputs) :
  R.v8484 (state s) (inputs i) = Zmod.unsigned (N.v8484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8484 s i)) at 1.
  unfold R.v8484, N.v8484.
  rewrite ?node_8482.
  rewrite ?node_8483.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8485 (s : N.State) (i : N.Inputs) :
  R.v8485 (state s) (inputs i) = Zmod.unsigned (N.v8485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8485 s i)) at 1.
  unfold R.v8485, N.v8485.
  rewrite ?node_8311.
  rewrite !state_r711_nr_5F711.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r711_nr_5F711 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8486 (s : N.State) (i : N.Inputs) :
  R.v8486 (state s) (inputs i) = Zmod.unsigned (N.v8486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8486 s i)) at 1.
  unfold R.v8486, N.v8486.
  rewrite ?node_8312.
  rewrite ?node_8315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8487 (s : N.State) (i : N.Inputs) :
  R.v8487 (state s) (inputs i) = Zmod.unsigned (N.v8487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8487 s i)) at 1.
  unfold R.v8487, N.v8487.
  rewrite ?node_8485.
  rewrite ?node_8486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8488 (s : N.State) (i : N.Inputs) :
  R.v8488 (state s) (inputs i) = Zmod.unsigned (N.v8488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8488 s i)) at 1.
  unfold R.v8488, N.v8488.
  rewrite ?node_8484.
  rewrite ?node_8487.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8489 (s : N.State) (i : N.Inputs) :
  R.v8489 (state s) (inputs i) = Zmod.unsigned (N.v8489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8489 s i)) at 1.
  unfold R.v8489, N.v8489.
  rewrite ?node_8319.
  rewrite !state_r715_nr_5F715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r715_nr_5F715 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8490 (s : N.State) (i : N.Inputs) :
  R.v8490 (state s) (inputs i) = Zmod.unsigned (N.v8490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8490 s i)) at 1.
  unfold R.v8490, N.v8490.
  rewrite ?node_8320.
  rewrite ?node_8323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8491 (s : N.State) (i : N.Inputs) :
  R.v8491 (state s) (inputs i) = Zmod.unsigned (N.v8491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8491 s i)) at 1.
  unfold R.v8491, N.v8491.
  rewrite ?node_8489.
  rewrite ?node_8490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8492 (s : N.State) (i : N.Inputs) :
  R.v8492 (state s) (inputs i) = Zmod.unsigned (N.v8492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8492 s i)) at 1.
  unfold R.v8492, N.v8492.
  rewrite ?node_8488.
  rewrite ?node_8491.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8493 (s : N.State) (i : N.Inputs) :
  R.v8493 (state s) (inputs i) = Zmod.unsigned (N.v8493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8493 s i)) at 1.
  unfold R.v8493, N.v8493.
  rewrite ?node_8331.
  rewrite !state_r719_nr_5F719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r719_nr_5F719 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8494 (s : N.State) (i : N.Inputs) :
  R.v8494 (state s) (inputs i) = Zmod.unsigned (N.v8494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8494 s i)) at 1.
  unfold R.v8494, N.v8494.
  rewrite ?node_8332.
  rewrite ?node_8335.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8495 (s : N.State) (i : N.Inputs) :
  R.v8495 (state s) (inputs i) = Zmod.unsigned (N.v8495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8495 s i)) at 1.
  unfold R.v8495, N.v8495.
  rewrite ?node_8493.
  rewrite ?node_8494.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8496 (s : N.State) (i : N.Inputs) :
  R.v8496 (state s) (inputs i) = Zmod.unsigned (N.v8496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8496 s i)) at 1.
  unfold R.v8496, N.v8496.
  rewrite ?node_8492.
  rewrite ?node_8495.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8497 (s : N.State) (i : N.Inputs) :
  R.v8497 (state s) (inputs i) = Zmod.unsigned (N.v8497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8497 s i)) at 1.
  unfold R.v8497, N.v8497.
  rewrite ?node_8359.
  rewrite ?node_8362.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8498 (s : N.State) (i : N.Inputs) :
  R.v8498 (state s) (inputs i) = Zmod.unsigned (N.v8498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8498 s i)) at 1.
  unfold R.v8498, N.v8498.
  rewrite ?node_8363.
  rewrite ?node_8366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8499 (s : N.State) (i : N.Inputs) :
  R.v8499 (state s) (inputs i) = Zmod.unsigned (N.v8499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8499 s i)) at 1.
  unfold R.v8499, N.v8499.
  rewrite ?node_8497.
  rewrite ?node_8498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8500 (s : N.State) (i : N.Inputs) :
  R.v8500 (state s) (inputs i) = Zmod.unsigned (N.v8500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8500 s i)) at 1.
  unfold R.v8500, N.v8500.
  rewrite ?node_8496.
  rewrite ?node_8499.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8501 (s : N.State) (i : N.Inputs) :
  R.v8501 (state s) (inputs i) = Zmod.unsigned (N.v8501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8501 s i)) at 1.
  unfold R.v8501, N.v8501.
  rewrite ?node_8481.
  rewrite ?node_8500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8502 (s : N.State) (i : N.Inputs) :
  R.v8502 (state s) (inputs i) = Zmod.unsigned (N.v8502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8502 s i)) at 1.
  unfold R.v8502, N.v8502.
  rewrite ?node_8338.
  rewrite !state_r723_nr_5F723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r723_nr_5F723 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8503 (s : N.State) (i : N.Inputs) :
  R.v8503 (state s) (inputs i) = Zmod.unsigned (N.v8503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8503 s i)) at 1.
  unfold R.v8503, N.v8503.
  rewrite ?node_8339.
  rewrite ?node_8342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8504 (s : N.State) (i : N.Inputs) :
  R.v8504 (state s) (inputs i) = Zmod.unsigned (N.v8504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8504 s i)) at 1.
  unfold R.v8504, N.v8504.
  rewrite ?node_8502.
  rewrite ?node_8503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8505 (s : N.State) (i : N.Inputs) :
  R.v8505 (state s) (inputs i) = Zmod.unsigned (N.v8505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8505 s i)) at 1.
  unfold R.v8505, N.v8505.
  rewrite !state_r724_nr_5F724.
  rewrite !state_r725_nr_5F725.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r724_nr_5F724 s)).
  rewrite ?(bits.mod_to_Z (N.r725_nr_5F725 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8506 (s : N.State) (i : N.Inputs) :
  R.v8506 (state s) (inputs i) = Zmod.unsigned (N.v8506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8506 s i)) at 1.
  unfold R.v8506, N.v8506.
  rewrite ?node_8345.
  rewrite !state_r726_nr_5F726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r726_nr_5F726 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8507 (s : N.State) (i : N.Inputs) :
  R.v8507 (state s) (inputs i) = Zmod.unsigned (N.v8507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8507 s i)) at 1.
  unfold R.v8507, N.v8507.
  rewrite ?node_8505.
  rewrite ?node_8506.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8508 (s : N.State) (i : N.Inputs) :
  R.v8508 (state s) (inputs i) = Zmod.unsigned (N.v8508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8508 s i)) at 1.
  unfold R.v8508, N.v8508.
  rewrite ?node_8504.
  rewrite ?node_8507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8509 (s : N.State) (i : N.Inputs) :
  R.v8509 (state s) (inputs i) = Zmod.unsigned (N.v8509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8509 s i)) at 1.
  unfold R.v8509, N.v8509.
  rewrite ?node_8501.
  rewrite ?node_8508.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8510 (s : N.State) (i : N.Inputs) :
  R.v8510 (state s) (inputs i) = Zmod.unsigned (N.v8510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8510 s i)) at 1.
  unfold R.v8510, N.v8510.
  rewrite ?node_8329.
  rewrite ?node_8355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8511 (s : N.State) (i : N.Inputs) :
  R.v8511 (state s) (inputs i) = Zmod.unsigned (N.v8511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8511 s i)) at 1.
  unfold R.v8511, N.v8511.
  rewrite ?node_8356.
  rewrite ?node_8375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8512 (s : N.State) (i : N.Inputs) :
  R.v8512 (state s) (inputs i) = Zmod.unsigned (N.v8512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8512 s i)) at 1.
  unfold R.v8512, N.v8512.
  rewrite ?node_8510.
  rewrite ?node_8511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8513 (s : N.State) (i : N.Inputs) :
  R.v8513 (state s) (inputs i) = Zmod.unsigned (N.v8513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8513 s i)) at 1.
  unfold R.v8513, N.v8513.
  rewrite ?node_8509.
  rewrite ?node_8512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8514 (s : N.State) (i : N.Inputs) :
  R.v8514 (state s) (inputs i) = Zmod.unsigned (N.v8514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8514 s i)) at 1.
  unfold R.v8514, N.v8514.
  rewrite ?node_8317.
  rewrite ?node_8324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8515 (s : N.State) (i : N.Inputs) :
  R.v8515 (state s) (inputs i) = Zmod.unsigned (N.v8515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8515 s i)) at 1.
  unfold R.v8515, N.v8515.
  rewrite ?node_8325.
  rewrite ?node_8328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8516 (s : N.State) (i : N.Inputs) :
  R.v8516 (state s) (inputs i) = Zmod.unsigned (N.v8516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8516 s i)) at 1.
  unfold R.v8516, N.v8516.
  rewrite ?node_8514.
  rewrite ?node_8515.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8517 (s : N.State) (i : N.Inputs) :
  R.v8517 (state s) (inputs i) = Zmod.unsigned (N.v8517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8517 s i)) at 1.
  unfold R.v8517, N.v8517.
  rewrite ?node_8347.
  rewrite ?node_8350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8518 (s : N.State) (i : N.Inputs) :
  R.v8518 (state s) (inputs i) = Zmod.unsigned (N.v8518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8518 s i)) at 1.
  unfold R.v8518, N.v8518.
  rewrite ?node_8351.
  rewrite ?node_8354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8519 (s : N.State) (i : N.Inputs) :
  R.v8519 (state s) (inputs i) = Zmod.unsigned (N.v8519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8519 s i)) at 1.
  unfold R.v8519, N.v8519.
  rewrite ?node_8517.
  rewrite ?node_8518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8520 (s : N.State) (i : N.Inputs) :
  R.v8520 (state s) (inputs i) = Zmod.unsigned (N.v8520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8520 s i)) at 1.
  unfold R.v8520, N.v8520.
  rewrite ?node_8516.
  rewrite ?node_8519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8521 (s : N.State) (i : N.Inputs) :
  R.v8521 (state s) (inputs i) = Zmod.unsigned (N.v8521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8521 s i)) at 1.
  unfold R.v8521, N.v8521.
  rewrite ?node_8367.
  rewrite ?node_8370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8522 (s : N.State) (i : N.Inputs) :
  R.v8522 (state s) (inputs i) = Zmod.unsigned (N.v8522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8522 s i)) at 1.
  unfold R.v8522, N.v8522.
  rewrite ?node_8371.
  rewrite ?node_8374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8523 (s : N.State) (i : N.Inputs) :
  R.v8523 (state s) (inputs i) = Zmod.unsigned (N.v8523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8523 s i)) at 1.
  unfold R.v8523, N.v8523.
  rewrite ?node_8521.
  rewrite ?node_8522.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8524 (s : N.State) (i : N.Inputs) :
  R.v8524 (state s) (inputs i) = Zmod.unsigned (N.v8524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8524 s i)) at 1.
  unfold R.v8524, N.v8524.
  rewrite ?node_8520.
  rewrite ?node_8523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8525 (s : N.State) (i : N.Inputs) :
  R.v8525 (state s) (inputs i) = Zmod.unsigned (N.v8525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8525 s i)) at 1.
  unfold R.v8525, N.v8525.
  rewrite ?node_8379.
  rewrite ?node_8380.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8526 (s : N.State) (i : N.Inputs) :
  R.v8526 (state s) (inputs i) = Zmod.unsigned (N.v8526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8526 s i)) at 1.
  unfold R.v8526, N.v8526.
  rewrite ?node_8524.
  rewrite ?node_8525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8527 (s : N.State) (i : N.Inputs) :
  R.v8527 (state s) (inputs i) = Zmod.unsigned (N.v8527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8527 s i)) at 1.
  unfold R.v8527, N.v8527.
  rewrite ?node_8389.
  rewrite ?node_8392.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8528 (s : N.State) (i : N.Inputs) :
  R.v8528 (state s) (inputs i) = Zmod.unsigned (N.v8528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8528 s i)) at 1.
  unfold R.v8528, N.v8528.
  rewrite ?node_8393.
  rewrite ?node_8396.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8529 (s : N.State) (i : N.Inputs) :
  R.v8529 (state s) (inputs i) = Zmod.unsigned (N.v8529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8529 s i)) at 1.
  unfold R.v8529, N.v8529.
  rewrite ?node_8527.
  rewrite ?node_8528.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8530 (s : N.State) (i : N.Inputs) :
  R.v8530 (state s) (inputs i) = Zmod.unsigned (N.v8530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8530 s i)) at 1.
  unfold R.v8530, N.v8530.
  rewrite ?node_8526.
  rewrite ?node_8529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8531 (s : N.State) (i : N.Inputs) :
  R.v8531 (state s) (inputs i) = Zmod.unsigned (N.v8531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8531 s i)) at 1.
  unfold R.v8531, N.v8531.
  rewrite ?node_8513.
  rewrite ?node_8530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8532 (s : N.State) (i : N.Inputs) :
  R.v8532 (state s) (inputs i) = Zmod.unsigned (N.v8532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8532 s i)) at 1.
  unfold R.v8532, N.v8532.
  rewrite ?node_8376.
  rewrite ?node_8381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8533 (s : N.State) (i : N.Inputs) :
  R.v8533 (state s) (inputs i) = Zmod.unsigned (N.v8533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8533 s i)) at 1.
  unfold R.v8533, N.v8533.
  rewrite ?node_8382.
  rewrite ?node_8385.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8534 (s : N.State) (i : N.Inputs) :
  R.v8534 (state s) (inputs i) = Zmod.unsigned (N.v8534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8534 s i)) at 1.
  unfold R.v8534, N.v8534.
  rewrite ?node_8532.
  rewrite ?node_8533.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8535 (s : N.State) (i : N.Inputs) :
  R.v8535 (state s) (inputs i) = Zmod.unsigned (N.v8535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8535 s i)) at 1.
  unfold R.v8535, N.v8535.
  rewrite ?node_8531.
  rewrite ?node_8534.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8536 (s : N.State) (i : N.Inputs) :
  R.v8536 (state s) (inputs i) = Zmod.unsigned (N.v8536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8536 s i)) at 1.
  unfold R.v8536, N.v8536.
  rewrite ?node_8397.
  rewrite ?node_8398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8537 (s : N.State) (i : N.Inputs) :
  R.v8537 (state s) (inputs i) = Zmod.unsigned (N.v8537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8537 s i)) at 1.
  unfold R.v8537, N.v8537.
  rewrite ?node_8535.
  rewrite ?node_8536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8538 (s : N.State) (i : N.Inputs) :
  R.v8538 (state s) (inputs i) = Zmod.unsigned (N.v8538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8538 s i)) at 1.
  unfold R.v8538, N.v8538.
  rewrite ?node_8386.
  rewrite ?node_8399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8539 (s : N.State) (i : N.Inputs) :
  R.v8539 (state s) (inputs i) = Zmod.unsigned (N.v8539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8539 s i)) at 1.
  unfold R.v8539, N.v8539.
  rewrite ?node_8400.
  rewrite ?node_8403.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8540 (s : N.State) (i : N.Inputs) :
  R.v8540 (state s) (inputs i) = Zmod.unsigned (N.v8540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8540 s i)) at 1.
  unfold R.v8540, N.v8540.
  rewrite ?node_8538.
  rewrite ?node_8539.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8541 (s : N.State) (i : N.Inputs) :
  R.v8541 (state s) (inputs i) = Zmod.unsigned (N.v8541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8541 s i)) at 1.
  unfold R.v8541, N.v8541.
  rewrite ?node_8537.
  rewrite ?node_8540.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8542 (s : N.State) (i : N.Inputs) :
  R.v8542 (state s) (inputs i) = Zmod.unsigned (N.v8542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8542 s i)) at 1.
  unfold R.v8542, N.v8542.
  rewrite ?node_8404.
  rewrite ?node_8407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8543 (s : N.State) (i : N.Inputs) :
  R.v8543 (state s) (inputs i) = Zmod.unsigned (N.v8543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8543 s i)) at 1.
  unfold R.v8543, N.v8543.
  rewrite ?node_8408.
  rewrite ?node_8411.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8544 (s : N.State) (i : N.Inputs) :
  R.v8544 (state s) (inputs i) = Zmod.unsigned (N.v8544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8544 s i)) at 1.
  unfold R.v8544, N.v8544.
  rewrite ?node_8542.
  rewrite ?node_8543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8545 (s : N.State) (i : N.Inputs) :
  R.v8545 (state s) (inputs i) = Zmod.unsigned (N.v8545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8545 s i)) at 1.
  unfold R.v8545, N.v8545.
  rewrite ?node_8541.
  rewrite ?node_8544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8546 (s : N.State) (i : N.Inputs) :
  R.v8546 (state s) (inputs i) = Zmod.unsigned (N.v8546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8546 s i)) at 1.
  unfold R.v8546, N.v8546.
  rewrite ?node_8545.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2375_nr_5F2406.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2375_nr_5F2406 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8547 (s : N.State) (i : N.Inputs) :
  R.v8547 (state s) (inputs i) = Zmod.unsigned (N.v8547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8547 s i)) at 1.
  unfold R.v8547, N.v8547.
  rewrite ?node_8412.
  rewrite ?node_8415.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8548 (s : N.State) (i : N.Inputs) :
  R.v8548 (state s) (inputs i) = Zmod.unsigned (N.v8548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8548 s i)) at 1.
  unfold R.v8548, N.v8548.
  rewrite ?node_8547.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2376_nr_5F2407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2376_nr_5F2407 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8549 (s : N.State) (i : N.Inputs) :
  R.v8549 (state s) (inputs i) = Zmod.unsigned (N.v8549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8549 s i)) at 1.
  unfold R.v8549, N.v8549.
  rewrite !state_r754_nr_5F754.
  rewrite !state_r755_nr_5F755.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r754_nr_5F754 s)).
  rewrite ?(bits.mod_to_Z (N.r755_nr_5F755 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8550 (s : N.State) (i : N.Inputs) :
  R.v8550 (state s) (inputs i) = Zmod.unsigned (N.v8550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8550 s i)) at 1.
  unfold R.v8550, N.v8550.
  rewrite ?node_8549.
  rewrite !state_r756_nr_5F756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r756_nr_5F756 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8551 (s : N.State) (i : N.Inputs) :
  R.v8551 (state s) (inputs i) = Zmod.unsigned (N.v8551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8551 s i)) at 1.
  unfold R.v8551, N.v8551.
  rewrite ?node_8550.
  rewrite !state_r757_nr_5F757.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r757_nr_5F757 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8552 (s : N.State) (i : N.Inputs) :
  R.v8552 (state s) (inputs i) = Zmod.unsigned (N.v8552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8552 s i)) at 1.
  unfold R.v8552, N.v8552.
  rewrite !state_r727_nr_5F727.
  rewrite !state_r728_nr_5F728.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r727_nr_5F727 s)).
  rewrite ?(bits.mod_to_Z (N.r728_nr_5F728 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8553 (s : N.State) (i : N.Inputs) :
  R.v8553 (state s) (inputs i) = Zmod.unsigned (N.v8553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8553 s i)) at 1.
  unfold R.v8553, N.v8553.
  rewrite ?node_8420.
  rewrite !state_r729_nr_5F729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r729_nr_5F729 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8554 (s : N.State) (i : N.Inputs) :
  R.v8554 (state s) (inputs i) = Zmod.unsigned (N.v8554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8554 s i)) at 1.
  unfold R.v8554, N.v8554.
  rewrite ?node_8552.
  rewrite ?node_8553.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8555 (s : N.State) (i : N.Inputs) :
  R.v8555 (state s) (inputs i) = Zmod.unsigned (N.v8555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8555 s i)) at 1.
  unfold R.v8555, N.v8555.
  rewrite ?node_8551.
  rewrite ?node_8554.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8556 (s : N.State) (i : N.Inputs) :
  R.v8556 (state s) (inputs i) = Zmod.unsigned (N.v8556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8556 s i)) at 1.
  unfold R.v8556, N.v8556.
  rewrite !state_r758_nr_5F758.
  rewrite !state_r759_nr_5F759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r758_nr_5F758 s)).
  rewrite ?(bits.mod_to_Z (N.r759_nr_5F759 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8557 (s : N.State) (i : N.Inputs) :
  R.v8557 (state s) (inputs i) = Zmod.unsigned (N.v8557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8557 s i)) at 1.
  unfold R.v8557, N.v8557.
  rewrite ?node_8556.
  rewrite !state_r760_nr_5F760.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r760_nr_5F760 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8558 (s : N.State) (i : N.Inputs) :
  R.v8558 (state s) (inputs i) = Zmod.unsigned (N.v8558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8558 s i)) at 1.
  unfold R.v8558, N.v8558.
  rewrite ?node_8557.
  rewrite !state_r761_nr_5F761.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r761_nr_5F761 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8559 (s : N.State) (i : N.Inputs) :
  R.v8559 (state s) (inputs i) = Zmod.unsigned (N.v8559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8559 s i)) at 1.
  unfold R.v8559, N.v8559.
  rewrite !state_r731_nr_5F731.
  rewrite !state_r732_nr_5F732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r731_nr_5F731 s)).
  rewrite ?(bits.mod_to_Z (N.r732_nr_5F732 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8560 (s : N.State) (i : N.Inputs) :
  R.v8560 (state s) (inputs i) = Zmod.unsigned (N.v8560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8560 s i)) at 1.
  unfold R.v8560, N.v8560.
  rewrite ?node_8427.
  rewrite !state_r733_nr_5F733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r733_nr_5F733 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8561 (s : N.State) (i : N.Inputs) :
  R.v8561 (state s) (inputs i) = Zmod.unsigned (N.v8561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8561 s i)) at 1.
  unfold R.v8561, N.v8561.
  rewrite ?node_8559.
  rewrite ?node_8560.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8562 (s : N.State) (i : N.Inputs) :
  R.v8562 (state s) (inputs i) = Zmod.unsigned (N.v8562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8562 s i)) at 1.
  unfold R.v8562, N.v8562.
  rewrite ?node_8558.
  rewrite ?node_8561.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8563 (s : N.State) (i : N.Inputs) :
  R.v8563 (state s) (inputs i) = Zmod.unsigned (N.v8563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8563 s i)) at 1.
  unfold R.v8563, N.v8563.
  rewrite ?node_8555.
  rewrite ?node_8562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8564 (s : N.State) (i : N.Inputs) :
  R.v8564 (state s) (inputs i) = Zmod.unsigned (N.v8564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8564 s i)) at 1.
  unfold R.v8564, N.v8564.
  rewrite !state_r762_nr_5F762.
  rewrite !state_r763_nr_5F763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r762_nr_5F762 s)).
  rewrite ?(bits.mod_to_Z (N.r763_nr_5F763 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8565 (s : N.State) (i : N.Inputs) :
  R.v8565 (state s) (inputs i) = Zmod.unsigned (N.v8565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8565 s i)) at 1.
  unfold R.v8565, N.v8565.
  rewrite ?node_8564.
  rewrite !state_r764_nr_5F764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r764_nr_5F764 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8566 (s : N.State) (i : N.Inputs) :
  R.v8566 (state s) (inputs i) = Zmod.unsigned (N.v8566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8566 s i)) at 1.
  unfold R.v8566, N.v8566.
  rewrite ?node_8565.
  rewrite !state_r765_nr_5F765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r765_nr_5F765 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8567 (s : N.State) (i : N.Inputs) :
  R.v8567 (state s) (inputs i) = Zmod.unsigned (N.v8567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8567 s i)) at 1.
  unfold R.v8567, N.v8567.
  rewrite !state_r735_nr_5F735.
  rewrite !state_r736_nr_5F736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r735_nr_5F735 s)).
  rewrite ?(bits.mod_to_Z (N.r736_nr_5F736 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8568 (s : N.State) (i : N.Inputs) :
  R.v8568 (state s) (inputs i) = Zmod.unsigned (N.v8568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8568 s i)) at 1.
  unfold R.v8568, N.v8568.
  rewrite ?node_8435.
  rewrite !state_r737_nr_5F737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r737_nr_5F737 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8569 (s : N.State) (i : N.Inputs) :
  R.v8569 (state s) (inputs i) = Zmod.unsigned (N.v8569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8569 s i)) at 1.
  unfold R.v8569, N.v8569.
  rewrite ?node_8567.
  rewrite ?node_8568.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8570 (s : N.State) (i : N.Inputs) :
  R.v8570 (state s) (inputs i) = Zmod.unsigned (N.v8570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8570 s i)) at 1.
  unfold R.v8570, N.v8570.
  rewrite ?node_8566.
  rewrite ?node_8569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8571 (s : N.State) (i : N.Inputs) :
  R.v8571 (state s) (inputs i) = Zmod.unsigned (N.v8571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8571 s i)) at 1.
  unfold R.v8571, N.v8571.
  rewrite ?node_8563.
  rewrite ?node_8570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8572 (s : N.State) (i : N.Inputs) :
  R.v8572 (state s) (inputs i) = Zmod.unsigned (N.v8572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8572 s i)) at 1.
  unfold R.v8572, N.v8572.
  rewrite !state_r766_nr_5F766.
  rewrite !state_r767_nr_5F767.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r766_nr_5F766 s)).
  rewrite ?(bits.mod_to_Z (N.r767_nr_5F767 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8573 (s : N.State) (i : N.Inputs) :
  R.v8573 (state s) (inputs i) = Zmod.unsigned (N.v8573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8573 s i)) at 1.
  unfold R.v8573, N.v8573.
  rewrite ?node_8572.
  rewrite !state_r768_nr_5F768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r768_nr_5F768 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8574 (s : N.State) (i : N.Inputs) :
  R.v8574 (state s) (inputs i) = Zmod.unsigned (N.v8574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8574 s i)) at 1.
  unfold R.v8574, N.v8574.
  rewrite ?node_8573.
  rewrite !state_r769_nr_5F769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r769_nr_5F769 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8575 (s : N.State) (i : N.Inputs) :
  R.v8575 (state s) (inputs i) = Zmod.unsigned (N.v8575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8575 s i)) at 1.
  unfold R.v8575, N.v8575.
  rewrite !state_r739_nr_5F739.
  rewrite !state_r740_nr_5F740.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r739_nr_5F739 s)).
  rewrite ?(bits.mod_to_Z (N.r740_nr_5F740 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8576 (s : N.State) (i : N.Inputs) :
  R.v8576 (state s) (inputs i) = Zmod.unsigned (N.v8576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8576 s i)) at 1.
  unfold R.v8576, N.v8576.
  rewrite ?node_8443.
  rewrite !state_r741_nr_5F741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r741_nr_5F741 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8577 (s : N.State) (i : N.Inputs) :
  R.v8577 (state s) (inputs i) = Zmod.unsigned (N.v8577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8577 s i)) at 1.
  unfold R.v8577, N.v8577.
  rewrite ?node_8575.
  rewrite ?node_8576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8578 (s : N.State) (i : N.Inputs) :
  R.v8578 (state s) (inputs i) = Zmod.unsigned (N.v8578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8578 s i)) at 1.
  unfold R.v8578, N.v8578.
  rewrite ?node_8574.
  rewrite ?node_8577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8579 (s : N.State) (i : N.Inputs) :
  R.v8579 (state s) (inputs i) = Zmod.unsigned (N.v8579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8579 s i)) at 1.
  unfold R.v8579, N.v8579.
  rewrite ?node_8571.
  rewrite ?node_8578.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8580 (s : N.State) (i : N.Inputs) :
  R.v8580 (state s) (inputs i) = Zmod.unsigned (N.v8580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8580 s i)) at 1.
  unfold R.v8580, N.v8580.
  rewrite ?node_8426.
  rewrite ?node_8433.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8581 (s : N.State) (i : N.Inputs) :
  R.v8581 (state s) (inputs i) = Zmod.unsigned (N.v8581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8581 s i)) at 1.
  unfold R.v8581, N.v8581.
  rewrite ?node_8434.
  rewrite ?node_8441.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8582 (s : N.State) (i : N.Inputs) :
  R.v8582 (state s) (inputs i) = Zmod.unsigned (N.v8582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8582 s i)) at 1.
  unfold R.v8582, N.v8582.
  rewrite ?node_8580.
  rewrite ?node_8581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8583 (s : N.State) (i : N.Inputs) :
  R.v8583 (state s) (inputs i) = Zmod.unsigned (N.v8583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8583 s i)) at 1.
  unfold R.v8583, N.v8583.
  rewrite ?node_8579.
  rewrite ?node_8582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8584 (s : N.State) (i : N.Inputs) :
  R.v8584 (state s) (inputs i) = Zmod.unsigned (N.v8584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8584 s i)) at 1.
  unfold R.v8584, N.v8584.
  rewrite !state_r770_nr_5F770.
  rewrite !state_r771_nr_5F771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r770_nr_5F770 s)).
  rewrite ?(bits.mod_to_Z (N.r771_nr_5F771 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8585 (s : N.State) (i : N.Inputs) :
  R.v8585 (state s) (inputs i) = Zmod.unsigned (N.v8585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8585 s i)) at 1.
  unfold R.v8585, N.v8585.
  rewrite ?node_8584.
  rewrite !state_r772_nr_5F772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r772_nr_5F772 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8586 (s : N.State) (i : N.Inputs) :
  R.v8586 (state s) (inputs i) = Zmod.unsigned (N.v8586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8586 s i)) at 1.
  unfold R.v8586, N.v8586.
  rewrite ?node_8585.
  rewrite !state_r773_nr_5F773.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r773_nr_5F773 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8587 (s : N.State) (i : N.Inputs) :
  R.v8587 (state s) (inputs i) = Zmod.unsigned (N.v8587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8587 s i)) at 1.
  unfold R.v8587, N.v8587.
  rewrite !state_r743_nr_5F743.
  rewrite !state_r744_nr_5F744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r743_nr_5F743 s)).
  rewrite ?(bits.mod_to_Z (N.r744_nr_5F744 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8588 (s : N.State) (i : N.Inputs) :
  R.v8588 (state s) (inputs i) = Zmod.unsigned (N.v8588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8588 s i)) at 1.
  unfold R.v8588, N.v8588.
  rewrite ?node_8455.
  rewrite !state_r745_nr_5F745.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r745_nr_5F745 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8589 (s : N.State) (i : N.Inputs) :
  R.v8589 (state s) (inputs i) = Zmod.unsigned (N.v8589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8589 s i)) at 1.
  unfold R.v8589, N.v8589.
  rewrite ?node_8587.
  rewrite ?node_8588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8590 (s : N.State) (i : N.Inputs) :
  R.v8590 (state s) (inputs i) = Zmod.unsigned (N.v8590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8590 s i)) at 1.
  unfold R.v8590, N.v8590.
  rewrite ?node_8586.
  rewrite ?node_8589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8591 (s : N.State) (i : N.Inputs) :
  R.v8591 (state s) (inputs i) = Zmod.unsigned (N.v8591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8591 s i)) at 1.
  unfold R.v8591, N.v8591.
  rewrite !state_r774_nr_5F774.
  rewrite !state_r775_nr_5F775.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r774_nr_5F774 s)).
  rewrite ?(bits.mod_to_Z (N.r775_nr_5F775 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8592 (s : N.State) (i : N.Inputs) :
  R.v8592 (state s) (inputs i) = Zmod.unsigned (N.v8592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8592 s i)) at 1.
  unfold R.v8592, N.v8592.
  rewrite ?node_8591.
  rewrite !state_r776_nr_5F776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r776_nr_5F776 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8593 (s : N.State) (i : N.Inputs) :
  R.v8593 (state s) (inputs i) = Zmod.unsigned (N.v8593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8593 s i)) at 1.
  unfold R.v8593, N.v8593.
  rewrite ?node_8592.
  rewrite !state_r777_nr_5F777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r777_nr_5F777 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8594 (s : N.State) (i : N.Inputs) :
  R.v8594 (state s) (inputs i) = Zmod.unsigned (N.v8594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8594 s i)) at 1.
  unfold R.v8594, N.v8594.
  rewrite !state_r747_nr_5F747.
  rewrite !state_r748_nr_5F748.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r747_nr_5F747 s)).
  rewrite ?(bits.mod_to_Z (N.r748_nr_5F748 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8595 (s : N.State) (i : N.Inputs) :
  R.v8595 (state s) (inputs i) = Zmod.unsigned (N.v8595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8595 s i)) at 1.
  unfold R.v8595, N.v8595.
  rewrite ?node_8462.
  rewrite !state_r749_nr_5F749.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r749_nr_5F749 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8596 (s : N.State) (i : N.Inputs) :
  R.v8596 (state s) (inputs i) = Zmod.unsigned (N.v8596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8596 s i)) at 1.
  unfold R.v8596, N.v8596.
  rewrite ?node_8594.
  rewrite ?node_8595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8597 (s : N.State) (i : N.Inputs) :
  R.v8597 (state s) (inputs i) = Zmod.unsigned (N.v8597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8597 s i)) at 1.
  unfold R.v8597, N.v8597.
  rewrite ?node_8593.
  rewrite ?node_8596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8598 (s : N.State) (i : N.Inputs) :
  R.v8598 (state s) (inputs i) = Zmod.unsigned (N.v8598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8598 s i)) at 1.
  unfold R.v8598, N.v8598.
  rewrite ?node_8590.
  rewrite ?node_8597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8599 (s : N.State) (i : N.Inputs) :
  R.v8599 (state s) (inputs i) = Zmod.unsigned (N.v8599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8599 s i)) at 1.
  unfold R.v8599, N.v8599.
  rewrite !state_r778_nr_5F778.
  rewrite !state_r779_nr_5F779.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r778_nr_5F778 s)).
  rewrite ?(bits.mod_to_Z (N.r779_nr_5F779 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8600 (s : N.State) (i : N.Inputs) :
  R.v8600 (state s) (inputs i) = Zmod.unsigned (N.v8600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8600 s i)) at 1.
  unfold R.v8600, N.v8600.
  rewrite ?node_8599.
  rewrite !state_r780_nr_5F780.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r780_nr_5F780 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8601 (s : N.State) (i : N.Inputs) :
  R.v8601 (state s) (inputs i) = Zmod.unsigned (N.v8601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8601 s i)) at 1.
  unfold R.v8601, N.v8601.
  rewrite ?node_8600.
  rewrite !state_r781_nr_5F781.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r781_nr_5F781 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8602 (s : N.State) (i : N.Inputs) :
  R.v8602 (state s) (inputs i) = Zmod.unsigned (N.v8602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8602 s i)) at 1.
  unfold R.v8602, N.v8602.
  rewrite ?node_8598.
  rewrite ?node_8601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8603 (s : N.State) (i : N.Inputs) :
  R.v8603 (state s) (inputs i) = Zmod.unsigned (N.v8603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8603 s i)) at 1.
  unfold R.v8603, N.v8603.
  rewrite ?node_8421.
  rewrite !state_r730_nr_5F730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r730_nr_5F730 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8604 (s : N.State) (i : N.Inputs) :
  R.v8604 (state s) (inputs i) = Zmod.unsigned (N.v8604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8604 s i)) at 1.
  unfold R.v8604, N.v8604.
  rewrite ?node_8422.
  rewrite ?node_8425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8605 (s : N.State) (i : N.Inputs) :
  R.v8605 (state s) (inputs i) = Zmod.unsigned (N.v8605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8605 s i)) at 1.
  unfold R.v8605, N.v8605.
  rewrite ?node_8603.
  rewrite ?node_8604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8606 (s : N.State) (i : N.Inputs) :
  R.v8606 (state s) (inputs i) = Zmod.unsigned (N.v8606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8606 s i)) at 1.
  unfold R.v8606, N.v8606.
  rewrite ?node_8602.
  rewrite ?node_8605.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8607 (s : N.State) (i : N.Inputs) :
  R.v8607 (state s) (inputs i) = Zmod.unsigned (N.v8607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8607 s i)) at 1.
  unfold R.v8607, N.v8607.
  rewrite ?node_8461.
  rewrite ?node_8468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8608 (s : N.State) (i : N.Inputs) :
  R.v8608 (state s) (inputs i) = Zmod.unsigned (N.v8608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8608 s i)) at 1.
  unfold R.v8608, N.v8608.
  rewrite ?node_8469.
  rewrite ?node_8471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8609 (s : N.State) (i : N.Inputs) :
  R.v8609 (state s) (inputs i) = Zmod.unsigned (N.v8609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8609 s i)) at 1.
  unfold R.v8609, N.v8609.
  rewrite ?node_8607.
  rewrite ?node_8608.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8610 (s : N.State) (i : N.Inputs) :
  R.v8610 (state s) (inputs i) = Zmod.unsigned (N.v8610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8610 s i)) at 1.
  unfold R.v8610, N.v8610.
  rewrite ?node_8606.
  rewrite ?node_8609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8611 (s : N.State) (i : N.Inputs) :
  R.v8611 (state s) (inputs i) = Zmod.unsigned (N.v8611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8611 s i)) at 1.
  unfold R.v8611, N.v8611.
  rewrite ?node_8583.
  rewrite ?node_8610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8612 (s : N.State) (i : N.Inputs) :
  R.v8612 (state s) (inputs i) = Zmod.unsigned (N.v8612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8612 s i)) at 1.
  unfold R.v8612, N.v8612.
  rewrite ?node_8428.
  rewrite !state_r734_nr_5F734.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r734_nr_5F734 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8613 (s : N.State) (i : N.Inputs) :
  R.v8613 (state s) (inputs i) = Zmod.unsigned (N.v8613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8613 s i)) at 1.
  unfold R.v8613, N.v8613.
  rewrite ?node_8429.
  rewrite ?node_8432.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8614 (s : N.State) (i : N.Inputs) :
  R.v8614 (state s) (inputs i) = Zmod.unsigned (N.v8614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8614 s i)) at 1.
  unfold R.v8614, N.v8614.
  rewrite ?node_8612.
  rewrite ?node_8613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8615 (s : N.State) (i : N.Inputs) :
  R.v8615 (state s) (inputs i) = Zmod.unsigned (N.v8615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8615 s i)) at 1.
  unfold R.v8615, N.v8615.
  rewrite ?node_8436.
  rewrite !state_r738_nr_5F738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r738_nr_5F738 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8616 (s : N.State) (i : N.Inputs) :
  R.v8616 (state s) (inputs i) = Zmod.unsigned (N.v8616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8616 s i)) at 1.
  unfold R.v8616, N.v8616.
  rewrite ?node_8437.
  rewrite ?node_8440.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8617 (s : N.State) (i : N.Inputs) :
  R.v8617 (state s) (inputs i) = Zmod.unsigned (N.v8617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8617 s i)) at 1.
  unfold R.v8617, N.v8617.
  rewrite ?node_8615.
  rewrite ?node_8616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8618 (s : N.State) (i : N.Inputs) :
  R.v8618 (state s) (inputs i) = Zmod.unsigned (N.v8618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8618 s i)) at 1.
  unfold R.v8618, N.v8618.
  rewrite ?node_8614.
  rewrite ?node_8617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8619 (s : N.State) (i : N.Inputs) :
  R.v8619 (state s) (inputs i) = Zmod.unsigned (N.v8619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8619 s i)) at 1.
  unfold R.v8619, N.v8619.
  rewrite ?node_8444.
  rewrite !state_r742_nr_5F742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r742_nr_5F742 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8620 (s : N.State) (i : N.Inputs) :
  R.v8620 (state s) (inputs i) = Zmod.unsigned (N.v8620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8620 s i)) at 1.
  unfold R.v8620, N.v8620.
  rewrite ?node_8445.
  rewrite ?node_8448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8621 (s : N.State) (i : N.Inputs) :
  R.v8621 (state s) (inputs i) = Zmod.unsigned (N.v8621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8621 s i)) at 1.
  unfold R.v8621, N.v8621.
  rewrite ?node_8619.
  rewrite ?node_8620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8622 (s : N.State) (i : N.Inputs) :
  R.v8622 (state s) (inputs i) = Zmod.unsigned (N.v8622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8622 s i)) at 1.
  unfold R.v8622, N.v8622.
  rewrite ?node_8618.
  rewrite ?node_8621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8623 (s : N.State) (i : N.Inputs) :
  R.v8623 (state s) (inputs i) = Zmod.unsigned (N.v8623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8623 s i)) at 1.
  unfold R.v8623, N.v8623.
  rewrite ?node_8456.
  rewrite !state_r746_nr_5F746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r746_nr_5F746 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8624 (s : N.State) (i : N.Inputs) :
  R.v8624 (state s) (inputs i) = Zmod.unsigned (N.v8624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8624 s i)) at 1.
  unfold R.v8624, N.v8624.
  rewrite ?node_8457.
  rewrite ?node_8460.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8625 (s : N.State) (i : N.Inputs) :
  R.v8625 (state s) (inputs i) = Zmod.unsigned (N.v8625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8625 s i)) at 1.
  unfold R.v8625, N.v8625.
  rewrite ?node_8623.
  rewrite ?node_8624.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8626 (s : N.State) (i : N.Inputs) :
  R.v8626 (state s) (inputs i) = Zmod.unsigned (N.v8626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8626 s i)) at 1.
  unfold R.v8626, N.v8626.
  rewrite ?node_8622.
  rewrite ?node_8625.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8627 (s : N.State) (i : N.Inputs) :
  R.v8627 (state s) (inputs i) = Zmod.unsigned (N.v8627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8627 s i)) at 1.
  unfold R.v8627, N.v8627.
  rewrite ?node_8484.
  rewrite ?node_8487.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8628 (s : N.State) (i : N.Inputs) :
  R.v8628 (state s) (inputs i) = Zmod.unsigned (N.v8628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8628 s i)) at 1.
  unfold R.v8628, N.v8628.
  rewrite ?node_8488.
  rewrite ?node_8491.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8629 (s : N.State) (i : N.Inputs) :
  R.v8629 (state s) (inputs i) = Zmod.unsigned (N.v8629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8629 s i)) at 1.
  unfold R.v8629, N.v8629.
  rewrite ?node_8627.
  rewrite ?node_8628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8630 (s : N.State) (i : N.Inputs) :
  R.v8630 (state s) (inputs i) = Zmod.unsigned (N.v8630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8630 s i)) at 1.
  unfold R.v8630, N.v8630.
  rewrite ?node_8626.
  rewrite ?node_8629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8631 (s : N.State) (i : N.Inputs) :
  R.v8631 (state s) (inputs i) = Zmod.unsigned (N.v8631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8631 s i)) at 1.
  unfold R.v8631, N.v8631.
  rewrite ?node_8611.
  rewrite ?node_8630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8632 (s : N.State) (i : N.Inputs) :
  R.v8632 (state s) (inputs i) = Zmod.unsigned (N.v8632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8632 s i)) at 1.
  unfold R.v8632, N.v8632.
  rewrite ?node_8463.
  rewrite !state_r750_nr_5F750.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r750_nr_5F750 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8633 (s : N.State) (i : N.Inputs) :
  R.v8633 (state s) (inputs i) = Zmod.unsigned (N.v8633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8633 s i)) at 1.
  unfold R.v8633, N.v8633.
  rewrite ?node_8464.
  rewrite ?node_8467.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8634 (s : N.State) (i : N.Inputs) :
  R.v8634 (state s) (inputs i) = Zmod.unsigned (N.v8634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8634 s i)) at 1.
  unfold R.v8634, N.v8634.
  rewrite ?node_8632.
  rewrite ?node_8633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8635 (s : N.State) (i : N.Inputs) :
  R.v8635 (state s) (inputs i) = Zmod.unsigned (N.v8635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8635 s i)) at 1.
  unfold R.v8635, N.v8635.
  rewrite !state_r751_nr_5F751.
  rewrite !state_r752_nr_5F752.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r751_nr_5F751 s)).
  rewrite ?(bits.mod_to_Z (N.r752_nr_5F752 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8636 (s : N.State) (i : N.Inputs) :
  R.v8636 (state s) (inputs i) = Zmod.unsigned (N.v8636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8636 s i)) at 1.
  unfold R.v8636, N.v8636.
  rewrite ?node_8470.
  rewrite !state_r753_nr_5F753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r753_nr_5F753 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8637 (s : N.State) (i : N.Inputs) :
  R.v8637 (state s) (inputs i) = Zmod.unsigned (N.v8637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8637 s i)) at 1.
  unfold R.v8637, N.v8637.
  rewrite ?node_8635.
  rewrite ?node_8636.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8638 (s : N.State) (i : N.Inputs) :
  R.v8638 (state s) (inputs i) = Zmod.unsigned (N.v8638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8638 s i)) at 1.
  unfold R.v8638, N.v8638.
  rewrite ?node_8634.
  rewrite ?node_8637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8639 (s : N.State) (i : N.Inputs) :
  R.v8639 (state s) (inputs i) = Zmod.unsigned (N.v8639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8639 s i)) at 1.
  unfold R.v8639, N.v8639.
  rewrite ?node_8631.
  rewrite ?node_8638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8640 (s : N.State) (i : N.Inputs) :
  R.v8640 (state s) (inputs i) = Zmod.unsigned (N.v8640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8640 s i)) at 1.
  unfold R.v8640, N.v8640.
  rewrite ?node_8454.
  rewrite ?node_8480.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8641 (s : N.State) (i : N.Inputs) :
  R.v8641 (state s) (inputs i) = Zmod.unsigned (N.v8641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8641 s i)) at 1.
  unfold R.v8641, N.v8641.
  rewrite ?node_8481.
  rewrite ?node_8500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8642 (s : N.State) (i : N.Inputs) :
  R.v8642 (state s) (inputs i) = Zmod.unsigned (N.v8642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8642 s i)) at 1.
  unfold R.v8642, N.v8642.
  rewrite ?node_8640.
  rewrite ?node_8641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8643 (s : N.State) (i : N.Inputs) :
  R.v8643 (state s) (inputs i) = Zmod.unsigned (N.v8643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8643 s i)) at 1.
  unfold R.v8643, N.v8643.
  rewrite ?node_8639.
  rewrite ?node_8642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8644 (s : N.State) (i : N.Inputs) :
  R.v8644 (state s) (inputs i) = Zmod.unsigned (N.v8644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8644 s i)) at 1.
  unfold R.v8644, N.v8644.
  rewrite ?node_8442.
  rewrite ?node_8449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8645 (s : N.State) (i : N.Inputs) :
  R.v8645 (state s) (inputs i) = Zmod.unsigned (N.v8645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8645 s i)) at 1.
  unfold R.v8645, N.v8645.
  rewrite ?node_8450.
  rewrite ?node_8453.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8646 (s : N.State) (i : N.Inputs) :
  R.v8646 (state s) (inputs i) = Zmod.unsigned (N.v8646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8646 s i)) at 1.
  unfold R.v8646, N.v8646.
  rewrite ?node_8644.
  rewrite ?node_8645.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8647 (s : N.State) (i : N.Inputs) :
  R.v8647 (state s) (inputs i) = Zmod.unsigned (N.v8647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8647 s i)) at 1.
  unfold R.v8647, N.v8647.
  rewrite ?node_8472.
  rewrite ?node_8475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8648 (s : N.State) (i : N.Inputs) :
  R.v8648 (state s) (inputs i) = Zmod.unsigned (N.v8648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8648 s i)) at 1.
  unfold R.v8648, N.v8648.
  rewrite ?node_8476.
  rewrite ?node_8479.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8649 (s : N.State) (i : N.Inputs) :
  R.v8649 (state s) (inputs i) = Zmod.unsigned (N.v8649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8649 s i)) at 1.
  unfold R.v8649, N.v8649.
  rewrite ?node_8647.
  rewrite ?node_8648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8650 (s : N.State) (i : N.Inputs) :
  R.v8650 (state s) (inputs i) = Zmod.unsigned (N.v8650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8650 s i)) at 1.
  unfold R.v8650, N.v8650.
  rewrite ?node_8646.
  rewrite ?node_8649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8651 (s : N.State) (i : N.Inputs) :
  R.v8651 (state s) (inputs i) = Zmod.unsigned (N.v8651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8651 s i)) at 1.
  unfold R.v8651, N.v8651.
  rewrite ?node_8492.
  rewrite ?node_8495.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8652 (s : N.State) (i : N.Inputs) :
  R.v8652 (state s) (inputs i) = Zmod.unsigned (N.v8652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8652 s i)) at 1.
  unfold R.v8652, N.v8652.
  rewrite ?node_8496.
  rewrite ?node_8499.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8653 (s : N.State) (i : N.Inputs) :
  R.v8653 (state s) (inputs i) = Zmod.unsigned (N.v8653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8653 s i)) at 1.
  unfold R.v8653, N.v8653.
  rewrite ?node_8651.
  rewrite ?node_8652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8654 (s : N.State) (i : N.Inputs) :
  R.v8654 (state s) (inputs i) = Zmod.unsigned (N.v8654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8654 s i)) at 1.
  unfold R.v8654, N.v8654.
  rewrite ?node_8650.
  rewrite ?node_8653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8655 (s : N.State) (i : N.Inputs) :
  R.v8655 (state s) (inputs i) = Zmod.unsigned (N.v8655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8655 s i)) at 1.
  unfold R.v8655, N.v8655.
  rewrite ?node_8504.
  rewrite ?node_8507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8656 (s : N.State) (i : N.Inputs) :
  R.v8656 (state s) (inputs i) = Zmod.unsigned (N.v8656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8656 s i)) at 1.
  unfold R.v8656, N.v8656.
  rewrite ?node_8654.
  rewrite ?node_8655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8657 (s : N.State) (i : N.Inputs) :
  R.v8657 (state s) (inputs i) = Zmod.unsigned (N.v8657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8657 s i)) at 1.
  unfold R.v8657, N.v8657.
  rewrite ?node_8516.
  rewrite ?node_8519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8658 (s : N.State) (i : N.Inputs) :
  R.v8658 (state s) (inputs i) = Zmod.unsigned (N.v8658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8658 s i)) at 1.
  unfold R.v8658, N.v8658.
  rewrite ?node_8520.
  rewrite ?node_8523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8659 (s : N.State) (i : N.Inputs) :
  R.v8659 (state s) (inputs i) = Zmod.unsigned (N.v8659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8659 s i)) at 1.
  unfold R.v8659, N.v8659.
  rewrite ?node_8657.
  rewrite ?node_8658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8660 (s : N.State) (i : N.Inputs) :
  R.v8660 (state s) (inputs i) = Zmod.unsigned (N.v8660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8660 s i)) at 1.
  unfold R.v8660, N.v8660.
  rewrite ?node_8656.
  rewrite ?node_8659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8661 (s : N.State) (i : N.Inputs) :
  R.v8661 (state s) (inputs i) = Zmod.unsigned (N.v8661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8661 s i)) at 1.
  unfold R.v8661, N.v8661.
  rewrite ?node_8643.
  rewrite ?node_8660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8662 (s : N.State) (i : N.Inputs) :
  R.v8662 (state s) (inputs i) = Zmod.unsigned (N.v8662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8662 s i)) at 1.
  unfold R.v8662, N.v8662.
  rewrite ?node_8501.
  rewrite ?node_8508.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8663 (s : N.State) (i : N.Inputs) :
  R.v8663 (state s) (inputs i) = Zmod.unsigned (N.v8663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8663 s i)) at 1.
  unfold R.v8663, N.v8663.
  rewrite ?node_8509.
  rewrite ?node_8512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8664 (s : N.State) (i : N.Inputs) :
  R.v8664 (state s) (inputs i) = Zmod.unsigned (N.v8664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8664 s i)) at 1.
  unfold R.v8664, N.v8664.
  rewrite ?node_8662.
  rewrite ?node_8663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8665 (s : N.State) (i : N.Inputs) :
  R.v8665 (state s) (inputs i) = Zmod.unsigned (N.v8665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8665 s i)) at 1.
  unfold R.v8665, N.v8665.
  rewrite ?node_8661.
  rewrite ?node_8664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8666 (s : N.State) (i : N.Inputs) :
  R.v8666 (state s) (inputs i) = Zmod.unsigned (N.v8666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8666 s i)) at 1.
  unfold R.v8666, N.v8666.
  rewrite ?node_8524.
  rewrite ?node_8525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8667 (s : N.State) (i : N.Inputs) :
  R.v8667 (state s) (inputs i) = Zmod.unsigned (N.v8667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8667 s i)) at 1.
  unfold R.v8667, N.v8667.
  rewrite ?node_8526.
  rewrite ?node_8529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8668 (s : N.State) (i : N.Inputs) :
  R.v8668 (state s) (inputs i) = Zmod.unsigned (N.v8668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8668 s i)) at 1.
  unfold R.v8668, N.v8668.
  rewrite ?node_8666.
  rewrite ?node_8667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8669 (s : N.State) (i : N.Inputs) :
  R.v8669 (state s) (inputs i) = Zmod.unsigned (N.v8669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8669 s i)) at 1.
  unfold R.v8669, N.v8669.
  rewrite ?node_8665.
  rewrite ?node_8668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8670 (s : N.State) (i : N.Inputs) :
  R.v8670 (state s) (inputs i) = Zmod.unsigned (N.v8670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8670 s i)) at 1.
  unfold R.v8670, N.v8670.
  rewrite ?node_8513.
  rewrite ?node_8530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8671 (s : N.State) (i : N.Inputs) :
  R.v8671 (state s) (inputs i) = Zmod.unsigned (N.v8671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8671 s i)) at 1.
  unfold R.v8671, N.v8671.
  rewrite ?node_8531.
  rewrite ?node_8534.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8672 (s : N.State) (i : N.Inputs) :
  R.v8672 (state s) (inputs i) = Zmod.unsigned (N.v8672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8672 s i)) at 1.
  unfold R.v8672, N.v8672.
  rewrite ?node_8670.
  rewrite ?node_8671.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8673 (s : N.State) (i : N.Inputs) :
  R.v8673 (state s) (inputs i) = Zmod.unsigned (N.v8673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8673 s i)) at 1.
  unfold R.v8673, N.v8673.
  rewrite ?node_8669.
  rewrite ?node_8672.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8674 (s : N.State) (i : N.Inputs) :
  R.v8674 (state s) (inputs i) = Zmod.unsigned (N.v8674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8674 s i)) at 1.
  unfold R.v8674, N.v8674.
  rewrite ?node_8535.
  rewrite ?node_8536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8675 (s : N.State) (i : N.Inputs) :
  R.v8675 (state s) (inputs i) = Zmod.unsigned (N.v8675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8675 s i)) at 1.
  unfold R.v8675, N.v8675.
  rewrite ?node_8537.
  rewrite ?node_8540.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8676 (s : N.State) (i : N.Inputs) :
  R.v8676 (state s) (inputs i) = Zmod.unsigned (N.v8676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8676 s i)) at 1.
  unfold R.v8676, N.v8676.
  rewrite ?node_8674.
  rewrite ?node_8675.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8677 (s : N.State) (i : N.Inputs) :
  R.v8677 (state s) (inputs i) = Zmod.unsigned (N.v8677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8677 s i)) at 1.
  unfold R.v8677, N.v8677.
  rewrite ?node_8673.
  rewrite ?node_8676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8678 (s : N.State) (i : N.Inputs) :
  R.v8678 (state s) (inputs i) = Zmod.unsigned (N.v8678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8678 s i)) at 1.
  unfold R.v8678, N.v8678.
  rewrite ?node_8677.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2377_nr_5F2408.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2377_nr_5F2408 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8679 (s : N.State) (i : N.Inputs) :
  R.v8679 (state s) (inputs i) = Zmod.unsigned (N.v8679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8679 s i)) at 1.
  unfold R.v8679, N.v8679.
  rewrite ?node_8541.
  rewrite ?node_8544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8680 (s : N.State) (i : N.Inputs) :
  R.v8680 (state s) (inputs i) = Zmod.unsigned (N.v8680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8680 s i)) at 1.
  unfold R.v8680, N.v8680.
  rewrite ?node_8679.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2378_nr_5F2409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2378_nr_5F2409 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8681 (s : N.State) (i : N.Inputs) :
  R.v8681 (state s) (inputs i) = Zmod.unsigned (N.v8681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8681 s i)) at 1.
  unfold R.v8681, N.v8681.
  rewrite !state_r782_nr_5F782.
  rewrite !state_r783_nr_5F783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r782_nr_5F782 s)).
  rewrite ?(bits.mod_to_Z (N.r783_nr_5F783 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8682 (s : N.State) (i : N.Inputs) :
  R.v8682 (state s) (inputs i) = Zmod.unsigned (N.v8682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8682 s i)) at 1.
  unfold R.v8682, N.v8682.
  rewrite ?node_8681.
  rewrite !state_r784_nr_5F784.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r784_nr_5F784 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8683 (s : N.State) (i : N.Inputs) :
  R.v8683 (state s) (inputs i) = Zmod.unsigned (N.v8683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8683 s i)) at 1.
  unfold R.v8683, N.v8683.
  rewrite ?node_8682.
  rewrite !state_r785_nr_5F785.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r785_nr_5F785 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8684 (s : N.State) (i : N.Inputs) :
  R.v8684 (state s) (inputs i) = Zmod.unsigned (N.v8684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8684 s i)) at 1.
  unfold R.v8684, N.v8684.
  rewrite !state_r754_nr_5F754.
  rewrite !state_r755_nr_5F755.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r754_nr_5F754 s)).
  rewrite ?(bits.mod_to_Z (N.r755_nr_5F755 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8685 (s : N.State) (i : N.Inputs) :
  R.v8685 (state s) (inputs i) = Zmod.unsigned (N.v8685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8685 s i)) at 1.
  unfold R.v8685, N.v8685.
  rewrite ?node_8549.
  rewrite !state_r756_nr_5F756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r756_nr_5F756 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8686 (s : N.State) (i : N.Inputs) :
  R.v8686 (state s) (inputs i) = Zmod.unsigned (N.v8686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8686 s i)) at 1.
  unfold R.v8686, N.v8686.
  rewrite ?node_8684.
  rewrite ?node_8685.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8687 (s : N.State) (i : N.Inputs) :
  R.v8687 (state s) (inputs i) = Zmod.unsigned (N.v8687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8687 s i)) at 1.
  unfold R.v8687, N.v8687.
  rewrite ?node_8683.
  rewrite ?node_8686.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8688 (s : N.State) (i : N.Inputs) :
  R.v8688 (state s) (inputs i) = Zmod.unsigned (N.v8688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8688 s i)) at 1.
  unfold R.v8688, N.v8688.
  rewrite !state_r786_nr_5F786.
  rewrite !state_r787_nr_5F787.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r786_nr_5F786 s)).
  rewrite ?(bits.mod_to_Z (N.r787_nr_5F787 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8689 (s : N.State) (i : N.Inputs) :
  R.v8689 (state s) (inputs i) = Zmod.unsigned (N.v8689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8689 s i)) at 1.
  unfold R.v8689, N.v8689.
  rewrite ?node_8688.
  rewrite !state_r788_nr_5F788.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r788_nr_5F788 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8690 (s : N.State) (i : N.Inputs) :
  R.v8690 (state s) (inputs i) = Zmod.unsigned (N.v8690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8690 s i)) at 1.
  unfold R.v8690, N.v8690.
  rewrite ?node_8689.
  rewrite !state_r789_nr_5F789.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r789_nr_5F789 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8691 (s : N.State) (i : N.Inputs) :
  R.v8691 (state s) (inputs i) = Zmod.unsigned (N.v8691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8691 s i)) at 1.
  unfold R.v8691, N.v8691.
  rewrite !state_r758_nr_5F758.
  rewrite !state_r759_nr_5F759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r758_nr_5F758 s)).
  rewrite ?(bits.mod_to_Z (N.r759_nr_5F759 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8692 (s : N.State) (i : N.Inputs) :
  R.v8692 (state s) (inputs i) = Zmod.unsigned (N.v8692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8692 s i)) at 1.
  unfold R.v8692, N.v8692.
  rewrite ?node_8556.
  rewrite !state_r760_nr_5F760.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r760_nr_5F760 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8693 (s : N.State) (i : N.Inputs) :
  R.v8693 (state s) (inputs i) = Zmod.unsigned (N.v8693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8693 s i)) at 1.
  unfold R.v8693, N.v8693.
  rewrite ?node_8691.
  rewrite ?node_8692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8694 (s : N.State) (i : N.Inputs) :
  R.v8694 (state s) (inputs i) = Zmod.unsigned (N.v8694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8694 s i)) at 1.
  unfold R.v8694, N.v8694.
  rewrite ?node_8690.
  rewrite ?node_8693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8695 (s : N.State) (i : N.Inputs) :
  R.v8695 (state s) (inputs i) = Zmod.unsigned (N.v8695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8695 s i)) at 1.
  unfold R.v8695, N.v8695.
  rewrite ?node_8687.
  rewrite ?node_8694.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8696 (s : N.State) (i : N.Inputs) :
  R.v8696 (state s) (inputs i) = Zmod.unsigned (N.v8696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8696 s i)) at 1.
  unfold R.v8696, N.v8696.
  rewrite !state_r790_nr_5F790.
  rewrite !state_r791_nr_5F791.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r790_nr_5F790 s)).
  rewrite ?(bits.mod_to_Z (N.r791_nr_5F791 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8697 (s : N.State) (i : N.Inputs) :
  R.v8697 (state s) (inputs i) = Zmod.unsigned (N.v8697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8697 s i)) at 1.
  unfold R.v8697, N.v8697.
  rewrite ?node_8696.
  rewrite !state_r792_nr_5F792.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r792_nr_5F792 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8698 (s : N.State) (i : N.Inputs) :
  R.v8698 (state s) (inputs i) = Zmod.unsigned (N.v8698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8698 s i)) at 1.
  unfold R.v8698, N.v8698.
  rewrite ?node_8697.
  rewrite !state_r793_nr_5F793.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r793_nr_5F793 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8699 (s : N.State) (i : N.Inputs) :
  R.v8699 (state s) (inputs i) = Zmod.unsigned (N.v8699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8699 s i)) at 1.
  unfold R.v8699, N.v8699.
  rewrite !state_r762_nr_5F762.
  rewrite !state_r763_nr_5F763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r762_nr_5F762 s)).
  rewrite ?(bits.mod_to_Z (N.r763_nr_5F763 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8700 (s : N.State) (i : N.Inputs) :
  R.v8700 (state s) (inputs i) = Zmod.unsigned (N.v8700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8700 s i)) at 1.
  unfold R.v8700, N.v8700.
  rewrite ?node_8564.
  rewrite !state_r764_nr_5F764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r764_nr_5F764 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8701 (s : N.State) (i : N.Inputs) :
  R.v8701 (state s) (inputs i) = Zmod.unsigned (N.v8701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8701 s i)) at 1.
  unfold R.v8701, N.v8701.
  rewrite ?node_8699.
  rewrite ?node_8700.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8702 (s : N.State) (i : N.Inputs) :
  R.v8702 (state s) (inputs i) = Zmod.unsigned (N.v8702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8702 s i)) at 1.
  unfold R.v8702, N.v8702.
  rewrite ?node_8698.
  rewrite ?node_8701.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8703 (s : N.State) (i : N.Inputs) :
  R.v8703 (state s) (inputs i) = Zmod.unsigned (N.v8703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8703 s i)) at 1.
  unfold R.v8703, N.v8703.
  rewrite ?node_8695.
  rewrite ?node_8702.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8704 (s : N.State) (i : N.Inputs) :
  R.v8704 (state s) (inputs i) = Zmod.unsigned (N.v8704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8704 s i)) at 1.
  unfold R.v8704, N.v8704.
  rewrite !state_r794_nr_5F794.
  rewrite !state_r795_nr_5F795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r794_nr_5F794 s)).
  rewrite ?(bits.mod_to_Z (N.r795_nr_5F795 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8705 (s : N.State) (i : N.Inputs) :
  R.v8705 (state s) (inputs i) = Zmod.unsigned (N.v8705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8705 s i)) at 1.
  unfold R.v8705, N.v8705.
  rewrite ?node_8704.
  rewrite !state_r796_nr_5F796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r796_nr_5F796 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8706 (s : N.State) (i : N.Inputs) :
  R.v8706 (state s) (inputs i) = Zmod.unsigned (N.v8706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8706 s i)) at 1.
  unfold R.v8706, N.v8706.
  rewrite ?node_8705.
  rewrite !state_r797_nr_5F797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r797_nr_5F797 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8707 (s : N.State) (i : N.Inputs) :
  R.v8707 (state s) (inputs i) = Zmod.unsigned (N.v8707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8707 s i)) at 1.
  unfold R.v8707, N.v8707.
  rewrite !state_r766_nr_5F766.
  rewrite !state_r767_nr_5F767.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r766_nr_5F766 s)).
  rewrite ?(bits.mod_to_Z (N.r767_nr_5F767 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8708 (s : N.State) (i : N.Inputs) :
  R.v8708 (state s) (inputs i) = Zmod.unsigned (N.v8708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8708 s i)) at 1.
  unfold R.v8708, N.v8708.
  rewrite ?node_8572.
  rewrite !state_r768_nr_5F768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r768_nr_5F768 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8709 (s : N.State) (i : N.Inputs) :
  R.v8709 (state s) (inputs i) = Zmod.unsigned (N.v8709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8709 s i)) at 1.
  unfold R.v8709, N.v8709.
  rewrite ?node_8707.
  rewrite ?node_8708.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8710 (s : N.State) (i : N.Inputs) :
  R.v8710 (state s) (inputs i) = Zmod.unsigned (N.v8710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8710 s i)) at 1.
  unfold R.v8710, N.v8710.
  rewrite ?node_8706.
  rewrite ?node_8709.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8711 (s : N.State) (i : N.Inputs) :
  R.v8711 (state s) (inputs i) = Zmod.unsigned (N.v8711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8711 s i)) at 1.
  unfold R.v8711, N.v8711.
  rewrite ?node_8703.
  rewrite ?node_8710.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8712 (s : N.State) (i : N.Inputs) :
  R.v8712 (state s) (inputs i) = Zmod.unsigned (N.v8712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8712 s i)) at 1.
  unfold R.v8712, N.v8712.
  rewrite ?node_8555.
  rewrite ?node_8562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8713 (s : N.State) (i : N.Inputs) :
  R.v8713 (state s) (inputs i) = Zmod.unsigned (N.v8713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8713 s i)) at 1.
  unfold R.v8713, N.v8713.
  rewrite ?node_8563.
  rewrite ?node_8570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8714 (s : N.State) (i : N.Inputs) :
  R.v8714 (state s) (inputs i) = Zmod.unsigned (N.v8714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8714 s i)) at 1.
  unfold R.v8714, N.v8714.
  rewrite ?node_8712.
  rewrite ?node_8713.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8715 (s : N.State) (i : N.Inputs) :
  R.v8715 (state s) (inputs i) = Zmod.unsigned (N.v8715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8715 s i)) at 1.
  unfold R.v8715, N.v8715.
  rewrite ?node_8711.
  rewrite ?node_8714.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8716 (s : N.State) (i : N.Inputs) :
  R.v8716 (state s) (inputs i) = Zmod.unsigned (N.v8716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8716 s i)) at 1.
  unfold R.v8716, N.v8716.
  rewrite !state_r798_nr_5F798.
  rewrite !state_r799_nr_5F799.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r798_nr_5F798 s)).
  rewrite ?(bits.mod_to_Z (N.r799_nr_5F799 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8717 (s : N.State) (i : N.Inputs) :
  R.v8717 (state s) (inputs i) = Zmod.unsigned (N.v8717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8717 s i)) at 1.
  unfold R.v8717, N.v8717.
  rewrite ?node_8716.
  rewrite !state_r800_nr_5F800.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r800_nr_5F800 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8718 (s : N.State) (i : N.Inputs) :
  R.v8718 (state s) (inputs i) = Zmod.unsigned (N.v8718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8718 s i)) at 1.
  unfold R.v8718, N.v8718.
  rewrite ?node_8717.
  rewrite !state_r801_nr_5F801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r801_nr_5F801 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8719 (s : N.State) (i : N.Inputs) :
  R.v8719 (state s) (inputs i) = Zmod.unsigned (N.v8719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8719 s i)) at 1.
  unfold R.v8719, N.v8719.
  rewrite !state_r770_nr_5F770.
  rewrite !state_r771_nr_5F771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r770_nr_5F770 s)).
  rewrite ?(bits.mod_to_Z (N.r771_nr_5F771 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8720 (s : N.State) (i : N.Inputs) :
  R.v8720 (state s) (inputs i) = Zmod.unsigned (N.v8720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8720 s i)) at 1.
  unfold R.v8720, N.v8720.
  rewrite ?node_8584.
  rewrite !state_r772_nr_5F772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r772_nr_5F772 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8721 (s : N.State) (i : N.Inputs) :
  R.v8721 (state s) (inputs i) = Zmod.unsigned (N.v8721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8721 s i)) at 1.
  unfold R.v8721, N.v8721.
  rewrite ?node_8719.
  rewrite ?node_8720.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8722 (s : N.State) (i : N.Inputs) :
  R.v8722 (state s) (inputs i) = Zmod.unsigned (N.v8722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8722 s i)) at 1.
  unfold R.v8722, N.v8722.
  rewrite ?node_8718.
  rewrite ?node_8721.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8723 (s : N.State) (i : N.Inputs) :
  R.v8723 (state s) (inputs i) = Zmod.unsigned (N.v8723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8723 s i)) at 1.
  unfold R.v8723, N.v8723.
  rewrite !state_r802_nr_5F802.
  rewrite !state_r803_nr_5F803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r802_nr_5F802 s)).
  rewrite ?(bits.mod_to_Z (N.r803_nr_5F803 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8724 (s : N.State) (i : N.Inputs) :
  R.v8724 (state s) (inputs i) = Zmod.unsigned (N.v8724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8724 s i)) at 1.
  unfold R.v8724, N.v8724.
  rewrite ?node_8723.
  rewrite !state_r804_nr_5F804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r804_nr_5F804 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8725 (s : N.State) (i : N.Inputs) :
  R.v8725 (state s) (inputs i) = Zmod.unsigned (N.v8725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8725 s i)) at 1.
  unfold R.v8725, N.v8725.
  rewrite ?node_8724.
  rewrite !state_r805_nr_5F805.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r805_nr_5F805 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8726 (s : N.State) (i : N.Inputs) :
  R.v8726 (state s) (inputs i) = Zmod.unsigned (N.v8726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8726 s i)) at 1.
  unfold R.v8726, N.v8726.
  rewrite !state_r774_nr_5F774.
  rewrite !state_r775_nr_5F775.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r774_nr_5F774 s)).
  rewrite ?(bits.mod_to_Z (N.r775_nr_5F775 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8727 (s : N.State) (i : N.Inputs) :
  R.v8727 (state s) (inputs i) = Zmod.unsigned (N.v8727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8727 s i)) at 1.
  unfold R.v8727, N.v8727.
  rewrite ?node_8591.
  rewrite !state_r776_nr_5F776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r776_nr_5F776 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8728 (s : N.State) (i : N.Inputs) :
  R.v8728 (state s) (inputs i) = Zmod.unsigned (N.v8728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8728 s i)) at 1.
  unfold R.v8728, N.v8728.
  rewrite ?node_8726.
  rewrite ?node_8727.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8729 (s : N.State) (i : N.Inputs) :
  R.v8729 (state s) (inputs i) = Zmod.unsigned (N.v8729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8729 s i)) at 1.
  unfold R.v8729, N.v8729.
  rewrite ?node_8725.
  rewrite ?node_8728.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8730 (s : N.State) (i : N.Inputs) :
  R.v8730 (state s) (inputs i) = Zmod.unsigned (N.v8730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8730 s i)) at 1.
  unfold R.v8730, N.v8730.
  rewrite ?node_8722.
  rewrite ?node_8729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8731 (s : N.State) (i : N.Inputs) :
  R.v8731 (state s) (inputs i) = Zmod.unsigned (N.v8731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8731 s i)) at 1.
  unfold R.v8731, N.v8731.
  rewrite !state_r806_nr_5F806.
  rewrite !state_r807_nr_5F807.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r806_nr_5F806 s)).
  rewrite ?(bits.mod_to_Z (N.r807_nr_5F807 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8732 (s : N.State) (i : N.Inputs) :
  R.v8732 (state s) (inputs i) = Zmod.unsigned (N.v8732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8732 s i)) at 1.
  unfold R.v8732, N.v8732.
  rewrite ?node_8731.
  rewrite !state_r808_nr_5F808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r808_nr_5F808 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8733 (s : N.State) (i : N.Inputs) :
  R.v8733 (state s) (inputs i) = Zmod.unsigned (N.v8733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8733 s i)) at 1.
  unfold R.v8733, N.v8733.
  rewrite ?node_8732.
  rewrite !state_r809_nr_5F809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r809_nr_5F809 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8734 (s : N.State) (i : N.Inputs) :
  R.v8734 (state s) (inputs i) = Zmod.unsigned (N.v8734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8734 s i)) at 1.
  unfold R.v8734, N.v8734.
  rewrite !state_r778_nr_5F778.
  rewrite !state_r779_nr_5F779.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r778_nr_5F778 s)).
  rewrite ?(bits.mod_to_Z (N.r779_nr_5F779 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8735 (s : N.State) (i : N.Inputs) :
  R.v8735 (state s) (inputs i) = Zmod.unsigned (N.v8735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8735 s i)) at 1.
  unfold R.v8735, N.v8735.
  rewrite ?node_8599.
  rewrite !state_r780_nr_5F780.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r780_nr_5F780 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8736 (s : N.State) (i : N.Inputs) :
  R.v8736 (state s) (inputs i) = Zmod.unsigned (N.v8736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8736 s i)) at 1.
  unfold R.v8736, N.v8736.
  rewrite ?node_8734.
  rewrite ?node_8735.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8737 (s : N.State) (i : N.Inputs) :
  R.v8737 (state s) (inputs i) = Zmod.unsigned (N.v8737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8737 s i)) at 1.
  unfold R.v8737, N.v8737.
  rewrite ?node_8733.
  rewrite ?node_8736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8738 (s : N.State) (i : N.Inputs) :
  R.v8738 (state s) (inputs i) = Zmod.unsigned (N.v8738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8738 s i)) at 1.
  unfold R.v8738, N.v8738.
  rewrite ?node_8730.
  rewrite ?node_8737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8739 (s : N.State) (i : N.Inputs) :
  R.v8739 (state s) (inputs i) = Zmod.unsigned (N.v8739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8739 s i)) at 1.
  unfold R.v8739, N.v8739.
  rewrite ?node_8550.
  rewrite !state_r757_nr_5F757.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r757_nr_5F757 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8740 (s : N.State) (i : N.Inputs) :
  R.v8740 (state s) (inputs i) = Zmod.unsigned (N.v8740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8740 s i)) at 1.
  unfold R.v8740, N.v8740.
  rewrite ?node_8551.
  rewrite ?node_8554.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8741 (s : N.State) (i : N.Inputs) :
  R.v8741 (state s) (inputs i) = Zmod.unsigned (N.v8741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8741 s i)) at 1.
  unfold R.v8741, N.v8741.
  rewrite ?node_8739.
  rewrite ?node_8740.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8742 (s : N.State) (i : N.Inputs) :
  R.v8742 (state s) (inputs i) = Zmod.unsigned (N.v8742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8742 s i)) at 1.
  unfold R.v8742, N.v8742.
  rewrite ?node_8738.
  rewrite ?node_8741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8743 (s : N.State) (i : N.Inputs) :
  R.v8743 (state s) (inputs i) = Zmod.unsigned (N.v8743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8743 s i)) at 1.
  unfold R.v8743, N.v8743.
  rewrite ?node_8590.
  rewrite ?node_8597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8744 (s : N.State) (i : N.Inputs) :
  R.v8744 (state s) (inputs i) = Zmod.unsigned (N.v8744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8744 s i)) at 1.
  unfold R.v8744, N.v8744.
  rewrite ?node_8598.
  rewrite ?node_8601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8745 (s : N.State) (i : N.Inputs) :
  R.v8745 (state s) (inputs i) = Zmod.unsigned (N.v8745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8745 s i)) at 1.
  unfold R.v8745, N.v8745.
  rewrite ?node_8743.
  rewrite ?node_8744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8746 (s : N.State) (i : N.Inputs) :
  R.v8746 (state s) (inputs i) = Zmod.unsigned (N.v8746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8746 s i)) at 1.
  unfold R.v8746, N.v8746.
  rewrite ?node_8742.
  rewrite ?node_8745.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8747 (s : N.State) (i : N.Inputs) :
  R.v8747 (state s) (inputs i) = Zmod.unsigned (N.v8747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8747 s i)) at 1.
  unfold R.v8747, N.v8747.
  rewrite ?node_8715.
  rewrite ?node_8746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8748 (s : N.State) (i : N.Inputs) :
  R.v8748 (state s) (inputs i) = Zmod.unsigned (N.v8748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8748 s i)) at 1.
  unfold R.v8748, N.v8748.
  rewrite ?node_8557.
  rewrite !state_r761_nr_5F761.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r761_nr_5F761 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8749 (s : N.State) (i : N.Inputs) :
  R.v8749 (state s) (inputs i) = Zmod.unsigned (N.v8749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8749 s i)) at 1.
  unfold R.v8749, N.v8749.
  rewrite ?node_8558.
  rewrite ?node_8561.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8750 (s : N.State) (i : N.Inputs) :
  R.v8750 (state s) (inputs i) = Zmod.unsigned (N.v8750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8750 s i)) at 1.
  unfold R.v8750, N.v8750.
  rewrite ?node_8748.
  rewrite ?node_8749.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8751 (s : N.State) (i : N.Inputs) :
  R.v8751 (state s) (inputs i) = Zmod.unsigned (N.v8751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8751 s i)) at 1.
  unfold R.v8751, N.v8751.
  rewrite ?node_8565.
  rewrite !state_r765_nr_5F765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r765_nr_5F765 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8752 (s : N.State) (i : N.Inputs) :
  R.v8752 (state s) (inputs i) = Zmod.unsigned (N.v8752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8752 s i)) at 1.
  unfold R.v8752, N.v8752.
  rewrite ?node_8566.
  rewrite ?node_8569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8753 (s : N.State) (i : N.Inputs) :
  R.v8753 (state s) (inputs i) = Zmod.unsigned (N.v8753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8753 s i)) at 1.
  unfold R.v8753, N.v8753.
  rewrite ?node_8751.
  rewrite ?node_8752.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8754 (s : N.State) (i : N.Inputs) :
  R.v8754 (state s) (inputs i) = Zmod.unsigned (N.v8754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8754 s i)) at 1.
  unfold R.v8754, N.v8754.
  rewrite ?node_8750.
  rewrite ?node_8753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8755 (s : N.State) (i : N.Inputs) :
  R.v8755 (state s) (inputs i) = Zmod.unsigned (N.v8755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8755 s i)) at 1.
  unfold R.v8755, N.v8755.
  rewrite ?node_8573.
  rewrite !state_r769_nr_5F769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r769_nr_5F769 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8756 (s : N.State) (i : N.Inputs) :
  R.v8756 (state s) (inputs i) = Zmod.unsigned (N.v8756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8756 s i)) at 1.
  unfold R.v8756, N.v8756.
  rewrite ?node_8574.
  rewrite ?node_8577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8757 (s : N.State) (i : N.Inputs) :
  R.v8757 (state s) (inputs i) = Zmod.unsigned (N.v8757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8757 s i)) at 1.
  unfold R.v8757, N.v8757.
  rewrite ?node_8755.
  rewrite ?node_8756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8758 (s : N.State) (i : N.Inputs) :
  R.v8758 (state s) (inputs i) = Zmod.unsigned (N.v8758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8758 s i)) at 1.
  unfold R.v8758, N.v8758.
  rewrite ?node_8754.
  rewrite ?node_8757.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8759 (s : N.State) (i : N.Inputs) :
  R.v8759 (state s) (inputs i) = Zmod.unsigned (N.v8759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8759 s i)) at 1.
  unfold R.v8759, N.v8759.
  rewrite ?node_8585.
  rewrite !state_r773_nr_5F773.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r773_nr_5F773 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8760 (s : N.State) (i : N.Inputs) :
  R.v8760 (state s) (inputs i) = Zmod.unsigned (N.v8760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8760 s i)) at 1.
  unfold R.v8760, N.v8760.
  rewrite ?node_8586.
  rewrite ?node_8589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8761 (s : N.State) (i : N.Inputs) :
  R.v8761 (state s) (inputs i) = Zmod.unsigned (N.v8761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8761 s i)) at 1.
  unfold R.v8761, N.v8761.
  rewrite ?node_8759.
  rewrite ?node_8760.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8762 (s : N.State) (i : N.Inputs) :
  R.v8762 (state s) (inputs i) = Zmod.unsigned (N.v8762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8762 s i)) at 1.
  unfold R.v8762, N.v8762.
  rewrite ?node_8758.
  rewrite ?node_8761.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8763 (s : N.State) (i : N.Inputs) :
  R.v8763 (state s) (inputs i) = Zmod.unsigned (N.v8763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8763 s i)) at 1.
  unfold R.v8763, N.v8763.
  rewrite ?node_8614.
  rewrite ?node_8617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8764 (s : N.State) (i : N.Inputs) :
  R.v8764 (state s) (inputs i) = Zmod.unsigned (N.v8764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8764 s i)) at 1.
  unfold R.v8764, N.v8764.
  rewrite ?node_8618.
  rewrite ?node_8621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8765 (s : N.State) (i : N.Inputs) :
  R.v8765 (state s) (inputs i) = Zmod.unsigned (N.v8765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8765 s i)) at 1.
  unfold R.v8765, N.v8765.
  rewrite ?node_8763.
  rewrite ?node_8764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8766 (s : N.State) (i : N.Inputs) :
  R.v8766 (state s) (inputs i) = Zmod.unsigned (N.v8766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8766 s i)) at 1.
  unfold R.v8766, N.v8766.
  rewrite ?node_8762.
  rewrite ?node_8765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8767 (s : N.State) (i : N.Inputs) :
  R.v8767 (state s) (inputs i) = Zmod.unsigned (N.v8767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8767 s i)) at 1.
  unfold R.v8767, N.v8767.
  rewrite ?node_8747.
  rewrite ?node_8766.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8768 (s : N.State) (i : N.Inputs) :
  R.v8768 (state s) (inputs i) = Zmod.unsigned (N.v8768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8768 s i)) at 1.
  unfold R.v8768, N.v8768.
  rewrite ?node_8592.
  rewrite !state_r777_nr_5F777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r777_nr_5F777 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8769 (s : N.State) (i : N.Inputs) :
  R.v8769 (state s) (inputs i) = Zmod.unsigned (N.v8769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8769 s i)) at 1.
  unfold R.v8769, N.v8769.
  rewrite ?node_8593.
  rewrite ?node_8596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8770 (s : N.State) (i : N.Inputs) :
  R.v8770 (state s) (inputs i) = Zmod.unsigned (N.v8770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8770 s i)) at 1.
  unfold R.v8770, N.v8770.
  rewrite ?node_8768.
  rewrite ?node_8769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8771 (s : N.State) (i : N.Inputs) :
  R.v8771 (state s) (inputs i) = Zmod.unsigned (N.v8771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8771 s i)) at 1.
  unfold R.v8771, N.v8771.
  rewrite ?node_8600.
  rewrite !state_r781_nr_5F781.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r781_nr_5F781 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8772 (s : N.State) (i : N.Inputs) :
  R.v8772 (state s) (inputs i) = Zmod.unsigned (N.v8772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8772 s i)) at 1.
  unfold R.v8772, N.v8772.
  rewrite ?node_8770.
  rewrite ?node_8771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8773 (s : N.State) (i : N.Inputs) :
  R.v8773 (state s) (inputs i) = Zmod.unsigned (N.v8773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8773 s i)) at 1.
  unfold R.v8773, N.v8773.
  rewrite ?node_8767.
  rewrite ?node_8772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8774 (s : N.State) (i : N.Inputs) :
  R.v8774 (state s) (inputs i) = Zmod.unsigned (N.v8774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8774 s i)) at 1.
  unfold R.v8774, N.v8774.
  rewrite ?node_8583.
  rewrite ?node_8610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8775 (s : N.State) (i : N.Inputs) :
  R.v8775 (state s) (inputs i) = Zmod.unsigned (N.v8775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8775 s i)) at 1.
  unfold R.v8775, N.v8775.
  rewrite ?node_8611.
  rewrite ?node_8630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8776 (s : N.State) (i : N.Inputs) :
  R.v8776 (state s) (inputs i) = Zmod.unsigned (N.v8776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8776 s i)) at 1.
  unfold R.v8776, N.v8776.
  rewrite ?node_8774.
  rewrite ?node_8775.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8777 (s : N.State) (i : N.Inputs) :
  R.v8777 (state s) (inputs i) = Zmod.unsigned (N.v8777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8777 s i)) at 1.
  unfold R.v8777, N.v8777.
  rewrite ?node_8773.
  rewrite ?node_8776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8778 (s : N.State) (i : N.Inputs) :
  R.v8778 (state s) (inputs i) = Zmod.unsigned (N.v8778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8778 s i)) at 1.
  unfold R.v8778, N.v8778.
  rewrite ?node_8571.
  rewrite ?node_8578.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8779 (s : N.State) (i : N.Inputs) :
  R.v8779 (state s) (inputs i) = Zmod.unsigned (N.v8779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8779 s i)) at 1.
  unfold R.v8779, N.v8779.
  rewrite ?node_8579.
  rewrite ?node_8582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8780 (s : N.State) (i : N.Inputs) :
  R.v8780 (state s) (inputs i) = Zmod.unsigned (N.v8780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8780 s i)) at 1.
  unfold R.v8780, N.v8780.
  rewrite ?node_8778.
  rewrite ?node_8779.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8781 (s : N.State) (i : N.Inputs) :
  R.v8781 (state s) (inputs i) = Zmod.unsigned (N.v8781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8781 s i)) at 1.
  unfold R.v8781, N.v8781.
  rewrite ?node_8602.
  rewrite ?node_8605.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8782 (s : N.State) (i : N.Inputs) :
  R.v8782 (state s) (inputs i) = Zmod.unsigned (N.v8782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8782 s i)) at 1.
  unfold R.v8782, N.v8782.
  rewrite ?node_8606.
  rewrite ?node_8609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8783 (s : N.State) (i : N.Inputs) :
  R.v8783 (state s) (inputs i) = Zmod.unsigned (N.v8783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8783 s i)) at 1.
  unfold R.v8783, N.v8783.
  rewrite ?node_8781.
  rewrite ?node_8782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8784 (s : N.State) (i : N.Inputs) :
  R.v8784 (state s) (inputs i) = Zmod.unsigned (N.v8784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8784 s i)) at 1.
  unfold R.v8784, N.v8784.
  rewrite ?node_8780.
  rewrite ?node_8783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8785 (s : N.State) (i : N.Inputs) :
  R.v8785 (state s) (inputs i) = Zmod.unsigned (N.v8785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8785 s i)) at 1.
  unfold R.v8785, N.v8785.
  rewrite ?node_8622.
  rewrite ?node_8625.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8786 (s : N.State) (i : N.Inputs) :
  R.v8786 (state s) (inputs i) = Zmod.unsigned (N.v8786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8786 s i)) at 1.
  unfold R.v8786, N.v8786.
  rewrite ?node_8626.
  rewrite ?node_8629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8787 (s : N.State) (i : N.Inputs) :
  R.v8787 (state s) (inputs i) = Zmod.unsigned (N.v8787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8787 s i)) at 1.
  unfold R.v8787, N.v8787.
  rewrite ?node_8785.
  rewrite ?node_8786.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8788 (s : N.State) (i : N.Inputs) :
  R.v8788 (state s) (inputs i) = Zmod.unsigned (N.v8788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8788 s i)) at 1.
  unfold R.v8788, N.v8788.
  rewrite ?node_8784.
  rewrite ?node_8787.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8789 (s : N.State) (i : N.Inputs) :
  R.v8789 (state s) (inputs i) = Zmod.unsigned (N.v8789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8789 s i)) at 1.
  unfold R.v8789, N.v8789.
  rewrite ?node_8634.
  rewrite ?node_8637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8790 (s : N.State) (i : N.Inputs) :
  R.v8790 (state s) (inputs i) = Zmod.unsigned (N.v8790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8790 s i)) at 1.
  unfold R.v8790, N.v8790.
  rewrite ?node_8788.
  rewrite ?node_8789.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8791 (s : N.State) (i : N.Inputs) :
  R.v8791 (state s) (inputs i) = Zmod.unsigned (N.v8791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8791 s i)) at 1.
  unfold R.v8791, N.v8791.
  rewrite ?node_8646.
  rewrite ?node_8649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8792 (s : N.State) (i : N.Inputs) :
  R.v8792 (state s) (inputs i) = Zmod.unsigned (N.v8792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8792 s i)) at 1.
  unfold R.v8792, N.v8792.
  rewrite ?node_8650.
  rewrite ?node_8653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8793 (s : N.State) (i : N.Inputs) :
  R.v8793 (state s) (inputs i) = Zmod.unsigned (N.v8793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8793 s i)) at 1.
  unfold R.v8793, N.v8793.
  rewrite ?node_8791.
  rewrite ?node_8792.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8794 (s : N.State) (i : N.Inputs) :
  R.v8794 (state s) (inputs i) = Zmod.unsigned (N.v8794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8794 s i)) at 1.
  unfold R.v8794, N.v8794.
  rewrite ?node_8790.
  rewrite ?node_8793.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8795 (s : N.State) (i : N.Inputs) :
  R.v8795 (state s) (inputs i) = Zmod.unsigned (N.v8795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8795 s i)) at 1.
  unfold R.v8795, N.v8795.
  rewrite ?node_8777.
  rewrite ?node_8794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8796 (s : N.State) (i : N.Inputs) :
  R.v8796 (state s) (inputs i) = Zmod.unsigned (N.v8796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8796 s i)) at 1.
  unfold R.v8796, N.v8796.
  rewrite ?node_8631.
  rewrite ?node_8638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8797 (s : N.State) (i : N.Inputs) :
  R.v8797 (state s) (inputs i) = Zmod.unsigned (N.v8797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8797 s i)) at 1.
  unfold R.v8797, N.v8797.
  rewrite ?node_8639.
  rewrite ?node_8642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8798 (s : N.State) (i : N.Inputs) :
  R.v8798 (state s) (inputs i) = Zmod.unsigned (N.v8798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8798 s i)) at 1.
  unfold R.v8798, N.v8798.
  rewrite ?node_8796.
  rewrite ?node_8797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8799 (s : N.State) (i : N.Inputs) :
  R.v8799 (state s) (inputs i) = Zmod.unsigned (N.v8799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8799 s i)) at 1.
  unfold R.v8799, N.v8799.
  rewrite ?node_8795.
  rewrite ?node_8798.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8800 (s : N.State) (i : N.Inputs) :
  R.v8800 (state s) (inputs i) = Zmod.unsigned (N.v8800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8800 s i)) at 1.
  unfold R.v8800, N.v8800.
  rewrite ?node_8654.
  rewrite ?node_8655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8801 (s : N.State) (i : N.Inputs) :
  R.v8801 (state s) (inputs i) = Zmod.unsigned (N.v8801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8801 s i)) at 1.
  unfold R.v8801, N.v8801.
  rewrite ?node_8656.
  rewrite ?node_8659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8802 (s : N.State) (i : N.Inputs) :
  R.v8802 (state s) (inputs i) = Zmod.unsigned (N.v8802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8802 s i)) at 1.
  unfold R.v8802, N.v8802.
  rewrite ?node_8800.
  rewrite ?node_8801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8803 (s : N.State) (i : N.Inputs) :
  R.v8803 (state s) (inputs i) = Zmod.unsigned (N.v8803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8803 s i)) at 1.
  unfold R.v8803, N.v8803.
  rewrite ?node_8799.
  rewrite ?node_8802.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8804 (s : N.State) (i : N.Inputs) :
  R.v8804 (state s) (inputs i) = Zmod.unsigned (N.v8804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8804 s i)) at 1.
  unfold R.v8804, N.v8804.
  rewrite ?node_8643.
  rewrite ?node_8660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8805 (s : N.State) (i : N.Inputs) :
  R.v8805 (state s) (inputs i) = Zmod.unsigned (N.v8805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8805 s i)) at 1.
  unfold R.v8805, N.v8805.
  rewrite ?node_8661.
  rewrite ?node_8664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8806 (s : N.State) (i : N.Inputs) :
  R.v8806 (state s) (inputs i) = Zmod.unsigned (N.v8806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8806 s i)) at 1.
  unfold R.v8806, N.v8806.
  rewrite ?node_8804.
  rewrite ?node_8805.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8807 (s : N.State) (i : N.Inputs) :
  R.v8807 (state s) (inputs i) = Zmod.unsigned (N.v8807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8807 s i)) at 1.
  unfold R.v8807, N.v8807.
  rewrite ?node_8803.
  rewrite ?node_8806.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8808 (s : N.State) (i : N.Inputs) :
  R.v8808 (state s) (inputs i) = Zmod.unsigned (N.v8808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8808 s i)) at 1.
  unfold R.v8808, N.v8808.
  rewrite ?node_8665.
  rewrite ?node_8668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8809 (s : N.State) (i : N.Inputs) :
  R.v8809 (state s) (inputs i) = Zmod.unsigned (N.v8809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8809 s i)) at 1.
  unfold R.v8809, N.v8809.
  rewrite ?node_8669.
  rewrite ?node_8672.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8810 (s : N.State) (i : N.Inputs) :
  R.v8810 (state s) (inputs i) = Zmod.unsigned (N.v8810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8810 s i)) at 1.
  unfold R.v8810, N.v8810.
  rewrite ?node_8808.
  rewrite ?node_8809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8811 (s : N.State) (i : N.Inputs) :
  R.v8811 (state s) (inputs i) = Zmod.unsigned (N.v8811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8811 s i)) at 1.
  unfold R.v8811, N.v8811.
  rewrite ?node_8807.
  rewrite ?node_8810.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8812 (s : N.State) (i : N.Inputs) :
  R.v8812 (state s) (inputs i) = Zmod.unsigned (N.v8812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8812 s i)) at 1.
  unfold R.v8812, N.v8812.
  rewrite ?node_8811.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2379_nr_5F2410.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2379_nr_5F2410 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8813 (s : N.State) (i : N.Inputs) :
  R.v8813 (state s) (inputs i) = Zmod.unsigned (N.v8813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8813 s i)) at 1.
  unfold R.v8813, N.v8813.
  rewrite ?node_8673.
  rewrite ?node_8676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8814 (s : N.State) (i : N.Inputs) :
  R.v8814 (state s) (inputs i) = Zmod.unsigned (N.v8814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8814 s i)) at 1.
  unfold R.v8814, N.v8814.
  rewrite ?node_8813.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2380_nr_5F2411.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2380_nr_5F2411 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8815 (s : N.State) (i : N.Inputs) :
  R.v8815 (state s) (inputs i) = Zmod.unsigned (N.v8815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8815 s i)) at 1.
  unfold R.v8815, N.v8815.
  rewrite !state_r810_nr_5F810.
  rewrite !state_r811_nr_5F811.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r810_nr_5F810 s)).
  rewrite ?(bits.mod_to_Z (N.r811_nr_5F811 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8816 (s : N.State) (i : N.Inputs) :
  R.v8816 (state s) (inputs i) = Zmod.unsigned (N.v8816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8816 s i)) at 1.
  unfold R.v8816, N.v8816.
  rewrite ?node_8815.
  rewrite !state_r812_nr_5F812.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r812_nr_5F812 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8817 (s : N.State) (i : N.Inputs) :
  R.v8817 (state s) (inputs i) = Zmod.unsigned (N.v8817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8817 s i)) at 1.
  unfold R.v8817, N.v8817.
  rewrite ?node_8816.
  rewrite !state_r813_nr_5F813.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r813_nr_5F813 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8818 (s : N.State) (i : N.Inputs) :
  R.v8818 (state s) (inputs i) = Zmod.unsigned (N.v8818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8818 s i)) at 1.
  unfold R.v8818, N.v8818.
  rewrite !state_r782_nr_5F782.
  rewrite !state_r783_nr_5F783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r782_nr_5F782 s)).
  rewrite ?(bits.mod_to_Z (N.r783_nr_5F783 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8819 (s : N.State) (i : N.Inputs) :
  R.v8819 (state s) (inputs i) = Zmod.unsigned (N.v8819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8819 s i)) at 1.
  unfold R.v8819, N.v8819.
  rewrite ?node_8681.
  rewrite !state_r784_nr_5F784.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r784_nr_5F784 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8820 (s : N.State) (i : N.Inputs) :
  R.v8820 (state s) (inputs i) = Zmod.unsigned (N.v8820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8820 s i)) at 1.
  unfold R.v8820, N.v8820.
  rewrite ?node_8818.
  rewrite ?node_8819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8821 (s : N.State) (i : N.Inputs) :
  R.v8821 (state s) (inputs i) = Zmod.unsigned (N.v8821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8821 s i)) at 1.
  unfold R.v8821, N.v8821.
  rewrite ?node_8817.
  rewrite ?node_8820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8822 (s : N.State) (i : N.Inputs) :
  R.v8822 (state s) (inputs i) = Zmod.unsigned (N.v8822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8822 s i)) at 1.
  unfold R.v8822, N.v8822.
  rewrite !state_r814_nr_5F814.
  rewrite !state_r815_nr_5F815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r814_nr_5F814 s)).
  rewrite ?(bits.mod_to_Z (N.r815_nr_5F815 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8823 (s : N.State) (i : N.Inputs) :
  R.v8823 (state s) (inputs i) = Zmod.unsigned (N.v8823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8823 s i)) at 1.
  unfold R.v8823, N.v8823.
  rewrite ?node_8822.
  rewrite !state_r816_nr_5F816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r816_nr_5F816 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8824 (s : N.State) (i : N.Inputs) :
  R.v8824 (state s) (inputs i) = Zmod.unsigned (N.v8824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8824 s i)) at 1.
  unfold R.v8824, N.v8824.
  rewrite ?node_8823.
  rewrite !state_r817_nr_5F817.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r817_nr_5F817 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8825 (s : N.State) (i : N.Inputs) :
  R.v8825 (state s) (inputs i) = Zmod.unsigned (N.v8825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8825 s i)) at 1.
  unfold R.v8825, N.v8825.
  rewrite !state_r786_nr_5F786.
  rewrite !state_r787_nr_5F787.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r786_nr_5F786 s)).
  rewrite ?(bits.mod_to_Z (N.r787_nr_5F787 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8826 (s : N.State) (i : N.Inputs) :
  R.v8826 (state s) (inputs i) = Zmod.unsigned (N.v8826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8826 s i)) at 1.
  unfold R.v8826, N.v8826.
  rewrite ?node_8688.
  rewrite !state_r788_nr_5F788.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r788_nr_5F788 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8827 (s : N.State) (i : N.Inputs) :
  R.v8827 (state s) (inputs i) = Zmod.unsigned (N.v8827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8827 s i)) at 1.
  unfold R.v8827, N.v8827.
  rewrite ?node_8825.
  rewrite ?node_8826.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8828 (s : N.State) (i : N.Inputs) :
  R.v8828 (state s) (inputs i) = Zmod.unsigned (N.v8828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8828 s i)) at 1.
  unfold R.v8828, N.v8828.
  rewrite ?node_8824.
  rewrite ?node_8827.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8829 (s : N.State) (i : N.Inputs) :
  R.v8829 (state s) (inputs i) = Zmod.unsigned (N.v8829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8829 s i)) at 1.
  unfold R.v8829, N.v8829.
  rewrite ?node_8821.
  rewrite ?node_8828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8830 (s : N.State) (i : N.Inputs) :
  R.v8830 (state s) (inputs i) = Zmod.unsigned (N.v8830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8830 s i)) at 1.
  unfold R.v8830, N.v8830.
  rewrite !state_r818_nr_5F818.
  rewrite !state_r819_nr_5F819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r818_nr_5F818 s)).
  rewrite ?(bits.mod_to_Z (N.r819_nr_5F819 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8831 (s : N.State) (i : N.Inputs) :
  R.v8831 (state s) (inputs i) = Zmod.unsigned (N.v8831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8831 s i)) at 1.
  unfold R.v8831, N.v8831.
  rewrite ?node_8830.
  rewrite !state_r820_nr_5F820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r820_nr_5F820 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8832 (s : N.State) (i : N.Inputs) :
  R.v8832 (state s) (inputs i) = Zmod.unsigned (N.v8832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8832 s i)) at 1.
  unfold R.v8832, N.v8832.
  rewrite ?node_8831.
  rewrite !state_r821_nr_5F821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r821_nr_5F821 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8833 (s : N.State) (i : N.Inputs) :
  R.v8833 (state s) (inputs i) = Zmod.unsigned (N.v8833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8833 s i)) at 1.
  unfold R.v8833, N.v8833.
  rewrite !state_r790_nr_5F790.
  rewrite !state_r791_nr_5F791.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r790_nr_5F790 s)).
  rewrite ?(bits.mod_to_Z (N.r791_nr_5F791 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8834 (s : N.State) (i : N.Inputs) :
  R.v8834 (state s) (inputs i) = Zmod.unsigned (N.v8834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8834 s i)) at 1.
  unfold R.v8834, N.v8834.
  rewrite ?node_8696.
  rewrite !state_r792_nr_5F792.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r792_nr_5F792 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8835 (s : N.State) (i : N.Inputs) :
  R.v8835 (state s) (inputs i) = Zmod.unsigned (N.v8835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8835 s i)) at 1.
  unfold R.v8835, N.v8835.
  rewrite ?node_8833.
  rewrite ?node_8834.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8836 (s : N.State) (i : N.Inputs) :
  R.v8836 (state s) (inputs i) = Zmod.unsigned (N.v8836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8836 s i)) at 1.
  unfold R.v8836, N.v8836.
  rewrite ?node_8832.
  rewrite ?node_8835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8837 (s : N.State) (i : N.Inputs) :
  R.v8837 (state s) (inputs i) = Zmod.unsigned (N.v8837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8837 s i)) at 1.
  unfold R.v8837, N.v8837.
  rewrite ?node_8829.
  rewrite ?node_8836.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8838 (s : N.State) (i : N.Inputs) :
  R.v8838 (state s) (inputs i) = Zmod.unsigned (N.v8838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8838 s i)) at 1.
  unfold R.v8838, N.v8838.
  rewrite !state_r822_nr_5F822.
  rewrite !state_r823_nr_5F823.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r822_nr_5F822 s)).
  rewrite ?(bits.mod_to_Z (N.r823_nr_5F823 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8839 (s : N.State) (i : N.Inputs) :
  R.v8839 (state s) (inputs i) = Zmod.unsigned (N.v8839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8839 s i)) at 1.
  unfold R.v8839, N.v8839.
  rewrite ?node_8838.
  rewrite !state_r824_nr_5F824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r824_nr_5F824 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8840 (s : N.State) (i : N.Inputs) :
  R.v8840 (state s) (inputs i) = Zmod.unsigned (N.v8840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8840 s i)) at 1.
  unfold R.v8840, N.v8840.
  rewrite ?node_8839.
  rewrite !state_r825_nr_5F825.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r825_nr_5F825 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8841 (s : N.State) (i : N.Inputs) :
  R.v8841 (state s) (inputs i) = Zmod.unsigned (N.v8841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8841 s i)) at 1.
  unfold R.v8841, N.v8841.
  rewrite !state_r794_nr_5F794.
  rewrite !state_r795_nr_5F795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r794_nr_5F794 s)).
  rewrite ?(bits.mod_to_Z (N.r795_nr_5F795 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8842 (s : N.State) (i : N.Inputs) :
  R.v8842 (state s) (inputs i) = Zmod.unsigned (N.v8842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8842 s i)) at 1.
  unfold R.v8842, N.v8842.
  rewrite ?node_8704.
  rewrite !state_r796_nr_5F796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r796_nr_5F796 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8843 (s : N.State) (i : N.Inputs) :
  R.v8843 (state s) (inputs i) = Zmod.unsigned (N.v8843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8843 s i)) at 1.
  unfold R.v8843, N.v8843.
  rewrite ?node_8841.
  rewrite ?node_8842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8844 (s : N.State) (i : N.Inputs) :
  R.v8844 (state s) (inputs i) = Zmod.unsigned (N.v8844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8844 s i)) at 1.
  unfold R.v8844, N.v8844.
  rewrite ?node_8840.
  rewrite ?node_8843.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8845 (s : N.State) (i : N.Inputs) :
  R.v8845 (state s) (inputs i) = Zmod.unsigned (N.v8845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8845 s i)) at 1.
  unfold R.v8845, N.v8845.
  rewrite ?node_8837.
  rewrite ?node_8844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8846 (s : N.State) (i : N.Inputs) :
  R.v8846 (state s) (inputs i) = Zmod.unsigned (N.v8846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8846 s i)) at 1.
  unfold R.v8846, N.v8846.
  rewrite ?node_8687.
  rewrite ?node_8694.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8847 (s : N.State) (i : N.Inputs) :
  R.v8847 (state s) (inputs i) = Zmod.unsigned (N.v8847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8847 s i)) at 1.
  unfold R.v8847, N.v8847.
  rewrite ?node_8695.
  rewrite ?node_8702.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8848 (s : N.State) (i : N.Inputs) :
  R.v8848 (state s) (inputs i) = Zmod.unsigned (N.v8848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8848 s i)) at 1.
  unfold R.v8848, N.v8848.
  rewrite ?node_8846.
  rewrite ?node_8847.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8849 (s : N.State) (i : N.Inputs) :
  R.v8849 (state s) (inputs i) = Zmod.unsigned (N.v8849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8849 s i)) at 1.
  unfold R.v8849, N.v8849.
  rewrite ?node_8845.
  rewrite ?node_8848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8850 (s : N.State) (i : N.Inputs) :
  R.v8850 (state s) (inputs i) = Zmod.unsigned (N.v8850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8850 s i)) at 1.
  unfold R.v8850, N.v8850.
  rewrite !state_r826_nr_5F826.
  rewrite !state_r827_nr_5F827.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r826_nr_5F826 s)).
  rewrite ?(bits.mod_to_Z (N.r827_nr_5F827 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8851 (s : N.State) (i : N.Inputs) :
  R.v8851 (state s) (inputs i) = Zmod.unsigned (N.v8851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8851 s i)) at 1.
  unfold R.v8851, N.v8851.
  rewrite ?node_8850.
  rewrite !state_r828_nr_5F828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r828_nr_5F828 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8852 (s : N.State) (i : N.Inputs) :
  R.v8852 (state s) (inputs i) = Zmod.unsigned (N.v8852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8852 s i)) at 1.
  unfold R.v8852, N.v8852.
  rewrite ?node_8851.
  rewrite !state_r829_nr_5F829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r829_nr_5F829 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8853 (s : N.State) (i : N.Inputs) :
  R.v8853 (state s) (inputs i) = Zmod.unsigned (N.v8853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8853 s i)) at 1.
  unfold R.v8853, N.v8853.
  rewrite !state_r798_nr_5F798.
  rewrite !state_r799_nr_5F799.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r798_nr_5F798 s)).
  rewrite ?(bits.mod_to_Z (N.r799_nr_5F799 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8854 (s : N.State) (i : N.Inputs) :
  R.v8854 (state s) (inputs i) = Zmod.unsigned (N.v8854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8854 s i)) at 1.
  unfold R.v8854, N.v8854.
  rewrite ?node_8716.
  rewrite !state_r800_nr_5F800.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r800_nr_5F800 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8855 (s : N.State) (i : N.Inputs) :
  R.v8855 (state s) (inputs i) = Zmod.unsigned (N.v8855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8855 s i)) at 1.
  unfold R.v8855, N.v8855.
  rewrite ?node_8853.
  rewrite ?node_8854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8856 (s : N.State) (i : N.Inputs) :
  R.v8856 (state s) (inputs i) = Zmod.unsigned (N.v8856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8856 s i)) at 1.
  unfold R.v8856, N.v8856.
  rewrite ?node_8852.
  rewrite ?node_8855.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8857 (s : N.State) (i : N.Inputs) :
  R.v8857 (state s) (inputs i) = Zmod.unsigned (N.v8857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8857 s i)) at 1.
  unfold R.v8857, N.v8857.
  rewrite !state_r830_nr_5F830.
  rewrite !state_r831_nr_5F831.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r830_nr_5F830 s)).
  rewrite ?(bits.mod_to_Z (N.r831_nr_5F831 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8858 (s : N.State) (i : N.Inputs) :
  R.v8858 (state s) (inputs i) = Zmod.unsigned (N.v8858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8858 s i)) at 1.
  unfold R.v8858, N.v8858.
  rewrite ?node_8857.
  rewrite !state_r832_nr_5F832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r832_nr_5F832 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8859 (s : N.State) (i : N.Inputs) :
  R.v8859 (state s) (inputs i) = Zmod.unsigned (N.v8859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8859 s i)) at 1.
  unfold R.v8859, N.v8859.
  rewrite ?node_8858.
  rewrite !state_r833_nr_5F833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r833_nr_5F833 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8860 (s : N.State) (i : N.Inputs) :
  R.v8860 (state s) (inputs i) = Zmod.unsigned (N.v8860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8860 s i)) at 1.
  unfold R.v8860, N.v8860.
  rewrite !state_r802_nr_5F802.
  rewrite !state_r803_nr_5F803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r802_nr_5F802 s)).
  rewrite ?(bits.mod_to_Z (N.r803_nr_5F803 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8861 (s : N.State) (i : N.Inputs) :
  R.v8861 (state s) (inputs i) = Zmod.unsigned (N.v8861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8861 s i)) at 1.
  unfold R.v8861, N.v8861.
  rewrite ?node_8723.
  rewrite !state_r804_nr_5F804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r804_nr_5F804 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8862 (s : N.State) (i : N.Inputs) :
  R.v8862 (state s) (inputs i) = Zmod.unsigned (N.v8862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8862 s i)) at 1.
  unfold R.v8862, N.v8862.
  rewrite ?node_8860.
  rewrite ?node_8861.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8863 (s : N.State) (i : N.Inputs) :
  R.v8863 (state s) (inputs i) = Zmod.unsigned (N.v8863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8863 s i)) at 1.
  unfold R.v8863, N.v8863.
  rewrite ?node_8859.
  rewrite ?node_8862.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8864 (s : N.State) (i : N.Inputs) :
  R.v8864 (state s) (inputs i) = Zmod.unsigned (N.v8864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8864 s i)) at 1.
  unfold R.v8864, N.v8864.
  rewrite ?node_8856.
  rewrite ?node_8863.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8865 (s : N.State) (i : N.Inputs) :
  R.v8865 (state s) (inputs i) = Zmod.unsigned (N.v8865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8865 s i)) at 1.
  unfold R.v8865, N.v8865.
  rewrite !state_r834_nr_5F834.
  rewrite !state_r835_nr_5F835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r834_nr_5F834 s)).
  rewrite ?(bits.mod_to_Z (N.r835_nr_5F835 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8866 (s : N.State) (i : N.Inputs) :
  R.v8866 (state s) (inputs i) = Zmod.unsigned (N.v8866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8866 s i)) at 1.
  unfold R.v8866, N.v8866.
  rewrite ?node_8865.
  rewrite !state_r836_nr_5F836.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r836_nr_5F836 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8867 (s : N.State) (i : N.Inputs) :
  R.v8867 (state s) (inputs i) = Zmod.unsigned (N.v8867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8867 s i)) at 1.
  unfold R.v8867, N.v8867.
  rewrite ?node_8866.
  rewrite !state_r837_nr_5F837.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r837_nr_5F837 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8868 (s : N.State) (i : N.Inputs) :
  R.v8868 (state s) (inputs i) = Zmod.unsigned (N.v8868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8868 s i)) at 1.
  unfold R.v8868, N.v8868.
  rewrite !state_r806_nr_5F806.
  rewrite !state_r807_nr_5F807.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r806_nr_5F806 s)).
  rewrite ?(bits.mod_to_Z (N.r807_nr_5F807 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8869 (s : N.State) (i : N.Inputs) :
  R.v8869 (state s) (inputs i) = Zmod.unsigned (N.v8869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8869 s i)) at 1.
  unfold R.v8869, N.v8869.
  rewrite ?node_8731.
  rewrite !state_r808_nr_5F808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r808_nr_5F808 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8870 (s : N.State) (i : N.Inputs) :
  R.v8870 (state s) (inputs i) = Zmod.unsigned (N.v8870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8870 s i)) at 1.
  unfold R.v8870, N.v8870.
  rewrite ?node_8868.
  rewrite ?node_8869.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8871 (s : N.State) (i : N.Inputs) :
  R.v8871 (state s) (inputs i) = Zmod.unsigned (N.v8871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8871 s i)) at 1.
  unfold R.v8871, N.v8871.
  rewrite ?node_8867.
  rewrite ?node_8870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8872 (s : N.State) (i : N.Inputs) :
  R.v8872 (state s) (inputs i) = Zmod.unsigned (N.v8872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8872 s i)) at 1.
  unfold R.v8872, N.v8872.
  rewrite ?node_8864.
  rewrite ?node_8871.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8873 (s : N.State) (i : N.Inputs) :
  R.v8873 (state s) (inputs i) = Zmod.unsigned (N.v8873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8873 s i)) at 1.
  unfold R.v8873, N.v8873.
  rewrite ?node_8872.
  rewrite !state_r838_nr_5F838.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r838_nr_5F838 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8874 (s : N.State) (i : N.Inputs) :
  R.v8874 (state s) (inputs i) = Zmod.unsigned (N.v8874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8874 s i)) at 1.
  unfold R.v8874, N.v8874.
  rewrite ?node_8722.
  rewrite ?node_8729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8875 (s : N.State) (i : N.Inputs) :
  R.v8875 (state s) (inputs i) = Zmod.unsigned (N.v8875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8875 s i)) at 1.
  unfold R.v8875, N.v8875.
  rewrite ?node_8730.
  rewrite ?node_8737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8876 (s : N.State) (i : N.Inputs) :
  R.v8876 (state s) (inputs i) = Zmod.unsigned (N.v8876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8876 s i)) at 1.
  unfold R.v8876, N.v8876.
  rewrite ?node_8874.
  rewrite ?node_8875.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8877 (s : N.State) (i : N.Inputs) :
  R.v8877 (state s) (inputs i) = Zmod.unsigned (N.v8877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8877 s i)) at 1.
  unfold R.v8877, N.v8877.
  rewrite ?node_8873.
  rewrite ?node_8876.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8878 (s : N.State) (i : N.Inputs) :
  R.v8878 (state s) (inputs i) = Zmod.unsigned (N.v8878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8878 s i)) at 1.
  unfold R.v8878, N.v8878.
  rewrite ?node_8849.
  rewrite ?node_8877.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8879 (s : N.State) (i : N.Inputs) :
  R.v8879 (state s) (inputs i) = Zmod.unsigned (N.v8879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8879 s i)) at 1.
  unfold R.v8879, N.v8879.
  rewrite ?node_8682.
  rewrite !state_r785_nr_5F785.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r785_nr_5F785 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8880 (s : N.State) (i : N.Inputs) :
  R.v8880 (state s) (inputs i) = Zmod.unsigned (N.v8880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8880 s i)) at 1.
  unfold R.v8880, N.v8880.
  rewrite ?node_8683.
  rewrite ?node_8686.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8881 (s : N.State) (i : N.Inputs) :
  R.v8881 (state s) (inputs i) = Zmod.unsigned (N.v8881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8881 s i)) at 1.
  unfold R.v8881, N.v8881.
  rewrite ?node_8879.
  rewrite ?node_8880.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8882 (s : N.State) (i : N.Inputs) :
  R.v8882 (state s) (inputs i) = Zmod.unsigned (N.v8882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8882 s i)) at 1.
  unfold R.v8882, N.v8882.
  rewrite ?node_8689.
  rewrite !state_r789_nr_5F789.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r789_nr_5F789 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8883 (s : N.State) (i : N.Inputs) :
  R.v8883 (state s) (inputs i) = Zmod.unsigned (N.v8883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8883 s i)) at 1.
  unfold R.v8883, N.v8883.
  rewrite ?node_8690.
  rewrite ?node_8693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8884 (s : N.State) (i : N.Inputs) :
  R.v8884 (state s) (inputs i) = Zmod.unsigned (N.v8884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8884 s i)) at 1.
  unfold R.v8884, N.v8884.
  rewrite ?node_8882.
  rewrite ?node_8883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8885 (s : N.State) (i : N.Inputs) :
  R.v8885 (state s) (inputs i) = Zmod.unsigned (N.v8885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8885 s i)) at 1.
  unfold R.v8885, N.v8885.
  rewrite ?node_8881.
  rewrite ?node_8884.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8886 (s : N.State) (i : N.Inputs) :
  R.v8886 (state s) (inputs i) = Zmod.unsigned (N.v8886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8886 s i)) at 1.
  unfold R.v8886, N.v8886.
  rewrite ?node_8697.
  rewrite !state_r793_nr_5F793.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r793_nr_5F793 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8887 (s : N.State) (i : N.Inputs) :
  R.v8887 (state s) (inputs i) = Zmod.unsigned (N.v8887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8887 s i)) at 1.
  unfold R.v8887, N.v8887.
  rewrite ?node_8698.
  rewrite ?node_8701.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8888 (s : N.State) (i : N.Inputs) :
  R.v8888 (state s) (inputs i) = Zmod.unsigned (N.v8888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8888 s i)) at 1.
  unfold R.v8888, N.v8888.
  rewrite ?node_8886.
  rewrite ?node_8887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8889 (s : N.State) (i : N.Inputs) :
  R.v8889 (state s) (inputs i) = Zmod.unsigned (N.v8889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8889 s i)) at 1.
  unfold R.v8889, N.v8889.
  rewrite ?node_8885.
  rewrite ?node_8888.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8890 (s : N.State) (i : N.Inputs) :
  R.v8890 (state s) (inputs i) = Zmod.unsigned (N.v8890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8890 s i)) at 1.
  unfold R.v8890, N.v8890.
  rewrite ?node_8705.
  rewrite !state_r797_nr_5F797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r797_nr_5F797 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8891 (s : N.State) (i : N.Inputs) :
  R.v8891 (state s) (inputs i) = Zmod.unsigned (N.v8891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8891 s i)) at 1.
  unfold R.v8891, N.v8891.
  rewrite ?node_8706.
  rewrite ?node_8709.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8892 (s : N.State) (i : N.Inputs) :
  R.v8892 (state s) (inputs i) = Zmod.unsigned (N.v8892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8892 s i)) at 1.
  unfold R.v8892, N.v8892.
  rewrite ?node_8890.
  rewrite ?node_8891.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8893 (s : N.State) (i : N.Inputs) :
  R.v8893 (state s) (inputs i) = Zmod.unsigned (N.v8893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8893 s i)) at 1.
  unfold R.v8893, N.v8893.
  rewrite ?node_8889.
  rewrite ?node_8892.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8894 (s : N.State) (i : N.Inputs) :
  R.v8894 (state s) (inputs i) = Zmod.unsigned (N.v8894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8894 s i)) at 1.
  unfold R.v8894, N.v8894.
  rewrite ?node_8750.
  rewrite ?node_8753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8895 (s : N.State) (i : N.Inputs) :
  R.v8895 (state s) (inputs i) = Zmod.unsigned (N.v8895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8895 s i)) at 1.
  unfold R.v8895, N.v8895.
  rewrite ?node_8754.
  rewrite ?node_8757.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8896 (s : N.State) (i : N.Inputs) :
  R.v8896 (state s) (inputs i) = Zmod.unsigned (N.v8896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8896 s i)) at 1.
  unfold R.v8896, N.v8896.
  rewrite ?node_8894.
  rewrite ?node_8895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8897 (s : N.State) (i : N.Inputs) :
  R.v8897 (state s) (inputs i) = Zmod.unsigned (N.v8897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8897 s i)) at 1.
  unfold R.v8897, N.v8897.
  rewrite ?node_8893.
  rewrite ?node_8896.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8898 (s : N.State) (i : N.Inputs) :
  R.v8898 (state s) (inputs i) = Zmod.unsigned (N.v8898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8898 s i)) at 1.
  unfold R.v8898, N.v8898.
  rewrite ?node_8878.
  rewrite ?node_8897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8899 (s : N.State) (i : N.Inputs) :
  R.v8899 (state s) (inputs i) = Zmod.unsigned (N.v8899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8899 s i)) at 1.
  unfold R.v8899, N.v8899.
  rewrite ?node_8717.
  rewrite !state_r801_nr_5F801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r801_nr_5F801 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8900 (s : N.State) (i : N.Inputs) :
  R.v8900 (state s) (inputs i) = Zmod.unsigned (N.v8900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8900 s i)) at 1.
  unfold R.v8900, N.v8900.
  rewrite ?node_8718.
  rewrite ?node_8721.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8901 (s : N.State) (i : N.Inputs) :
  R.v8901 (state s) (inputs i) = Zmod.unsigned (N.v8901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8901 s i)) at 1.
  unfold R.v8901, N.v8901.
  rewrite ?node_8899.
  rewrite ?node_8900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8902 (s : N.State) (i : N.Inputs) :
  R.v8902 (state s) (inputs i) = Zmod.unsigned (N.v8902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8902 s i)) at 1.
  unfold R.v8902, N.v8902.
  rewrite ?node_8724.
  rewrite !state_r805_nr_5F805.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r805_nr_5F805 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8903 (s : N.State) (i : N.Inputs) :
  R.v8903 (state s) (inputs i) = Zmod.unsigned (N.v8903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8903 s i)) at 1.
  unfold R.v8903, N.v8903.
  rewrite ?node_8725.
  rewrite ?node_8728.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8904 (s : N.State) (i : N.Inputs) :
  R.v8904 (state s) (inputs i) = Zmod.unsigned (N.v8904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8904 s i)) at 1.
  unfold R.v8904, N.v8904.
  rewrite ?node_8902.
  rewrite ?node_8903.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8905 (s : N.State) (i : N.Inputs) :
  R.v8905 (state s) (inputs i) = Zmod.unsigned (N.v8905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8905 s i)) at 1.
  unfold R.v8905, N.v8905.
  rewrite ?node_8901.
  rewrite ?node_8904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8906 (s : N.State) (i : N.Inputs) :
  R.v8906 (state s) (inputs i) = Zmod.unsigned (N.v8906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8906 s i)) at 1.
  unfold R.v8906, N.v8906.
  rewrite ?node_8732.
  rewrite !state_r809_nr_5F809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r809_nr_5F809 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8907 (s : N.State) (i : N.Inputs) :
  R.v8907 (state s) (inputs i) = Zmod.unsigned (N.v8907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8907 s i)) at 1.
  unfold R.v8907, N.v8907.
  rewrite ?node_8733.
  rewrite ?node_8736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8908 (s : N.State) (i : N.Inputs) :
  R.v8908 (state s) (inputs i) = Zmod.unsigned (N.v8908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8908 s i)) at 1.
  unfold R.v8908, N.v8908.
  rewrite ?node_8906.
  rewrite ?node_8907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8909 (s : N.State) (i : N.Inputs) :
  R.v8909 (state s) (inputs i) = Zmod.unsigned (N.v8909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8909 s i)) at 1.
  unfold R.v8909, N.v8909.
  rewrite ?node_8905.
  rewrite ?node_8908.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8910 (s : N.State) (i : N.Inputs) :
  R.v8910 (state s) (inputs i) = Zmod.unsigned (N.v8910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8910 s i)) at 1.
  unfold R.v8910, N.v8910.
  rewrite ?node_8898.
  rewrite ?node_8909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8911 (s : N.State) (i : N.Inputs) :
  R.v8911 (state s) (inputs i) = Zmod.unsigned (N.v8911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8911 s i)) at 1.
  unfold R.v8911, N.v8911.
  rewrite ?node_8715.
  rewrite ?node_8746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8912 (s : N.State) (i : N.Inputs) :
  R.v8912 (state s) (inputs i) = Zmod.unsigned (N.v8912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8912 s i)) at 1.
  unfold R.v8912, N.v8912.
  rewrite ?node_8747.
  rewrite ?node_8766.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8913 (s : N.State) (i : N.Inputs) :
  R.v8913 (state s) (inputs i) = Zmod.unsigned (N.v8913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8913 s i)) at 1.
  unfold R.v8913, N.v8913.
  rewrite ?node_8911.
  rewrite ?node_8912.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8914 (s : N.State) (i : N.Inputs) :
  R.v8914 (state s) (inputs i) = Zmod.unsigned (N.v8914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8914 s i)) at 1.
  unfold R.v8914, N.v8914.
  rewrite ?node_8910.
  rewrite ?node_8913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8915 (s : N.State) (i : N.Inputs) :
  R.v8915 (state s) (inputs i) = Zmod.unsigned (N.v8915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8915 s i)) at 1.
  unfold R.v8915, N.v8915.
  rewrite ?node_8703.
  rewrite ?node_8710.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8916 (s : N.State) (i : N.Inputs) :
  R.v8916 (state s) (inputs i) = Zmod.unsigned (N.v8916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8916 s i)) at 1.
  unfold R.v8916, N.v8916.
  rewrite ?node_8711.
  rewrite ?node_8714.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8917 (s : N.State) (i : N.Inputs) :
  R.v8917 (state s) (inputs i) = Zmod.unsigned (N.v8917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8917 s i)) at 1.
  unfold R.v8917, N.v8917.
  rewrite ?node_8915.
  rewrite ?node_8916.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8918 (s : N.State) (i : N.Inputs) :
  R.v8918 (state s) (inputs i) = Zmod.unsigned (N.v8918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8918 s i)) at 1.
  unfold R.v8918, N.v8918.
  rewrite ?node_8738.
  rewrite ?node_8741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8919 (s : N.State) (i : N.Inputs) :
  R.v8919 (state s) (inputs i) = Zmod.unsigned (N.v8919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8919 s i)) at 1.
  unfold R.v8919, N.v8919.
  rewrite ?node_8742.
  rewrite ?node_8745.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8920 (s : N.State) (i : N.Inputs) :
  R.v8920 (state s) (inputs i) = Zmod.unsigned (N.v8920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8920 s i)) at 1.
  unfold R.v8920, N.v8920.
  rewrite ?node_8918.
  rewrite ?node_8919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8921 (s : N.State) (i : N.Inputs) :
  R.v8921 (state s) (inputs i) = Zmod.unsigned (N.v8921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8921 s i)) at 1.
  unfold R.v8921, N.v8921.
  rewrite ?node_8917.
  rewrite ?node_8920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8922 (s : N.State) (i : N.Inputs) :
  R.v8922 (state s) (inputs i) = Zmod.unsigned (N.v8922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8922 s i)) at 1.
  unfold R.v8922, N.v8922.
  rewrite ?node_8758.
  rewrite ?node_8761.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8923 (s : N.State) (i : N.Inputs) :
  R.v8923 (state s) (inputs i) = Zmod.unsigned (N.v8923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8923 s i)) at 1.
  unfold R.v8923, N.v8923.
  rewrite ?node_8762.
  rewrite ?node_8765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8924 (s : N.State) (i : N.Inputs) :
  R.v8924 (state s) (inputs i) = Zmod.unsigned (N.v8924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8924 s i)) at 1.
  unfold R.v8924, N.v8924.
  rewrite ?node_8922.
  rewrite ?node_8923.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8925 (s : N.State) (i : N.Inputs) :
  R.v8925 (state s) (inputs i) = Zmod.unsigned (N.v8925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8925 s i)) at 1.
  unfold R.v8925, N.v8925.
  rewrite ?node_8921.
  rewrite ?node_8924.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8926 (s : N.State) (i : N.Inputs) :
  R.v8926 (state s) (inputs i) = Zmod.unsigned (N.v8926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8926 s i)) at 1.
  unfold R.v8926, N.v8926.
  rewrite ?node_8770.
  rewrite ?node_8771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8927 (s : N.State) (i : N.Inputs) :
  R.v8927 (state s) (inputs i) = Zmod.unsigned (N.v8927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8927 s i)) at 1.
  unfold R.v8927, N.v8927.
  rewrite ?node_8925.
  rewrite ?node_8926.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8928 (s : N.State) (i : N.Inputs) :
  R.v8928 (state s) (inputs i) = Zmod.unsigned (N.v8928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8928 s i)) at 1.
  unfold R.v8928, N.v8928.
  rewrite ?node_8780.
  rewrite ?node_8783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8929 (s : N.State) (i : N.Inputs) :
  R.v8929 (state s) (inputs i) = Zmod.unsigned (N.v8929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8929 s i)) at 1.
  unfold R.v8929, N.v8929.
  rewrite ?node_8784.
  rewrite ?node_8787.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8930 (s : N.State) (i : N.Inputs) :
  R.v8930 (state s) (inputs i) = Zmod.unsigned (N.v8930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8930 s i)) at 1.
  unfold R.v8930, N.v8930.
  rewrite ?node_8928.
  rewrite ?node_8929.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8931 (s : N.State) (i : N.Inputs) :
  R.v8931 (state s) (inputs i) = Zmod.unsigned (N.v8931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8931 s i)) at 1.
  unfold R.v8931, N.v8931.
  rewrite ?node_8927.
  rewrite ?node_8930.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8932 (s : N.State) (i : N.Inputs) :
  R.v8932 (state s) (inputs i) = Zmod.unsigned (N.v8932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8932 s i)) at 1.
  unfold R.v8932, N.v8932.
  rewrite ?node_8914.
  rewrite ?node_8931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8933 (s : N.State) (i : N.Inputs) :
  R.v8933 (state s) (inputs i) = Zmod.unsigned (N.v8933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8933 s i)) at 1.
  unfold R.v8933, N.v8933.
  rewrite ?node_8767.
  rewrite ?node_8772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8934 (s : N.State) (i : N.Inputs) :
  R.v8934 (state s) (inputs i) = Zmod.unsigned (N.v8934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8934 s i)) at 1.
  unfold R.v8934, N.v8934.
  rewrite ?node_8773.
  rewrite ?node_8776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8935 (s : N.State) (i : N.Inputs) :
  R.v8935 (state s) (inputs i) = Zmod.unsigned (N.v8935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8935 s i)) at 1.
  unfold R.v8935, N.v8935.
  rewrite ?node_8933.
  rewrite ?node_8934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8936 (s : N.State) (i : N.Inputs) :
  R.v8936 (state s) (inputs i) = Zmod.unsigned (N.v8936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8936 s i)) at 1.
  unfold R.v8936, N.v8936.
  rewrite ?node_8932.
  rewrite ?node_8935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8937 (s : N.State) (i : N.Inputs) :
  R.v8937 (state s) (inputs i) = Zmod.unsigned (N.v8937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8937 s i)) at 1.
  unfold R.v8937, N.v8937.
  rewrite ?node_8788.
  rewrite ?node_8789.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8938 (s : N.State) (i : N.Inputs) :
  R.v8938 (state s) (inputs i) = Zmod.unsigned (N.v8938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8938 s i)) at 1.
  unfold R.v8938, N.v8938.
  rewrite ?node_8790.
  rewrite ?node_8793.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8939 (s : N.State) (i : N.Inputs) :
  R.v8939 (state s) (inputs i) = Zmod.unsigned (N.v8939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8939 s i)) at 1.
  unfold R.v8939, N.v8939.
  rewrite ?node_8937.
  rewrite ?node_8938.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8940 (s : N.State) (i : N.Inputs) :
  R.v8940 (state s) (inputs i) = Zmod.unsigned (N.v8940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8940 s i)) at 1.
  unfold R.v8940, N.v8940.
  rewrite ?node_8936.
  rewrite ?node_8939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8941 (s : N.State) (i : N.Inputs) :
  R.v8941 (state s) (inputs i) = Zmod.unsigned (N.v8941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8941 s i)) at 1.
  unfold R.v8941, N.v8941.
  rewrite ?node_8777.
  rewrite ?node_8794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8942 (s : N.State) (i : N.Inputs) :
  R.v8942 (state s) (inputs i) = Zmod.unsigned (N.v8942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8942 s i)) at 1.
  unfold R.v8942, N.v8942.
  rewrite ?node_8795.
  rewrite ?node_8798.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8943 (s : N.State) (i : N.Inputs) :
  R.v8943 (state s) (inputs i) = Zmod.unsigned (N.v8943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8943 s i)) at 1.
  unfold R.v8943, N.v8943.
  rewrite ?node_8941.
  rewrite ?node_8942.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8944 (s : N.State) (i : N.Inputs) :
  R.v8944 (state s) (inputs i) = Zmod.unsigned (N.v8944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8944 s i)) at 1.
  unfold R.v8944, N.v8944.
  rewrite ?node_8940.
  rewrite ?node_8943.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8945 (s : N.State) (i : N.Inputs) :
  R.v8945 (state s) (inputs i) = Zmod.unsigned (N.v8945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8945 s i)) at 1.
  unfold R.v8945, N.v8945.
  rewrite ?node_8799.
  rewrite ?node_8802.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8946 (s : N.State) (i : N.Inputs) :
  R.v8946 (state s) (inputs i) = Zmod.unsigned (N.v8946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8946 s i)) at 1.
  unfold R.v8946, N.v8946.
  rewrite ?node_8803.
  rewrite ?node_8806.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8947 (s : N.State) (i : N.Inputs) :
  R.v8947 (state s) (inputs i) = Zmod.unsigned (N.v8947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8947 s i)) at 1.
  unfold R.v8947, N.v8947.
  rewrite ?node_8945.
  rewrite ?node_8946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8948 (s : N.State) (i : N.Inputs) :
  R.v8948 (state s) (inputs i) = Zmod.unsigned (N.v8948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8948 s i)) at 1.
  unfold R.v8948, N.v8948.
  rewrite ?node_8944.
  rewrite ?node_8947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8949 (s : N.State) (i : N.Inputs) :
  R.v8949 (state s) (inputs i) = Zmod.unsigned (N.v8949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8949 s i)) at 1.
  unfold R.v8949, N.v8949.
  rewrite ?node_8948.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2381_nr_5F2412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2381_nr_5F2412 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8950 (s : N.State) (i : N.Inputs) :
  R.v8950 (state s) (inputs i) = Zmod.unsigned (N.v8950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8950 s i)) at 1.
  unfold R.v8950, N.v8950.
  rewrite ?node_8807.
  rewrite ?node_8810.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8951 (s : N.State) (i : N.Inputs) :
  R.v8951 (state s) (inputs i) = Zmod.unsigned (N.v8951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8951 s i)) at 1.
  unfold R.v8951, N.v8951.
  rewrite ?node_8950.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2382_nr_5F2413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2382_nr_5F2413 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8952 (s : N.State) (i : N.Inputs) :
  R.v8952 (state s) (inputs i) = Zmod.unsigned (N.v8952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8952 s i)) at 1.
  unfold R.v8952, N.v8952.
  rewrite !state_r839_nr_5F839.
  rewrite !state_r840_nr_5F840.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r839_nr_5F839 s)).
  rewrite ?(bits.mod_to_Z (N.r840_nr_5F840 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8953 (s : N.State) (i : N.Inputs) :
  R.v8953 (state s) (inputs i) = Zmod.unsigned (N.v8953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8953 s i)) at 1.
  unfold R.v8953, N.v8953.
  rewrite ?node_8952.
  rewrite !state_r841_nr_5F841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r841_nr_5F841 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8954 (s : N.State) (i : N.Inputs) :
  R.v8954 (state s) (inputs i) = Zmod.unsigned (N.v8954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8954 s i)) at 1.
  unfold R.v8954, N.v8954.
  rewrite ?node_8953.
  rewrite !state_r842_nr_5F842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r842_nr_5F842 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8955 (s : N.State) (i : N.Inputs) :
  R.v8955 (state s) (inputs i) = Zmod.unsigned (N.v8955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8955 s i)) at 1.
  unfold R.v8955, N.v8955.
  rewrite !state_r810_nr_5F810.
  rewrite !state_r811_nr_5F811.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r810_nr_5F810 s)).
  rewrite ?(bits.mod_to_Z (N.r811_nr_5F811 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8956 (s : N.State) (i : N.Inputs) :
  R.v8956 (state s) (inputs i) = Zmod.unsigned (N.v8956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8956 s i)) at 1.
  unfold R.v8956, N.v8956.
  rewrite ?node_8815.
  rewrite !state_r812_nr_5F812.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r812_nr_5F812 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8957 (s : N.State) (i : N.Inputs) :
  R.v8957 (state s) (inputs i) = Zmod.unsigned (N.v8957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8957 s i)) at 1.
  unfold R.v8957, N.v8957.
  rewrite ?node_8955.
  rewrite ?node_8956.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8958 (s : N.State) (i : N.Inputs) :
  R.v8958 (state s) (inputs i) = Zmod.unsigned (N.v8958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8958 s i)) at 1.
  unfold R.v8958, N.v8958.
  rewrite ?node_8954.
  rewrite ?node_8957.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8959 (s : N.State) (i : N.Inputs) :
  R.v8959 (state s) (inputs i) = Zmod.unsigned (N.v8959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8959 s i)) at 1.
  unfold R.v8959, N.v8959.
  rewrite !state_r843_nr_5F843.
  rewrite !state_r844_nr_5F844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r843_nr_5F843 s)).
  rewrite ?(bits.mod_to_Z (N.r844_nr_5F844 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8960 (s : N.State) (i : N.Inputs) :
  R.v8960 (state s) (inputs i) = Zmod.unsigned (N.v8960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8960 s i)) at 1.
  unfold R.v8960, N.v8960.
  rewrite ?node_8959.
  rewrite !state_r845_nr_5F845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r845_nr_5F845 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8961 (s : N.State) (i : N.Inputs) :
  R.v8961 (state s) (inputs i) = Zmod.unsigned (N.v8961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8961 s i)) at 1.
  unfold R.v8961, N.v8961.
  rewrite ?node_8960.
  rewrite !state_r846_nr_5F846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r846_nr_5F846 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8962 (s : N.State) (i : N.Inputs) :
  R.v8962 (state s) (inputs i) = Zmod.unsigned (N.v8962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8962 s i)) at 1.
  unfold R.v8962, N.v8962.
  rewrite !state_r814_nr_5F814.
  rewrite !state_r815_nr_5F815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r814_nr_5F814 s)).
  rewrite ?(bits.mod_to_Z (N.r815_nr_5F815 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8963 (s : N.State) (i : N.Inputs) :
  R.v8963 (state s) (inputs i) = Zmod.unsigned (N.v8963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8963 s i)) at 1.
  unfold R.v8963, N.v8963.
  rewrite ?node_8822.
  rewrite !state_r816_nr_5F816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r816_nr_5F816 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8964 (s : N.State) (i : N.Inputs) :
  R.v8964 (state s) (inputs i) = Zmod.unsigned (N.v8964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8964 s i)) at 1.
  unfold R.v8964, N.v8964.
  rewrite ?node_8962.
  rewrite ?node_8963.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8965 (s : N.State) (i : N.Inputs) :
  R.v8965 (state s) (inputs i) = Zmod.unsigned (N.v8965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8965 s i)) at 1.
  unfold R.v8965, N.v8965.
  rewrite ?node_8961.
  rewrite ?node_8964.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8966 (s : N.State) (i : N.Inputs) :
  R.v8966 (state s) (inputs i) = Zmod.unsigned (N.v8966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8966 s i)) at 1.
  unfold R.v8966, N.v8966.
  rewrite ?node_8958.
  rewrite ?node_8965.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8967 (s : N.State) (i : N.Inputs) :
  R.v8967 (state s) (inputs i) = Zmod.unsigned (N.v8967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8967 s i)) at 1.
  unfold R.v8967, N.v8967.
  rewrite !state_r847_nr_5F847.
  rewrite !state_r848_nr_5F848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r847_nr_5F847 s)).
  rewrite ?(bits.mod_to_Z (N.r848_nr_5F848 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8968 (s : N.State) (i : N.Inputs) :
  R.v8968 (state s) (inputs i) = Zmod.unsigned (N.v8968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8968 s i)) at 1.
  unfold R.v8968, N.v8968.
  rewrite ?node_8967.
  rewrite !state_r849_nr_5F849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r849_nr_5F849 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8969 (s : N.State) (i : N.Inputs) :
  R.v8969 (state s) (inputs i) = Zmod.unsigned (N.v8969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8969 s i)) at 1.
  unfold R.v8969, N.v8969.
  rewrite ?node_8968.
  rewrite !state_r850_nr_5F850.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r850_nr_5F850 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8970 (s : N.State) (i : N.Inputs) :
  R.v8970 (state s) (inputs i) = Zmod.unsigned (N.v8970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8970 s i)) at 1.
  unfold R.v8970, N.v8970.
  rewrite !state_r818_nr_5F818.
  rewrite !state_r819_nr_5F819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r818_nr_5F818 s)).
  rewrite ?(bits.mod_to_Z (N.r819_nr_5F819 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8971 (s : N.State) (i : N.Inputs) :
  R.v8971 (state s) (inputs i) = Zmod.unsigned (N.v8971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8971 s i)) at 1.
  unfold R.v8971, N.v8971.
  rewrite ?node_8830.
  rewrite !state_r820_nr_5F820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r820_nr_5F820 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8972 (s : N.State) (i : N.Inputs) :
  R.v8972 (state s) (inputs i) = Zmod.unsigned (N.v8972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8972 s i)) at 1.
  unfold R.v8972, N.v8972.
  rewrite ?node_8970.
  rewrite ?node_8971.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8973 (s : N.State) (i : N.Inputs) :
  R.v8973 (state s) (inputs i) = Zmod.unsigned (N.v8973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8973 s i)) at 1.
  unfold R.v8973, N.v8973.
  rewrite ?node_8969.
  rewrite ?node_8972.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8974 (s : N.State) (i : N.Inputs) :
  R.v8974 (state s) (inputs i) = Zmod.unsigned (N.v8974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8974 s i)) at 1.
  unfold R.v8974, N.v8974.
  rewrite ?node_8966.
  rewrite ?node_8973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8975 (s : N.State) (i : N.Inputs) :
  R.v8975 (state s) (inputs i) = Zmod.unsigned (N.v8975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8975 s i)) at 1.
  unfold R.v8975, N.v8975.
  rewrite !state_r851_nr_5F851.
  rewrite !state_r852_nr_5F852.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r851_nr_5F851 s)).
  rewrite ?(bits.mod_to_Z (N.r852_nr_5F852 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8976 (s : N.State) (i : N.Inputs) :
  R.v8976 (state s) (inputs i) = Zmod.unsigned (N.v8976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8976 s i)) at 1.
  unfold R.v8976, N.v8976.
  rewrite ?node_8975.
  rewrite !state_r853_nr_5F853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r853_nr_5F853 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8977 (s : N.State) (i : N.Inputs) :
  R.v8977 (state s) (inputs i) = Zmod.unsigned (N.v8977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8977 s i)) at 1.
  unfold R.v8977, N.v8977.
  rewrite ?node_8976.
  rewrite !state_r854_nr_5F854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r854_nr_5F854 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8978 (s : N.State) (i : N.Inputs) :
  R.v8978 (state s) (inputs i) = Zmod.unsigned (N.v8978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8978 s i)) at 1.
  unfold R.v8978, N.v8978.
  rewrite !state_r822_nr_5F822.
  rewrite !state_r823_nr_5F823.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r822_nr_5F822 s)).
  rewrite ?(bits.mod_to_Z (N.r823_nr_5F823 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8979 (s : N.State) (i : N.Inputs) :
  R.v8979 (state s) (inputs i) = Zmod.unsigned (N.v8979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8979 s i)) at 1.
  unfold R.v8979, N.v8979.
  rewrite ?node_8838.
  rewrite !state_r824_nr_5F824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r824_nr_5F824 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8980 (s : N.State) (i : N.Inputs) :
  R.v8980 (state s) (inputs i) = Zmod.unsigned (N.v8980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8980 s i)) at 1.
  unfold R.v8980, N.v8980.
  rewrite ?node_8978.
  rewrite ?node_8979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8981 (s : N.State) (i : N.Inputs) :
  R.v8981 (state s) (inputs i) = Zmod.unsigned (N.v8981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8981 s i)) at 1.
  unfold R.v8981, N.v8981.
  rewrite ?node_8977.
  rewrite ?node_8980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8982 (s : N.State) (i : N.Inputs) :
  R.v8982 (state s) (inputs i) = Zmod.unsigned (N.v8982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8982 s i)) at 1.
  unfold R.v8982, N.v8982.
  rewrite ?node_8974.
  rewrite ?node_8981.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8983 (s : N.State) (i : N.Inputs) :
  R.v8983 (state s) (inputs i) = Zmod.unsigned (N.v8983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8983 s i)) at 1.
  unfold R.v8983, N.v8983.
  rewrite ?node_8821.
  rewrite ?node_8828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8984 (s : N.State) (i : N.Inputs) :
  R.v8984 (state s) (inputs i) = Zmod.unsigned (N.v8984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8984 s i)) at 1.
  unfold R.v8984, N.v8984.
  rewrite ?node_8829.
  rewrite ?node_8836.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8985 (s : N.State) (i : N.Inputs) :
  R.v8985 (state s) (inputs i) = Zmod.unsigned (N.v8985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8985 s i)) at 1.
  unfold R.v8985, N.v8985.
  rewrite ?node_8983.
  rewrite ?node_8984.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8986 (s : N.State) (i : N.Inputs) :
  R.v8986 (state s) (inputs i) = Zmod.unsigned (N.v8986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8986 s i)) at 1.
  unfold R.v8986, N.v8986.
  rewrite ?node_8982.
  rewrite ?node_8985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8987 (s : N.State) (i : N.Inputs) :
  R.v8987 (state s) (inputs i) = Zmod.unsigned (N.v8987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8987 s i)) at 1.
  unfold R.v8987, N.v8987.
  rewrite !state_r855_nr_5F855.
  rewrite !state_r856_nr_5F856.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r855_nr_5F855 s)).
  rewrite ?(bits.mod_to_Z (N.r856_nr_5F856 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8988 (s : N.State) (i : N.Inputs) :
  R.v8988 (state s) (inputs i) = Zmod.unsigned (N.v8988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8988 s i)) at 1.
  unfold R.v8988, N.v8988.
  rewrite ?node_8987.
  rewrite !state_r857_nr_5F857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r857_nr_5F857 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8989 (s : N.State) (i : N.Inputs) :
  R.v8989 (state s) (inputs i) = Zmod.unsigned (N.v8989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8989 s i)) at 1.
  unfold R.v8989, N.v8989.
  rewrite ?node_8988.
  rewrite !state_r858_nr_5F858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r858_nr_5F858 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8990 (s : N.State) (i : N.Inputs) :
  R.v8990 (state s) (inputs i) = Zmod.unsigned (N.v8990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8990 s i)) at 1.
  unfold R.v8990, N.v8990.
  rewrite !state_r826_nr_5F826.
  rewrite !state_r827_nr_5F827.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r826_nr_5F826 s)).
  rewrite ?(bits.mod_to_Z (N.r827_nr_5F827 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8991 (s : N.State) (i : N.Inputs) :
  R.v8991 (state s) (inputs i) = Zmod.unsigned (N.v8991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8991 s i)) at 1.
  unfold R.v8991, N.v8991.
  rewrite ?node_8850.
  rewrite !state_r828_nr_5F828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r828_nr_5F828 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8992 (s : N.State) (i : N.Inputs) :
  R.v8992 (state s) (inputs i) = Zmod.unsigned (N.v8992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8992 s i)) at 1.
  unfold R.v8992, N.v8992.
  rewrite ?node_8990.
  rewrite ?node_8991.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8993 (s : N.State) (i : N.Inputs) :
  R.v8993 (state s) (inputs i) = Zmod.unsigned (N.v8993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8993 s i)) at 1.
  unfold R.v8993, N.v8993.
  rewrite ?node_8989.
  rewrite ?node_8992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8994 (s : N.State) (i : N.Inputs) :
  R.v8994 (state s) (inputs i) = Zmod.unsigned (N.v8994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8994 s i)) at 1.
  unfold R.v8994, N.v8994.
  rewrite !state_r859_nr_5F859.
  rewrite !state_r860_nr_5F860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r859_nr_5F859 s)).
  rewrite ?(bits.mod_to_Z (N.r860_nr_5F860 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8995 (s : N.State) (i : N.Inputs) :
  R.v8995 (state s) (inputs i) = Zmod.unsigned (N.v8995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8995 s i)) at 1.
  unfold R.v8995, N.v8995.
  rewrite ?node_8994.
  rewrite !state_r861_nr_5F861.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r861_nr_5F861 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8996 (s : N.State) (i : N.Inputs) :
  R.v8996 (state s) (inputs i) = Zmod.unsigned (N.v8996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8996 s i)) at 1.
  unfold R.v8996, N.v8996.
  rewrite ?node_8995.
  rewrite !state_r862_nr_5F862.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r862_nr_5F862 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8997 (s : N.State) (i : N.Inputs) :
  R.v8997 (state s) (inputs i) = Zmod.unsigned (N.v8997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8997 s i)) at 1.
  unfold R.v8997, N.v8997.
  rewrite !state_r830_nr_5F830.
  rewrite !state_r831_nr_5F831.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r830_nr_5F830 s)).
  rewrite ?(bits.mod_to_Z (N.r831_nr_5F831 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8998 (s : N.State) (i : N.Inputs) :
  R.v8998 (state s) (inputs i) = Zmod.unsigned (N.v8998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8998 s i)) at 1.
  unfold R.v8998, N.v8998.
  rewrite ?node_8857.
  rewrite !state_r832_nr_5F832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r832_nr_5F832 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8999 (s : N.State) (i : N.Inputs) :
  R.v8999 (state s) (inputs i) = Zmod.unsigned (N.v8999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8999 s i)) at 1.
  unfold R.v8999, N.v8999.
  rewrite ?node_8997.
  rewrite ?node_8998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
