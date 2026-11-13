(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes008.
Lemma node_9000 (s : N.State) (i : N.Inputs) :
  R.v9000 (state s) (inputs i) = Zmod.unsigned (N.v9000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9000 s i)) at 1.
  unfold R.v9000, N.v9000.
  rewrite ?node_8996.
  rewrite ?node_8999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9001 (s : N.State) (i : N.Inputs) :
  R.v9001 (state s) (inputs i) = Zmod.unsigned (N.v9001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9001 s i)) at 1.
  unfold R.v9001, N.v9001.
  rewrite ?node_8993.
  rewrite ?node_9000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9002 (s : N.State) (i : N.Inputs) :
  R.v9002 (state s) (inputs i) = Zmod.unsigned (N.v9002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9002 s i)) at 1.
  unfold R.v9002, N.v9002.
  rewrite !state_r863_nr_5F863.
  rewrite !state_r864_nr_5F864.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r863_nr_5F863 s)).
  rewrite ?(bits.mod_to_Z (N.r864_nr_5F864 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9003 (s : N.State) (i : N.Inputs) :
  R.v9003 (state s) (inputs i) = Zmod.unsigned (N.v9003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9003 s i)) at 1.
  unfold R.v9003, N.v9003.
  rewrite ?node_9002.
  rewrite !state_r865_nr_5F865.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r865_nr_5F865 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9004 (s : N.State) (i : N.Inputs) :
  R.v9004 (state s) (inputs i) = Zmod.unsigned (N.v9004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9004 s i)) at 1.
  unfold R.v9004, N.v9004.
  rewrite ?node_9003.
  rewrite !state_r866_nr_5F866.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r866_nr_5F866 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9005 (s : N.State) (i : N.Inputs) :
  R.v9005 (state s) (inputs i) = Zmod.unsigned (N.v9005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9005 s i)) at 1.
  unfold R.v9005, N.v9005.
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

Lemma node_9006 (s : N.State) (i : N.Inputs) :
  R.v9006 (state s) (inputs i) = Zmod.unsigned (N.v9006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9006 s i)) at 1.
  unfold R.v9006, N.v9006.
  rewrite ?node_8865.
  rewrite !state_r836_nr_5F836.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r836_nr_5F836 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9007 (s : N.State) (i : N.Inputs) :
  R.v9007 (state s) (inputs i) = Zmod.unsigned (N.v9007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9007 s i)) at 1.
  unfold R.v9007, N.v9007.
  rewrite ?node_9005.
  rewrite ?node_9006.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9008 (s : N.State) (i : N.Inputs) :
  R.v9008 (state s) (inputs i) = Zmod.unsigned (N.v9008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9008 s i)) at 1.
  unfold R.v9008, N.v9008.
  rewrite ?node_9004.
  rewrite ?node_9007.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9009 (s : N.State) (i : N.Inputs) :
  R.v9009 (state s) (inputs i) = Zmod.unsigned (N.v9009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9009 s i)) at 1.
  unfold R.v9009, N.v9009.
  rewrite ?node_9001.
  rewrite ?node_9008.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9010 (s : N.State) (i : N.Inputs) :
  R.v9010 (state s) (inputs i) = Zmod.unsigned (N.v9010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9010 s i)) at 1.
  unfold R.v9010, N.v9010.
  rewrite ?node_9009.
  rewrite !state_r867_nr_5F867.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r867_nr_5F867 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9011 (s : N.State) (i : N.Inputs) :
  R.v9011 (state s) (inputs i) = Zmod.unsigned (N.v9011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9011 s i)) at 1.
  unfold R.v9011, N.v9011.
  rewrite ?node_8856.
  rewrite ?node_8863.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9012 (s : N.State) (i : N.Inputs) :
  R.v9012 (state s) (inputs i) = Zmod.unsigned (N.v9012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9012 s i)) at 1.
  unfold R.v9012, N.v9012.
  rewrite ?node_8864.
  rewrite ?node_8871.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9013 (s : N.State) (i : N.Inputs) :
  R.v9013 (state s) (inputs i) = Zmod.unsigned (N.v9013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9013 s i)) at 1.
  unfold R.v9013, N.v9013.
  rewrite ?node_9011.
  rewrite ?node_9012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9014 (s : N.State) (i : N.Inputs) :
  R.v9014 (state s) (inputs i) = Zmod.unsigned (N.v9014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9014 s i)) at 1.
  unfold R.v9014, N.v9014.
  rewrite ?node_9010.
  rewrite ?node_9013.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9015 (s : N.State) (i : N.Inputs) :
  R.v9015 (state s) (inputs i) = Zmod.unsigned (N.v9015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9015 s i)) at 1.
  unfold R.v9015, N.v9015.
  rewrite ?node_8986.
  rewrite ?node_9014.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9016 (s : N.State) (i : N.Inputs) :
  R.v9016 (state s) (inputs i) = Zmod.unsigned (N.v9016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9016 s i)) at 1.
  unfold R.v9016, N.v9016.
  rewrite ?node_8816.
  rewrite !state_r813_nr_5F813.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r813_nr_5F813 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9017 (s : N.State) (i : N.Inputs) :
  R.v9017 (state s) (inputs i) = Zmod.unsigned (N.v9017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9017 s i)) at 1.
  unfold R.v9017, N.v9017.
  rewrite ?node_8817.
  rewrite ?node_8820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9018 (s : N.State) (i : N.Inputs) :
  R.v9018 (state s) (inputs i) = Zmod.unsigned (N.v9018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9018 s i)) at 1.
  unfold R.v9018, N.v9018.
  rewrite ?node_9016.
  rewrite ?node_9017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9019 (s : N.State) (i : N.Inputs) :
  R.v9019 (state s) (inputs i) = Zmod.unsigned (N.v9019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9019 s i)) at 1.
  unfold R.v9019, N.v9019.
  rewrite ?node_8823.
  rewrite !state_r817_nr_5F817.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r817_nr_5F817 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9020 (s : N.State) (i : N.Inputs) :
  R.v9020 (state s) (inputs i) = Zmod.unsigned (N.v9020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9020 s i)) at 1.
  unfold R.v9020, N.v9020.
  rewrite ?node_8824.
  rewrite ?node_8827.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9021 (s : N.State) (i : N.Inputs) :
  R.v9021 (state s) (inputs i) = Zmod.unsigned (N.v9021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9021 s i)) at 1.
  unfold R.v9021, N.v9021.
  rewrite ?node_9019.
  rewrite ?node_9020.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9022 (s : N.State) (i : N.Inputs) :
  R.v9022 (state s) (inputs i) = Zmod.unsigned (N.v9022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9022 s i)) at 1.
  unfold R.v9022, N.v9022.
  rewrite ?node_9018.
  rewrite ?node_9021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9023 (s : N.State) (i : N.Inputs) :
  R.v9023 (state s) (inputs i) = Zmod.unsigned (N.v9023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9023 s i)) at 1.
  unfold R.v9023, N.v9023.
  rewrite ?node_8831.
  rewrite !state_r821_nr_5F821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r821_nr_5F821 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9024 (s : N.State) (i : N.Inputs) :
  R.v9024 (state s) (inputs i) = Zmod.unsigned (N.v9024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9024 s i)) at 1.
  unfold R.v9024, N.v9024.
  rewrite ?node_8832.
  rewrite ?node_8835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9025 (s : N.State) (i : N.Inputs) :
  R.v9025 (state s) (inputs i) = Zmod.unsigned (N.v9025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9025 s i)) at 1.
  unfold R.v9025, N.v9025.
  rewrite ?node_9023.
  rewrite ?node_9024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9026 (s : N.State) (i : N.Inputs) :
  R.v9026 (state s) (inputs i) = Zmod.unsigned (N.v9026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9026 s i)) at 1.
  unfold R.v9026, N.v9026.
  rewrite ?node_9022.
  rewrite ?node_9025.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9027 (s : N.State) (i : N.Inputs) :
  R.v9027 (state s) (inputs i) = Zmod.unsigned (N.v9027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9027 s i)) at 1.
  unfold R.v9027, N.v9027.
  rewrite ?node_8839.
  rewrite !state_r825_nr_5F825.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r825_nr_5F825 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9028 (s : N.State) (i : N.Inputs) :
  R.v9028 (state s) (inputs i) = Zmod.unsigned (N.v9028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9028 s i)) at 1.
  unfold R.v9028, N.v9028.
  rewrite ?node_8840.
  rewrite ?node_8843.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9029 (s : N.State) (i : N.Inputs) :
  R.v9029 (state s) (inputs i) = Zmod.unsigned (N.v9029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9029 s i)) at 1.
  unfold R.v9029, N.v9029.
  rewrite ?node_9027.
  rewrite ?node_9028.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9030 (s : N.State) (i : N.Inputs) :
  R.v9030 (state s) (inputs i) = Zmod.unsigned (N.v9030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9030 s i)) at 1.
  unfold R.v9030, N.v9030.
  rewrite ?node_9026.
  rewrite ?node_9029.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9031 (s : N.State) (i : N.Inputs) :
  R.v9031 (state s) (inputs i) = Zmod.unsigned (N.v9031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9031 s i)) at 1.
  unfold R.v9031, N.v9031.
  rewrite ?node_8881.
  rewrite ?node_8884.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9032 (s : N.State) (i : N.Inputs) :
  R.v9032 (state s) (inputs i) = Zmod.unsigned (N.v9032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9032 s i)) at 1.
  unfold R.v9032, N.v9032.
  rewrite ?node_8885.
  rewrite ?node_8888.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9033 (s : N.State) (i : N.Inputs) :
  R.v9033 (state s) (inputs i) = Zmod.unsigned (N.v9033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9033 s i)) at 1.
  unfold R.v9033, N.v9033.
  rewrite ?node_9031.
  rewrite ?node_9032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9034 (s : N.State) (i : N.Inputs) :
  R.v9034 (state s) (inputs i) = Zmod.unsigned (N.v9034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9034 s i)) at 1.
  unfold R.v9034, N.v9034.
  rewrite ?node_9030.
  rewrite ?node_9033.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9035 (s : N.State) (i : N.Inputs) :
  R.v9035 (state s) (inputs i) = Zmod.unsigned (N.v9035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9035 s i)) at 1.
  unfold R.v9035, N.v9035.
  rewrite ?node_9015.
  rewrite ?node_9034.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9036 (s : N.State) (i : N.Inputs) :
  R.v9036 (state s) (inputs i) = Zmod.unsigned (N.v9036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9036 s i)) at 1.
  unfold R.v9036, N.v9036.
  rewrite ?node_8851.
  rewrite !state_r829_nr_5F829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r829_nr_5F829 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9037 (s : N.State) (i : N.Inputs) :
  R.v9037 (state s) (inputs i) = Zmod.unsigned (N.v9037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9037 s i)) at 1.
  unfold R.v9037, N.v9037.
  rewrite ?node_8852.
  rewrite ?node_8855.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9038 (s : N.State) (i : N.Inputs) :
  R.v9038 (state s) (inputs i) = Zmod.unsigned (N.v9038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9038 s i)) at 1.
  unfold R.v9038, N.v9038.
  rewrite ?node_9036.
  rewrite ?node_9037.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9039 (s : N.State) (i : N.Inputs) :
  R.v9039 (state s) (inputs i) = Zmod.unsigned (N.v9039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9039 s i)) at 1.
  unfold R.v9039, N.v9039.
  rewrite ?node_8858.
  rewrite !state_r833_nr_5F833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r833_nr_5F833 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9040 (s : N.State) (i : N.Inputs) :
  R.v9040 (state s) (inputs i) = Zmod.unsigned (N.v9040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9040 s i)) at 1.
  unfold R.v9040, N.v9040.
  rewrite ?node_8859.
  rewrite ?node_8862.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9041 (s : N.State) (i : N.Inputs) :
  R.v9041 (state s) (inputs i) = Zmod.unsigned (N.v9041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9041 s i)) at 1.
  unfold R.v9041, N.v9041.
  rewrite ?node_9039.
  rewrite ?node_9040.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9042 (s : N.State) (i : N.Inputs) :
  R.v9042 (state s) (inputs i) = Zmod.unsigned (N.v9042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9042 s i)) at 1.
  unfold R.v9042, N.v9042.
  rewrite ?node_9038.
  rewrite ?node_9041.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9043 (s : N.State) (i : N.Inputs) :
  R.v9043 (state s) (inputs i) = Zmod.unsigned (N.v9043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9043 s i)) at 1.
  unfold R.v9043, N.v9043.
  rewrite ?node_8866.
  rewrite !state_r837_nr_5F837.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r837_nr_5F837 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9044 (s : N.State) (i : N.Inputs) :
  R.v9044 (state s) (inputs i) = Zmod.unsigned (N.v9044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9044 s i)) at 1.
  unfold R.v9044, N.v9044.
  rewrite ?node_8867.
  rewrite ?node_8870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9045 (s : N.State) (i : N.Inputs) :
  R.v9045 (state s) (inputs i) = Zmod.unsigned (N.v9045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9045 s i)) at 1.
  unfold R.v9045, N.v9045.
  rewrite ?node_9043.
  rewrite ?node_9044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9046 (s : N.State) (i : N.Inputs) :
  R.v9046 (state s) (inputs i) = Zmod.unsigned (N.v9046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9046 s i)) at 1.
  unfold R.v9046, N.v9046.
  rewrite ?node_9042.
  rewrite ?node_9045.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9047 (s : N.State) (i : N.Inputs) :
  R.v9047 (state s) (inputs i) = Zmod.unsigned (N.v9047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9047 s i)) at 1.
  unfold R.v9047, N.v9047.
  rewrite ?node_9035.
  rewrite ?node_9046.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9048 (s : N.State) (i : N.Inputs) :
  R.v9048 (state s) (inputs i) = Zmod.unsigned (N.v9048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9048 s i)) at 1.
  unfold R.v9048, N.v9048.
  rewrite ?node_8849.
  rewrite ?node_8877.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9049 (s : N.State) (i : N.Inputs) :
  R.v9049 (state s) (inputs i) = Zmod.unsigned (N.v9049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9049 s i)) at 1.
  unfold R.v9049, N.v9049.
  rewrite ?node_8878.
  rewrite ?node_8897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9050 (s : N.State) (i : N.Inputs) :
  R.v9050 (state s) (inputs i) = Zmod.unsigned (N.v9050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9050 s i)) at 1.
  unfold R.v9050, N.v9050.
  rewrite ?node_9048.
  rewrite ?node_9049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9051 (s : N.State) (i : N.Inputs) :
  R.v9051 (state s) (inputs i) = Zmod.unsigned (N.v9051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9051 s i)) at 1.
  unfold R.v9051, N.v9051.
  rewrite ?node_9047.
  rewrite ?node_9050.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9052 (s : N.State) (i : N.Inputs) :
  R.v9052 (state s) (inputs i) = Zmod.unsigned (N.v9052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9052 s i)) at 1.
  unfold R.v9052, N.v9052.
  rewrite ?node_8837.
  rewrite ?node_8844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9053 (s : N.State) (i : N.Inputs) :
  R.v9053 (state s) (inputs i) = Zmod.unsigned (N.v9053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9053 s i)) at 1.
  unfold R.v9053, N.v9053.
  rewrite ?node_8845.
  rewrite ?node_8848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9054 (s : N.State) (i : N.Inputs) :
  R.v9054 (state s) (inputs i) = Zmod.unsigned (N.v9054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9054 s i)) at 1.
  unfold R.v9054, N.v9054.
  rewrite ?node_9052.
  rewrite ?node_9053.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9055 (s : N.State) (i : N.Inputs) :
  R.v9055 (state s) (inputs i) = Zmod.unsigned (N.v9055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9055 s i)) at 1.
  unfold R.v9055, N.v9055.
  rewrite ?node_8872.
  rewrite !state_r838_nr_5F838.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r838_nr_5F838 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9056 (s : N.State) (i : N.Inputs) :
  R.v9056 (state s) (inputs i) = Zmod.unsigned (N.v9056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9056 s i)) at 1.
  unfold R.v9056, N.v9056.
  rewrite ?node_8873.
  rewrite ?node_8876.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9057 (s : N.State) (i : N.Inputs) :
  R.v9057 (state s) (inputs i) = Zmod.unsigned (N.v9057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9057 s i)) at 1.
  unfold R.v9057, N.v9057.
  rewrite ?node_9055.
  rewrite ?node_9056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9058 (s : N.State) (i : N.Inputs) :
  R.v9058 (state s) (inputs i) = Zmod.unsigned (N.v9058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9058 s i)) at 1.
  unfold R.v9058, N.v9058.
  rewrite ?node_9054.
  rewrite ?node_9057.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9059 (s : N.State) (i : N.Inputs) :
  R.v9059 (state s) (inputs i) = Zmod.unsigned (N.v9059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9059 s i)) at 1.
  unfold R.v9059, N.v9059.
  rewrite ?node_8889.
  rewrite ?node_8892.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9060 (s : N.State) (i : N.Inputs) :
  R.v9060 (state s) (inputs i) = Zmod.unsigned (N.v9060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9060 s i)) at 1.
  unfold R.v9060, N.v9060.
  rewrite ?node_8893.
  rewrite ?node_8896.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9061 (s : N.State) (i : N.Inputs) :
  R.v9061 (state s) (inputs i) = Zmod.unsigned (N.v9061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9061 s i)) at 1.
  unfold R.v9061, N.v9061.
  rewrite ?node_9059.
  rewrite ?node_9060.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9062 (s : N.State) (i : N.Inputs) :
  R.v9062 (state s) (inputs i) = Zmod.unsigned (N.v9062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9062 s i)) at 1.
  unfold R.v9062, N.v9062.
  rewrite ?node_9058.
  rewrite ?node_9061.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9063 (s : N.State) (i : N.Inputs) :
  R.v9063 (state s) (inputs i) = Zmod.unsigned (N.v9063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9063 s i)) at 1.
  unfold R.v9063, N.v9063.
  rewrite ?node_8901.
  rewrite ?node_8904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9064 (s : N.State) (i : N.Inputs) :
  R.v9064 (state s) (inputs i) = Zmod.unsigned (N.v9064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9064 s i)) at 1.
  unfold R.v9064, N.v9064.
  rewrite ?node_8905.
  rewrite ?node_8908.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9065 (s : N.State) (i : N.Inputs) :
  R.v9065 (state s) (inputs i) = Zmod.unsigned (N.v9065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9065 s i)) at 1.
  unfold R.v9065, N.v9065.
  rewrite ?node_9063.
  rewrite ?node_9064.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9066 (s : N.State) (i : N.Inputs) :
  R.v9066 (state s) (inputs i) = Zmod.unsigned (N.v9066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9066 s i)) at 1.
  unfold R.v9066, N.v9066.
  rewrite ?node_9062.
  rewrite ?node_9065.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9067 (s : N.State) (i : N.Inputs) :
  R.v9067 (state s) (inputs i) = Zmod.unsigned (N.v9067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9067 s i)) at 1.
  unfold R.v9067, N.v9067.
  rewrite ?node_8917.
  rewrite ?node_8920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9068 (s : N.State) (i : N.Inputs) :
  R.v9068 (state s) (inputs i) = Zmod.unsigned (N.v9068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9068 s i)) at 1.
  unfold R.v9068, N.v9068.
  rewrite ?node_8921.
  rewrite ?node_8924.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9069 (s : N.State) (i : N.Inputs) :
  R.v9069 (state s) (inputs i) = Zmod.unsigned (N.v9069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9069 s i)) at 1.
  unfold R.v9069, N.v9069.
  rewrite ?node_9067.
  rewrite ?node_9068.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9070 (s : N.State) (i : N.Inputs) :
  R.v9070 (state s) (inputs i) = Zmod.unsigned (N.v9070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9070 s i)) at 1.
  unfold R.v9070, N.v9070.
  rewrite ?node_9066.
  rewrite ?node_9069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9071 (s : N.State) (i : N.Inputs) :
  R.v9071 (state s) (inputs i) = Zmod.unsigned (N.v9071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9071 s i)) at 1.
  unfold R.v9071, N.v9071.
  rewrite ?node_9051.
  rewrite ?node_9070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9072 (s : N.State) (i : N.Inputs) :
  R.v9072 (state s) (inputs i) = Zmod.unsigned (N.v9072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9072 s i)) at 1.
  unfold R.v9072, N.v9072.
  rewrite ?node_8898.
  rewrite ?node_8909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9073 (s : N.State) (i : N.Inputs) :
  R.v9073 (state s) (inputs i) = Zmod.unsigned (N.v9073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9073 s i)) at 1.
  unfold R.v9073, N.v9073.
  rewrite ?node_8910.
  rewrite ?node_8913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9074 (s : N.State) (i : N.Inputs) :
  R.v9074 (state s) (inputs i) = Zmod.unsigned (N.v9074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9074 s i)) at 1.
  unfold R.v9074, N.v9074.
  rewrite ?node_9072.
  rewrite ?node_9073.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9075 (s : N.State) (i : N.Inputs) :
  R.v9075 (state s) (inputs i) = Zmod.unsigned (N.v9075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9075 s i)) at 1.
  unfold R.v9075, N.v9075.
  rewrite ?node_9071.
  rewrite ?node_9074.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9076 (s : N.State) (i : N.Inputs) :
  R.v9076 (state s) (inputs i) = Zmod.unsigned (N.v9076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9076 s i)) at 1.
  unfold R.v9076, N.v9076.
  rewrite ?node_8925.
  rewrite ?node_8926.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9077 (s : N.State) (i : N.Inputs) :
  R.v9077 (state s) (inputs i) = Zmod.unsigned (N.v9077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9077 s i)) at 1.
  unfold R.v9077, N.v9077.
  rewrite ?node_8927.
  rewrite ?node_8930.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9078 (s : N.State) (i : N.Inputs) :
  R.v9078 (state s) (inputs i) = Zmod.unsigned (N.v9078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9078 s i)) at 1.
  unfold R.v9078, N.v9078.
  rewrite ?node_9076.
  rewrite ?node_9077.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9079 (s : N.State) (i : N.Inputs) :
  R.v9079 (state s) (inputs i) = Zmod.unsigned (N.v9079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9079 s i)) at 1.
  unfold R.v9079, N.v9079.
  rewrite ?node_9075.
  rewrite ?node_9078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9080 (s : N.State) (i : N.Inputs) :
  R.v9080 (state s) (inputs i) = Zmod.unsigned (N.v9080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9080 s i)) at 1.
  unfold R.v9080, N.v9080.
  rewrite ?node_8914.
  rewrite ?node_8931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9081 (s : N.State) (i : N.Inputs) :
  R.v9081 (state s) (inputs i) = Zmod.unsigned (N.v9081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9081 s i)) at 1.
  unfold R.v9081, N.v9081.
  rewrite ?node_8932.
  rewrite ?node_8935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9082 (s : N.State) (i : N.Inputs) :
  R.v9082 (state s) (inputs i) = Zmod.unsigned (N.v9082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9082 s i)) at 1.
  unfold R.v9082, N.v9082.
  rewrite ?node_9080.
  rewrite ?node_9081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9083 (s : N.State) (i : N.Inputs) :
  R.v9083 (state s) (inputs i) = Zmod.unsigned (N.v9083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9083 s i)) at 1.
  unfold R.v9083, N.v9083.
  rewrite ?node_9079.
  rewrite ?node_9082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9084 (s : N.State) (i : N.Inputs) :
  R.v9084 (state s) (inputs i) = Zmod.unsigned (N.v9084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9084 s i)) at 1.
  unfold R.v9084, N.v9084.
  rewrite ?node_8936.
  rewrite ?node_8939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9085 (s : N.State) (i : N.Inputs) :
  R.v9085 (state s) (inputs i) = Zmod.unsigned (N.v9085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9085 s i)) at 1.
  unfold R.v9085, N.v9085.
  rewrite ?node_8940.
  rewrite ?node_8943.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9086 (s : N.State) (i : N.Inputs) :
  R.v9086 (state s) (inputs i) = Zmod.unsigned (N.v9086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9086 s i)) at 1.
  unfold R.v9086, N.v9086.
  rewrite ?node_9084.
  rewrite ?node_9085.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9087 (s : N.State) (i : N.Inputs) :
  R.v9087 (state s) (inputs i) = Zmod.unsigned (N.v9087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9087 s i)) at 1.
  unfold R.v9087, N.v9087.
  rewrite ?node_9083.
  rewrite ?node_9086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9088 (s : N.State) (i : N.Inputs) :
  R.v9088 (state s) (inputs i) = Zmod.unsigned (N.v9088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9088 s i)) at 1.
  unfold R.v9088, N.v9088.
  rewrite ?node_9087.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2383_nr_5F2414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2383_nr_5F2414 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9089 (s : N.State) (i : N.Inputs) :
  R.v9089 (state s) (inputs i) = Zmod.unsigned (N.v9089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9089 s i)) at 1.
  unfold R.v9089, N.v9089.
  rewrite ?node_8944.
  rewrite ?node_8947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9090 (s : N.State) (i : N.Inputs) :
  R.v9090 (state s) (inputs i) = Zmod.unsigned (N.v9090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9090 s i)) at 1.
  unfold R.v9090, N.v9090.
  rewrite ?node_9089.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2384_nr_5F2415.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2384_nr_5F2415 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9091 (s : N.State) (i : N.Inputs) :
  R.v9091 (state s) (inputs i) = Zmod.unsigned (N.v9091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9091 s i)) at 1.
  unfold R.v9091, N.v9091.
  rewrite !state_r868_nr_5F868.
  rewrite !state_r869_nr_5F869.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r868_nr_5F868 s)).
  rewrite ?(bits.mod_to_Z (N.r869_nr_5F869 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9092 (s : N.State) (i : N.Inputs) :
  R.v9092 (state s) (inputs i) = Zmod.unsigned (N.v9092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9092 s i)) at 1.
  unfold R.v9092, N.v9092.
  rewrite ?node_9091.
  rewrite !state_r870_nr_5F870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r870_nr_5F870 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9093 (s : N.State) (i : N.Inputs) :
  R.v9093 (state s) (inputs i) = Zmod.unsigned (N.v9093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9093 s i)) at 1.
  unfold R.v9093, N.v9093.
  rewrite ?node_9092.
  rewrite !state_r871_nr_5F871.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r871_nr_5F871 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9094 (s : N.State) (i : N.Inputs) :
  R.v9094 (state s) (inputs i) = Zmod.unsigned (N.v9094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9094 s i)) at 1.
  unfold R.v9094, N.v9094.
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

Lemma node_9095 (s : N.State) (i : N.Inputs) :
  R.v9095 (state s) (inputs i) = Zmod.unsigned (N.v9095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9095 s i)) at 1.
  unfold R.v9095, N.v9095.
  rewrite ?node_8952.
  rewrite !state_r841_nr_5F841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r841_nr_5F841 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9096 (s : N.State) (i : N.Inputs) :
  R.v9096 (state s) (inputs i) = Zmod.unsigned (N.v9096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9096 s i)) at 1.
  unfold R.v9096, N.v9096.
  rewrite ?node_9094.
  rewrite ?node_9095.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9097 (s : N.State) (i : N.Inputs) :
  R.v9097 (state s) (inputs i) = Zmod.unsigned (N.v9097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9097 s i)) at 1.
  unfold R.v9097, N.v9097.
  rewrite ?node_9093.
  rewrite ?node_9096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9098 (s : N.State) (i : N.Inputs) :
  R.v9098 (state s) (inputs i) = Zmod.unsigned (N.v9098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9098 s i)) at 1.
  unfold R.v9098, N.v9098.
  rewrite !state_r872_nr_5F872.
  rewrite !state_r873_nr_5F873.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r872_nr_5F872 s)).
  rewrite ?(bits.mod_to_Z (N.r873_nr_5F873 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9099 (s : N.State) (i : N.Inputs) :
  R.v9099 (state s) (inputs i) = Zmod.unsigned (N.v9099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9099 s i)) at 1.
  unfold R.v9099, N.v9099.
  rewrite ?node_9098.
  rewrite !state_r874_nr_5F874.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r874_nr_5F874 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9100 (s : N.State) (i : N.Inputs) :
  R.v9100 (state s) (inputs i) = Zmod.unsigned (N.v9100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9100 s i)) at 1.
  unfold R.v9100, N.v9100.
  rewrite ?node_9099.
  rewrite !state_r875_nr_5F875.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r875_nr_5F875 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9101 (s : N.State) (i : N.Inputs) :
  R.v9101 (state s) (inputs i) = Zmod.unsigned (N.v9101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9101 s i)) at 1.
  unfold R.v9101, N.v9101.
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

Lemma node_9102 (s : N.State) (i : N.Inputs) :
  R.v9102 (state s) (inputs i) = Zmod.unsigned (N.v9102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9102 s i)) at 1.
  unfold R.v9102, N.v9102.
  rewrite ?node_8959.
  rewrite !state_r845_nr_5F845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r845_nr_5F845 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9103 (s : N.State) (i : N.Inputs) :
  R.v9103 (state s) (inputs i) = Zmod.unsigned (N.v9103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9103 s i)) at 1.
  unfold R.v9103, N.v9103.
  rewrite ?node_9101.
  rewrite ?node_9102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9104 (s : N.State) (i : N.Inputs) :
  R.v9104 (state s) (inputs i) = Zmod.unsigned (N.v9104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9104 s i)) at 1.
  unfold R.v9104, N.v9104.
  rewrite ?node_9100.
  rewrite ?node_9103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9105 (s : N.State) (i : N.Inputs) :
  R.v9105 (state s) (inputs i) = Zmod.unsigned (N.v9105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9105 s i)) at 1.
  unfold R.v9105, N.v9105.
  rewrite ?node_9097.
  rewrite ?node_9104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9106 (s : N.State) (i : N.Inputs) :
  R.v9106 (state s) (inputs i) = Zmod.unsigned (N.v9106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9106 s i)) at 1.
  unfold R.v9106, N.v9106.
  rewrite !state_r876_nr_5F876.
  rewrite !state_r877_nr_5F877.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r876_nr_5F876 s)).
  rewrite ?(bits.mod_to_Z (N.r877_nr_5F877 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9107 (s : N.State) (i : N.Inputs) :
  R.v9107 (state s) (inputs i) = Zmod.unsigned (N.v9107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9107 s i)) at 1.
  unfold R.v9107, N.v9107.
  rewrite ?node_9106.
  rewrite !state_r878_nr_5F878.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r878_nr_5F878 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9108 (s : N.State) (i : N.Inputs) :
  R.v9108 (state s) (inputs i) = Zmod.unsigned (N.v9108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9108 s i)) at 1.
  unfold R.v9108, N.v9108.
  rewrite ?node_9107.
  rewrite !state_r879_nr_5F879.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r879_nr_5F879 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9109 (s : N.State) (i : N.Inputs) :
  R.v9109 (state s) (inputs i) = Zmod.unsigned (N.v9109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9109 s i)) at 1.
  unfold R.v9109, N.v9109.
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

Lemma node_9110 (s : N.State) (i : N.Inputs) :
  R.v9110 (state s) (inputs i) = Zmod.unsigned (N.v9110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9110 s i)) at 1.
  unfold R.v9110, N.v9110.
  rewrite ?node_8967.
  rewrite !state_r849_nr_5F849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r849_nr_5F849 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9111 (s : N.State) (i : N.Inputs) :
  R.v9111 (state s) (inputs i) = Zmod.unsigned (N.v9111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9111 s i)) at 1.
  unfold R.v9111, N.v9111.
  rewrite ?node_9109.
  rewrite ?node_9110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9112 (s : N.State) (i : N.Inputs) :
  R.v9112 (state s) (inputs i) = Zmod.unsigned (N.v9112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9112 s i)) at 1.
  unfold R.v9112, N.v9112.
  rewrite ?node_9108.
  rewrite ?node_9111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9113 (s : N.State) (i : N.Inputs) :
  R.v9113 (state s) (inputs i) = Zmod.unsigned (N.v9113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9113 s i)) at 1.
  unfold R.v9113, N.v9113.
  rewrite ?node_9105.
  rewrite ?node_9112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9114 (s : N.State) (i : N.Inputs) :
  R.v9114 (state s) (inputs i) = Zmod.unsigned (N.v9114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9114 s i)) at 1.
  unfold R.v9114, N.v9114.
  rewrite !state_r880_nr_5F880.
  rewrite !state_r881_nr_5F881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r880_nr_5F880 s)).
  rewrite ?(bits.mod_to_Z (N.r881_nr_5F881 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9115 (s : N.State) (i : N.Inputs) :
  R.v9115 (state s) (inputs i) = Zmod.unsigned (N.v9115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9115 s i)) at 1.
  unfold R.v9115, N.v9115.
  rewrite ?node_9114.
  rewrite !state_r882_nr_5F882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r882_nr_5F882 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9116 (s : N.State) (i : N.Inputs) :
  R.v9116 (state s) (inputs i) = Zmod.unsigned (N.v9116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9116 s i)) at 1.
  unfold R.v9116, N.v9116.
  rewrite ?node_9115.
  rewrite !state_r883_nr_5F883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r883_nr_5F883 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9117 (s : N.State) (i : N.Inputs) :
  R.v9117 (state s) (inputs i) = Zmod.unsigned (N.v9117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9117 s i)) at 1.
  unfold R.v9117, N.v9117.
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

Lemma node_9118 (s : N.State) (i : N.Inputs) :
  R.v9118 (state s) (inputs i) = Zmod.unsigned (N.v9118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9118 s i)) at 1.
  unfold R.v9118, N.v9118.
  rewrite ?node_8975.
  rewrite !state_r853_nr_5F853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r853_nr_5F853 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9119 (s : N.State) (i : N.Inputs) :
  R.v9119 (state s) (inputs i) = Zmod.unsigned (N.v9119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9119 s i)) at 1.
  unfold R.v9119, N.v9119.
  rewrite ?node_9117.
  rewrite ?node_9118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9120 (s : N.State) (i : N.Inputs) :
  R.v9120 (state s) (inputs i) = Zmod.unsigned (N.v9120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9120 s i)) at 1.
  unfold R.v9120, N.v9120.
  rewrite ?node_9116.
  rewrite ?node_9119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9121 (s : N.State) (i : N.Inputs) :
  R.v9121 (state s) (inputs i) = Zmod.unsigned (N.v9121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9121 s i)) at 1.
  unfold R.v9121, N.v9121.
  rewrite ?node_9113.
  rewrite ?node_9120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9122 (s : N.State) (i : N.Inputs) :
  R.v9122 (state s) (inputs i) = Zmod.unsigned (N.v9122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9122 s i)) at 1.
  unfold R.v9122, N.v9122.
  rewrite ?node_8958.
  rewrite ?node_8965.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9123 (s : N.State) (i : N.Inputs) :
  R.v9123 (state s) (inputs i) = Zmod.unsigned (N.v9123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9123 s i)) at 1.
  unfold R.v9123, N.v9123.
  rewrite ?node_8966.
  rewrite ?node_8973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9124 (s : N.State) (i : N.Inputs) :
  R.v9124 (state s) (inputs i) = Zmod.unsigned (N.v9124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9124 s i)) at 1.
  unfold R.v9124, N.v9124.
  rewrite ?node_9122.
  rewrite ?node_9123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9125 (s : N.State) (i : N.Inputs) :
  R.v9125 (state s) (inputs i) = Zmod.unsigned (N.v9125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9125 s i)) at 1.
  unfold R.v9125, N.v9125.
  rewrite ?node_9121.
  rewrite ?node_9124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9126 (s : N.State) (i : N.Inputs) :
  R.v9126 (state s) (inputs i) = Zmod.unsigned (N.v9126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9126 s i)) at 1.
  unfold R.v9126, N.v9126.
  rewrite !state_r884_nr_5F884.
  rewrite !state_r885_nr_5F885.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r884_nr_5F884 s)).
  rewrite ?(bits.mod_to_Z (N.r885_nr_5F885 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9127 (s : N.State) (i : N.Inputs) :
  R.v9127 (state s) (inputs i) = Zmod.unsigned (N.v9127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9127 s i)) at 1.
  unfold R.v9127, N.v9127.
  rewrite ?node_9126.
  rewrite !state_r886_nr_5F886.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r886_nr_5F886 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9128 (s : N.State) (i : N.Inputs) :
  R.v9128 (state s) (inputs i) = Zmod.unsigned (N.v9128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9128 s i)) at 1.
  unfold R.v9128, N.v9128.
  rewrite ?node_9127.
  rewrite !state_r887_nr_5F887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r887_nr_5F887 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9129 (s : N.State) (i : N.Inputs) :
  R.v9129 (state s) (inputs i) = Zmod.unsigned (N.v9129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9129 s i)) at 1.
  unfold R.v9129, N.v9129.
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

Lemma node_9130 (s : N.State) (i : N.Inputs) :
  R.v9130 (state s) (inputs i) = Zmod.unsigned (N.v9130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9130 s i)) at 1.
  unfold R.v9130, N.v9130.
  rewrite ?node_8987.
  rewrite !state_r857_nr_5F857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r857_nr_5F857 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9131 (s : N.State) (i : N.Inputs) :
  R.v9131 (state s) (inputs i) = Zmod.unsigned (N.v9131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9131 s i)) at 1.
  unfold R.v9131, N.v9131.
  rewrite ?node_9129.
  rewrite ?node_9130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9132 (s : N.State) (i : N.Inputs) :
  R.v9132 (state s) (inputs i) = Zmod.unsigned (N.v9132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9132 s i)) at 1.
  unfold R.v9132, N.v9132.
  rewrite ?node_9128.
  rewrite ?node_9131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9133 (s : N.State) (i : N.Inputs) :
  R.v9133 (state s) (inputs i) = Zmod.unsigned (N.v9133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9133 s i)) at 1.
  unfold R.v9133, N.v9133.
  rewrite !state_r888_nr_5F888.
  rewrite !state_r889_nr_5F889.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r888_nr_5F888 s)).
  rewrite ?(bits.mod_to_Z (N.r889_nr_5F889 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9134 (s : N.State) (i : N.Inputs) :
  R.v9134 (state s) (inputs i) = Zmod.unsigned (N.v9134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9134 s i)) at 1.
  unfold R.v9134, N.v9134.
  rewrite ?node_9133.
  rewrite !state_r890_nr_5F890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r890_nr_5F890 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9135 (s : N.State) (i : N.Inputs) :
  R.v9135 (state s) (inputs i) = Zmod.unsigned (N.v9135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9135 s i)) at 1.
  unfold R.v9135, N.v9135.
  rewrite ?node_9134.
  rewrite !state_r891_nr_5F891.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r891_nr_5F891 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9136 (s : N.State) (i : N.Inputs) :
  R.v9136 (state s) (inputs i) = Zmod.unsigned (N.v9136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9136 s i)) at 1.
  unfold R.v9136, N.v9136.
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

Lemma node_9137 (s : N.State) (i : N.Inputs) :
  R.v9137 (state s) (inputs i) = Zmod.unsigned (N.v9137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9137 s i)) at 1.
  unfold R.v9137, N.v9137.
  rewrite ?node_8994.
  rewrite !state_r861_nr_5F861.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r861_nr_5F861 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9138 (s : N.State) (i : N.Inputs) :
  R.v9138 (state s) (inputs i) = Zmod.unsigned (N.v9138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9138 s i)) at 1.
  unfold R.v9138, N.v9138.
  rewrite ?node_9136.
  rewrite ?node_9137.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9139 (s : N.State) (i : N.Inputs) :
  R.v9139 (state s) (inputs i) = Zmod.unsigned (N.v9139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9139 s i)) at 1.
  unfold R.v9139, N.v9139.
  rewrite ?node_9135.
  rewrite ?node_9138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9140 (s : N.State) (i : N.Inputs) :
  R.v9140 (state s) (inputs i) = Zmod.unsigned (N.v9140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9140 s i)) at 1.
  unfold R.v9140, N.v9140.
  rewrite ?node_9132.
  rewrite ?node_9139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9141 (s : N.State) (i : N.Inputs) :
  R.v9141 (state s) (inputs i) = Zmod.unsigned (N.v9141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9141 s i)) at 1.
  unfold R.v9141, N.v9141.
  rewrite !state_r892_nr_5F892.
  rewrite !state_r893_nr_5F893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r892_nr_5F892 s)).
  rewrite ?(bits.mod_to_Z (N.r893_nr_5F893 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9142 (s : N.State) (i : N.Inputs) :
  R.v9142 (state s) (inputs i) = Zmod.unsigned (N.v9142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9142 s i)) at 1.
  unfold R.v9142, N.v9142.
  rewrite ?node_9141.
  rewrite !state_r894_nr_5F894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r894_nr_5F894 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9143 (s : N.State) (i : N.Inputs) :
  R.v9143 (state s) (inputs i) = Zmod.unsigned (N.v9143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9143 s i)) at 1.
  unfold R.v9143, N.v9143.
  rewrite ?node_9142.
  rewrite !state_r895_nr_5F895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r895_nr_5F895 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9144 (s : N.State) (i : N.Inputs) :
  R.v9144 (state s) (inputs i) = Zmod.unsigned (N.v9144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9144 s i)) at 1.
  unfold R.v9144, N.v9144.
  rewrite !state_r863_nr_5F863.
  rewrite !state_r864_nr_5F864.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r863_nr_5F863 s)).
  rewrite ?(bits.mod_to_Z (N.r864_nr_5F864 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9145 (s : N.State) (i : N.Inputs) :
  R.v9145 (state s) (inputs i) = Zmod.unsigned (N.v9145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9145 s i)) at 1.
  unfold R.v9145, N.v9145.
  rewrite ?node_9002.
  rewrite !state_r865_nr_5F865.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r865_nr_5F865 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9146 (s : N.State) (i : N.Inputs) :
  R.v9146 (state s) (inputs i) = Zmod.unsigned (N.v9146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9146 s i)) at 1.
  unfold R.v9146, N.v9146.
  rewrite ?node_9144.
  rewrite ?node_9145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9147 (s : N.State) (i : N.Inputs) :
  R.v9147 (state s) (inputs i) = Zmod.unsigned (N.v9147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9147 s i)) at 1.
  unfold R.v9147, N.v9147.
  rewrite ?node_9143.
  rewrite ?node_9146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9148 (s : N.State) (i : N.Inputs) :
  R.v9148 (state s) (inputs i) = Zmod.unsigned (N.v9148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9148 s i)) at 1.
  unfold R.v9148, N.v9148.
  rewrite ?node_9140.
  rewrite ?node_9147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9149 (s : N.State) (i : N.Inputs) :
  R.v9149 (state s) (inputs i) = Zmod.unsigned (N.v9149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9149 s i)) at 1.
  unfold R.v9149, N.v9149.
  rewrite !state_r896_nr_5F896.
  rewrite !state_r897_nr_5F897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r896_nr_5F896 s)).
  rewrite ?(bits.mod_to_Z (N.r897_nr_5F897 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9150 (s : N.State) (i : N.Inputs) :
  R.v9150 (state s) (inputs i) = Zmod.unsigned (N.v9150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9150 s i)) at 1.
  unfold R.v9150, N.v9150.
  rewrite ?node_9148.
  rewrite ?node_9149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9151 (s : N.State) (i : N.Inputs) :
  R.v9151 (state s) (inputs i) = Zmod.unsigned (N.v9151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9151 s i)) at 1.
  unfold R.v9151, N.v9151.
  rewrite ?node_8993.
  rewrite ?node_9000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9152 (s : N.State) (i : N.Inputs) :
  R.v9152 (state s) (inputs i) = Zmod.unsigned (N.v9152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9152 s i)) at 1.
  unfold R.v9152, N.v9152.
  rewrite ?node_9001.
  rewrite ?node_9008.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9153 (s : N.State) (i : N.Inputs) :
  R.v9153 (state s) (inputs i) = Zmod.unsigned (N.v9153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9153 s i)) at 1.
  unfold R.v9153, N.v9153.
  rewrite ?node_9151.
  rewrite ?node_9152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9154 (s : N.State) (i : N.Inputs) :
  R.v9154 (state s) (inputs i) = Zmod.unsigned (N.v9154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9154 s i)) at 1.
  unfold R.v9154, N.v9154.
  rewrite ?node_9150.
  rewrite ?node_9153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9155 (s : N.State) (i : N.Inputs) :
  R.v9155 (state s) (inputs i) = Zmod.unsigned (N.v9155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9155 s i)) at 1.
  unfold R.v9155, N.v9155.
  rewrite ?node_9125.
  rewrite ?node_9154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9156 (s : N.State) (i : N.Inputs) :
  R.v9156 (state s) (inputs i) = Zmod.unsigned (N.v9156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9156 s i)) at 1.
  unfold R.v9156, N.v9156.
  rewrite ?node_8953.
  rewrite !state_r842_nr_5F842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r842_nr_5F842 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9157 (s : N.State) (i : N.Inputs) :
  R.v9157 (state s) (inputs i) = Zmod.unsigned (N.v9157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9157 s i)) at 1.
  unfold R.v9157, N.v9157.
  rewrite ?node_8954.
  rewrite ?node_8957.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9158 (s : N.State) (i : N.Inputs) :
  R.v9158 (state s) (inputs i) = Zmod.unsigned (N.v9158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9158 s i)) at 1.
  unfold R.v9158, N.v9158.
  rewrite ?node_9156.
  rewrite ?node_9157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9159 (s : N.State) (i : N.Inputs) :
  R.v9159 (state s) (inputs i) = Zmod.unsigned (N.v9159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9159 s i)) at 1.
  unfold R.v9159, N.v9159.
  rewrite ?node_8960.
  rewrite !state_r846_nr_5F846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r846_nr_5F846 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9160 (s : N.State) (i : N.Inputs) :
  R.v9160 (state s) (inputs i) = Zmod.unsigned (N.v9160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9160 s i)) at 1.
  unfold R.v9160, N.v9160.
  rewrite ?node_8961.
  rewrite ?node_8964.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9161 (s : N.State) (i : N.Inputs) :
  R.v9161 (state s) (inputs i) = Zmod.unsigned (N.v9161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9161 s i)) at 1.
  unfold R.v9161, N.v9161.
  rewrite ?node_9159.
  rewrite ?node_9160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9162 (s : N.State) (i : N.Inputs) :
  R.v9162 (state s) (inputs i) = Zmod.unsigned (N.v9162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9162 s i)) at 1.
  unfold R.v9162, N.v9162.
  rewrite ?node_9158.
  rewrite ?node_9161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9163 (s : N.State) (i : N.Inputs) :
  R.v9163 (state s) (inputs i) = Zmod.unsigned (N.v9163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9163 s i)) at 1.
  unfold R.v9163, N.v9163.
  rewrite ?node_8968.
  rewrite !state_r850_nr_5F850.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r850_nr_5F850 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9164 (s : N.State) (i : N.Inputs) :
  R.v9164 (state s) (inputs i) = Zmod.unsigned (N.v9164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9164 s i)) at 1.
  unfold R.v9164, N.v9164.
  rewrite ?node_8969.
  rewrite ?node_8972.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9165 (s : N.State) (i : N.Inputs) :
  R.v9165 (state s) (inputs i) = Zmod.unsigned (N.v9165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9165 s i)) at 1.
  unfold R.v9165, N.v9165.
  rewrite ?node_9163.
  rewrite ?node_9164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9166 (s : N.State) (i : N.Inputs) :
  R.v9166 (state s) (inputs i) = Zmod.unsigned (N.v9166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9166 s i)) at 1.
  unfold R.v9166, N.v9166.
  rewrite ?node_9162.
  rewrite ?node_9165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9167 (s : N.State) (i : N.Inputs) :
  R.v9167 (state s) (inputs i) = Zmod.unsigned (N.v9167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9167 s i)) at 1.
  unfold R.v9167, N.v9167.
  rewrite ?node_8976.
  rewrite !state_r854_nr_5F854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r854_nr_5F854 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9168 (s : N.State) (i : N.Inputs) :
  R.v9168 (state s) (inputs i) = Zmod.unsigned (N.v9168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9168 s i)) at 1.
  unfold R.v9168, N.v9168.
  rewrite ?node_8977.
  rewrite ?node_8980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9169 (s : N.State) (i : N.Inputs) :
  R.v9169 (state s) (inputs i) = Zmod.unsigned (N.v9169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9169 s i)) at 1.
  unfold R.v9169, N.v9169.
  rewrite ?node_9167.
  rewrite ?node_9168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9170 (s : N.State) (i : N.Inputs) :
  R.v9170 (state s) (inputs i) = Zmod.unsigned (N.v9170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9170 s i)) at 1.
  unfold R.v9170, N.v9170.
  rewrite ?node_9166.
  rewrite ?node_9169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9171 (s : N.State) (i : N.Inputs) :
  R.v9171 (state s) (inputs i) = Zmod.unsigned (N.v9171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9171 s i)) at 1.
  unfold R.v9171, N.v9171.
  rewrite ?node_9018.
  rewrite ?node_9021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9172 (s : N.State) (i : N.Inputs) :
  R.v9172 (state s) (inputs i) = Zmod.unsigned (N.v9172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9172 s i)) at 1.
  unfold R.v9172, N.v9172.
  rewrite ?node_9022.
  rewrite ?node_9025.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9173 (s : N.State) (i : N.Inputs) :
  R.v9173 (state s) (inputs i) = Zmod.unsigned (N.v9173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9173 s i)) at 1.
  unfold R.v9173, N.v9173.
  rewrite ?node_9171.
  rewrite ?node_9172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9174 (s : N.State) (i : N.Inputs) :
  R.v9174 (state s) (inputs i) = Zmod.unsigned (N.v9174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9174 s i)) at 1.
  unfold R.v9174, N.v9174.
  rewrite ?node_9170.
  rewrite ?node_9173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9175 (s : N.State) (i : N.Inputs) :
  R.v9175 (state s) (inputs i) = Zmod.unsigned (N.v9175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9175 s i)) at 1.
  unfold R.v9175, N.v9175.
  rewrite ?node_9155.
  rewrite ?node_9174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9176 (s : N.State) (i : N.Inputs) :
  R.v9176 (state s) (inputs i) = Zmod.unsigned (N.v9176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9176 s i)) at 1.
  unfold R.v9176, N.v9176.
  rewrite ?node_8988.
  rewrite !state_r858_nr_5F858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r858_nr_5F858 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9177 (s : N.State) (i : N.Inputs) :
  R.v9177 (state s) (inputs i) = Zmod.unsigned (N.v9177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9177 s i)) at 1.
  unfold R.v9177, N.v9177.
  rewrite ?node_8989.
  rewrite ?node_8992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9178 (s : N.State) (i : N.Inputs) :
  R.v9178 (state s) (inputs i) = Zmod.unsigned (N.v9178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9178 s i)) at 1.
  unfold R.v9178, N.v9178.
  rewrite ?node_9176.
  rewrite ?node_9177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9179 (s : N.State) (i : N.Inputs) :
  R.v9179 (state s) (inputs i) = Zmod.unsigned (N.v9179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9179 s i)) at 1.
  unfold R.v9179, N.v9179.
  rewrite ?node_8995.
  rewrite !state_r862_nr_5F862.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r862_nr_5F862 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9180 (s : N.State) (i : N.Inputs) :
  R.v9180 (state s) (inputs i) = Zmod.unsigned (N.v9180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9180 s i)) at 1.
  unfold R.v9180, N.v9180.
  rewrite ?node_8996.
  rewrite ?node_8999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9181 (s : N.State) (i : N.Inputs) :
  R.v9181 (state s) (inputs i) = Zmod.unsigned (N.v9181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9181 s i)) at 1.
  unfold R.v9181, N.v9181.
  rewrite ?node_9179.
  rewrite ?node_9180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9182 (s : N.State) (i : N.Inputs) :
  R.v9182 (state s) (inputs i) = Zmod.unsigned (N.v9182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9182 s i)) at 1.
  unfold R.v9182, N.v9182.
  rewrite ?node_9178.
  rewrite ?node_9181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9183 (s : N.State) (i : N.Inputs) :
  R.v9183 (state s) (inputs i) = Zmod.unsigned (N.v9183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9183 s i)) at 1.
  unfold R.v9183, N.v9183.
  rewrite ?node_9003.
  rewrite !state_r866_nr_5F866.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r866_nr_5F866 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9184 (s : N.State) (i : N.Inputs) :
  R.v9184 (state s) (inputs i) = Zmod.unsigned (N.v9184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9184 s i)) at 1.
  unfold R.v9184, N.v9184.
  rewrite ?node_9004.
  rewrite ?node_9007.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9185 (s : N.State) (i : N.Inputs) :
  R.v9185 (state s) (inputs i) = Zmod.unsigned (N.v9185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9185 s i)) at 1.
  unfold R.v9185, N.v9185.
  rewrite ?node_9183.
  rewrite ?node_9184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9186 (s : N.State) (i : N.Inputs) :
  R.v9186 (state s) (inputs i) = Zmod.unsigned (N.v9186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9186 s i)) at 1.
  unfold R.v9186, N.v9186.
  rewrite ?node_9182.
  rewrite ?node_9185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9187 (s : N.State) (i : N.Inputs) :
  R.v9187 (state s) (inputs i) = Zmod.unsigned (N.v9187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9187 s i)) at 1.
  unfold R.v9187, N.v9187.
  rewrite ?node_9175.
  rewrite ?node_9186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9188 (s : N.State) (i : N.Inputs) :
  R.v9188 (state s) (inputs i) = Zmod.unsigned (N.v9188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9188 s i)) at 1.
  unfold R.v9188, N.v9188.
  rewrite ?node_8986.
  rewrite ?node_9014.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9189 (s : N.State) (i : N.Inputs) :
  R.v9189 (state s) (inputs i) = Zmod.unsigned (N.v9189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9189 s i)) at 1.
  unfold R.v9189, N.v9189.
  rewrite ?node_9015.
  rewrite ?node_9034.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9190 (s : N.State) (i : N.Inputs) :
  R.v9190 (state s) (inputs i) = Zmod.unsigned (N.v9190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9190 s i)) at 1.
  unfold R.v9190, N.v9190.
  rewrite ?node_9188.
  rewrite ?node_9189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9191 (s : N.State) (i : N.Inputs) :
  R.v9191 (state s) (inputs i) = Zmod.unsigned (N.v9191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9191 s i)) at 1.
  unfold R.v9191, N.v9191.
  rewrite ?node_9187.
  rewrite ?node_9190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9192 (s : N.State) (i : N.Inputs) :
  R.v9192 (state s) (inputs i) = Zmod.unsigned (N.v9192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9192 s i)) at 1.
  unfold R.v9192, N.v9192.
  rewrite ?node_8974.
  rewrite ?node_8981.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9193 (s : N.State) (i : N.Inputs) :
  R.v9193 (state s) (inputs i) = Zmod.unsigned (N.v9193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9193 s i)) at 1.
  unfold R.v9193, N.v9193.
  rewrite ?node_8982.
  rewrite ?node_8985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9194 (s : N.State) (i : N.Inputs) :
  R.v9194 (state s) (inputs i) = Zmod.unsigned (N.v9194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9194 s i)) at 1.
  unfold R.v9194, N.v9194.
  rewrite ?node_9192.
  rewrite ?node_9193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9195 (s : N.State) (i : N.Inputs) :
  R.v9195 (state s) (inputs i) = Zmod.unsigned (N.v9195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9195 s i)) at 1.
  unfold R.v9195, N.v9195.
  rewrite ?node_9009.
  rewrite !state_r867_nr_5F867.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r867_nr_5F867 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9196 (s : N.State) (i : N.Inputs) :
  R.v9196 (state s) (inputs i) = Zmod.unsigned (N.v9196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9196 s i)) at 1.
  unfold R.v9196, N.v9196.
  rewrite ?node_9010.
  rewrite ?node_9013.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9197 (s : N.State) (i : N.Inputs) :
  R.v9197 (state s) (inputs i) = Zmod.unsigned (N.v9197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9197 s i)) at 1.
  unfold R.v9197, N.v9197.
  rewrite ?node_9195.
  rewrite ?node_9196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9198 (s : N.State) (i : N.Inputs) :
  R.v9198 (state s) (inputs i) = Zmod.unsigned (N.v9198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9198 s i)) at 1.
  unfold R.v9198, N.v9198.
  rewrite ?node_9194.
  rewrite ?node_9197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9199 (s : N.State) (i : N.Inputs) :
  R.v9199 (state s) (inputs i) = Zmod.unsigned (N.v9199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9199 s i)) at 1.
  unfold R.v9199, N.v9199.
  rewrite ?node_9026.
  rewrite ?node_9029.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9200 (s : N.State) (i : N.Inputs) :
  R.v9200 (state s) (inputs i) = Zmod.unsigned (N.v9200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9200 s i)) at 1.
  unfold R.v9200, N.v9200.
  rewrite ?node_9030.
  rewrite ?node_9033.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9201 (s : N.State) (i : N.Inputs) :
  R.v9201 (state s) (inputs i) = Zmod.unsigned (N.v9201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9201 s i)) at 1.
  unfold R.v9201, N.v9201.
  rewrite ?node_9199.
  rewrite ?node_9200.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9202 (s : N.State) (i : N.Inputs) :
  R.v9202 (state s) (inputs i) = Zmod.unsigned (N.v9202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9202 s i)) at 1.
  unfold R.v9202, N.v9202.
  rewrite ?node_9198.
  rewrite ?node_9201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9203 (s : N.State) (i : N.Inputs) :
  R.v9203 (state s) (inputs i) = Zmod.unsigned (N.v9203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9203 s i)) at 1.
  unfold R.v9203, N.v9203.
  rewrite ?node_9038.
  rewrite ?node_9041.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9204 (s : N.State) (i : N.Inputs) :
  R.v9204 (state s) (inputs i) = Zmod.unsigned (N.v9204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9204 s i)) at 1.
  unfold R.v9204, N.v9204.
  rewrite ?node_9042.
  rewrite ?node_9045.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9205 (s : N.State) (i : N.Inputs) :
  R.v9205 (state s) (inputs i) = Zmod.unsigned (N.v9205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9205 s i)) at 1.
  unfold R.v9205, N.v9205.
  rewrite ?node_9203.
  rewrite ?node_9204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9206 (s : N.State) (i : N.Inputs) :
  R.v9206 (state s) (inputs i) = Zmod.unsigned (N.v9206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9206 s i)) at 1.
  unfold R.v9206, N.v9206.
  rewrite ?node_9202.
  rewrite ?node_9205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9207 (s : N.State) (i : N.Inputs) :
  R.v9207 (state s) (inputs i) = Zmod.unsigned (N.v9207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9207 s i)) at 1.
  unfold R.v9207, N.v9207.
  rewrite ?node_9054.
  rewrite ?node_9057.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9208 (s : N.State) (i : N.Inputs) :
  R.v9208 (state s) (inputs i) = Zmod.unsigned (N.v9208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9208 s i)) at 1.
  unfold R.v9208, N.v9208.
  rewrite ?node_9058.
  rewrite ?node_9061.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9209 (s : N.State) (i : N.Inputs) :
  R.v9209 (state s) (inputs i) = Zmod.unsigned (N.v9209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9209 s i)) at 1.
  unfold R.v9209, N.v9209.
  rewrite ?node_9207.
  rewrite ?node_9208.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9210 (s : N.State) (i : N.Inputs) :
  R.v9210 (state s) (inputs i) = Zmod.unsigned (N.v9210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9210 s i)) at 1.
  unfold R.v9210, N.v9210.
  rewrite ?node_9206.
  rewrite ?node_9209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9211 (s : N.State) (i : N.Inputs) :
  R.v9211 (state s) (inputs i) = Zmod.unsigned (N.v9211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9211 s i)) at 1.
  unfold R.v9211, N.v9211.
  rewrite ?node_9191.
  rewrite ?node_9210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9212 (s : N.State) (i : N.Inputs) :
  R.v9212 (state s) (inputs i) = Zmod.unsigned (N.v9212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9212 s i)) at 1.
  unfold R.v9212, N.v9212.
  rewrite ?node_9035.
  rewrite ?node_9046.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9213 (s : N.State) (i : N.Inputs) :
  R.v9213 (state s) (inputs i) = Zmod.unsigned (N.v9213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9213 s i)) at 1.
  unfold R.v9213, N.v9213.
  rewrite ?node_9047.
  rewrite ?node_9050.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9214 (s : N.State) (i : N.Inputs) :
  R.v9214 (state s) (inputs i) = Zmod.unsigned (N.v9214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9214 s i)) at 1.
  unfold R.v9214, N.v9214.
  rewrite ?node_9212.
  rewrite ?node_9213.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9215 (s : N.State) (i : N.Inputs) :
  R.v9215 (state s) (inputs i) = Zmod.unsigned (N.v9215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9215 s i)) at 1.
  unfold R.v9215, N.v9215.
  rewrite ?node_9211.
  rewrite ?node_9214.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9216 (s : N.State) (i : N.Inputs) :
  R.v9216 (state s) (inputs i) = Zmod.unsigned (N.v9216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9216 s i)) at 1.
  unfold R.v9216, N.v9216.
  rewrite ?node_9062.
  rewrite ?node_9065.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9217 (s : N.State) (i : N.Inputs) :
  R.v9217 (state s) (inputs i) = Zmod.unsigned (N.v9217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9217 s i)) at 1.
  unfold R.v9217, N.v9217.
  rewrite ?node_9066.
  rewrite ?node_9069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9218 (s : N.State) (i : N.Inputs) :
  R.v9218 (state s) (inputs i) = Zmod.unsigned (N.v9218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9218 s i)) at 1.
  unfold R.v9218, N.v9218.
  rewrite ?node_9216.
  rewrite ?node_9217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9219 (s : N.State) (i : N.Inputs) :
  R.v9219 (state s) (inputs i) = Zmod.unsigned (N.v9219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9219 s i)) at 1.
  unfold R.v9219, N.v9219.
  rewrite ?node_9215.
  rewrite ?node_9218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9220 (s : N.State) (i : N.Inputs) :
  R.v9220 (state s) (inputs i) = Zmod.unsigned (N.v9220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9220 s i)) at 1.
  unfold R.v9220, N.v9220.
  rewrite ?node_9051.
  rewrite ?node_9070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9221 (s : N.State) (i : N.Inputs) :
  R.v9221 (state s) (inputs i) = Zmod.unsigned (N.v9221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9221 s i)) at 1.
  unfold R.v9221, N.v9221.
  rewrite ?node_9071.
  rewrite ?node_9074.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9222 (s : N.State) (i : N.Inputs) :
  R.v9222 (state s) (inputs i) = Zmod.unsigned (N.v9222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9222 s i)) at 1.
  unfold R.v9222, N.v9222.
  rewrite ?node_9220.
  rewrite ?node_9221.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9223 (s : N.State) (i : N.Inputs) :
  R.v9223 (state s) (inputs i) = Zmod.unsigned (N.v9223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9223 s i)) at 1.
  unfold R.v9223, N.v9223.
  rewrite ?node_9219.
  rewrite ?node_9222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9224 (s : N.State) (i : N.Inputs) :
  R.v9224 (state s) (inputs i) = Zmod.unsigned (N.v9224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9224 s i)) at 1.
  unfold R.v9224, N.v9224.
  rewrite ?node_9075.
  rewrite ?node_9078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9225 (s : N.State) (i : N.Inputs) :
  R.v9225 (state s) (inputs i) = Zmod.unsigned (N.v9225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9225 s i)) at 1.
  unfold R.v9225, N.v9225.
  rewrite ?node_9079.
  rewrite ?node_9082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9226 (s : N.State) (i : N.Inputs) :
  R.v9226 (state s) (inputs i) = Zmod.unsigned (N.v9226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9226 s i)) at 1.
  unfold R.v9226, N.v9226.
  rewrite ?node_9224.
  rewrite ?node_9225.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9227 (s : N.State) (i : N.Inputs) :
  R.v9227 (state s) (inputs i) = Zmod.unsigned (N.v9227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9227 s i)) at 1.
  unfold R.v9227, N.v9227.
  rewrite ?node_9223.
  rewrite ?node_9226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9228 (s : N.State) (i : N.Inputs) :
  R.v9228 (state s) (inputs i) = Zmod.unsigned (N.v9228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9228 s i)) at 1.
  unfold R.v9228, N.v9228.
  rewrite ?node_9227.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2385_nr_5F2416.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2385_nr_5F2416 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9229 (s : N.State) (i : N.Inputs) :
  R.v9229 (state s) (inputs i) = Zmod.unsigned (N.v9229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9229 s i)) at 1.
  unfold R.v9229, N.v9229.
  rewrite ?node_9083.
  rewrite ?node_9086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9230 (s : N.State) (i : N.Inputs) :
  R.v9230 (state s) (inputs i) = Zmod.unsigned (N.v9230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9230 s i)) at 1.
  unfold R.v9230, N.v9230.
  rewrite ?node_9229.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2386_nr_5F2417.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2386_nr_5F2417 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9231 (s : N.State) (i : N.Inputs) :
  R.v9231 (state s) (inputs i) = Zmod.unsigned (N.v9231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9231 s i)) at 1.
  unfold R.v9231, N.v9231.
  rewrite !state_r898_nr_5F898.
  rewrite !state_r899_nr_5F899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r898_nr_5F898 s)).
  rewrite ?(bits.mod_to_Z (N.r899_nr_5F899 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9232 (s : N.State) (i : N.Inputs) :
  R.v9232 (state s) (inputs i) = Zmod.unsigned (N.v9232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9232 s i)) at 1.
  unfold R.v9232, N.v9232.
  rewrite ?node_9231.
  rewrite !state_r900_nr_5F900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r900_nr_5F900 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9233 (s : N.State) (i : N.Inputs) :
  R.v9233 (state s) (inputs i) = Zmod.unsigned (N.v9233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9233 s i)) at 1.
  unfold R.v9233, N.v9233.
  rewrite ?node_9232.
  rewrite !state_r901_nr_5F901.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r901_nr_5F901 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9234 (s : N.State) (i : N.Inputs) :
  R.v9234 (state s) (inputs i) = Zmod.unsigned (N.v9234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9234 s i)) at 1.
  unfold R.v9234, N.v9234.
  rewrite !state_r868_nr_5F868.
  rewrite !state_r869_nr_5F869.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r868_nr_5F868 s)).
  rewrite ?(bits.mod_to_Z (N.r869_nr_5F869 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9235 (s : N.State) (i : N.Inputs) :
  R.v9235 (state s) (inputs i) = Zmod.unsigned (N.v9235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9235 s i)) at 1.
  unfold R.v9235, N.v9235.
  rewrite ?node_9091.
  rewrite !state_r870_nr_5F870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r870_nr_5F870 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9236 (s : N.State) (i : N.Inputs) :
  R.v9236 (state s) (inputs i) = Zmod.unsigned (N.v9236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9236 s i)) at 1.
  unfold R.v9236, N.v9236.
  rewrite ?node_9234.
  rewrite ?node_9235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9237 (s : N.State) (i : N.Inputs) :
  R.v9237 (state s) (inputs i) = Zmod.unsigned (N.v9237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9237 s i)) at 1.
  unfold R.v9237, N.v9237.
  rewrite ?node_9233.
  rewrite ?node_9236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9238 (s : N.State) (i : N.Inputs) :
  R.v9238 (state s) (inputs i) = Zmod.unsigned (N.v9238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9238 s i)) at 1.
  unfold R.v9238, N.v9238.
  rewrite !state_r902_nr_5F902.
  rewrite !state_r903_nr_5F903.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r902_nr_5F902 s)).
  rewrite ?(bits.mod_to_Z (N.r903_nr_5F903 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9239 (s : N.State) (i : N.Inputs) :
  R.v9239 (state s) (inputs i) = Zmod.unsigned (N.v9239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9239 s i)) at 1.
  unfold R.v9239, N.v9239.
  rewrite ?node_9238.
  rewrite !state_r904_nr_5F904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r904_nr_5F904 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9240 (s : N.State) (i : N.Inputs) :
  R.v9240 (state s) (inputs i) = Zmod.unsigned (N.v9240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9240 s i)) at 1.
  unfold R.v9240, N.v9240.
  rewrite ?node_9239.
  rewrite !state_r905_nr_5F905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r905_nr_5F905 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9241 (s : N.State) (i : N.Inputs) :
  R.v9241 (state s) (inputs i) = Zmod.unsigned (N.v9241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9241 s i)) at 1.
  unfold R.v9241, N.v9241.
  rewrite !state_r872_nr_5F872.
  rewrite !state_r873_nr_5F873.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r872_nr_5F872 s)).
  rewrite ?(bits.mod_to_Z (N.r873_nr_5F873 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9242 (s : N.State) (i : N.Inputs) :
  R.v9242 (state s) (inputs i) = Zmod.unsigned (N.v9242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9242 s i)) at 1.
  unfold R.v9242, N.v9242.
  rewrite ?node_9098.
  rewrite !state_r874_nr_5F874.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r874_nr_5F874 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9243 (s : N.State) (i : N.Inputs) :
  R.v9243 (state s) (inputs i) = Zmod.unsigned (N.v9243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9243 s i)) at 1.
  unfold R.v9243, N.v9243.
  rewrite ?node_9241.
  rewrite ?node_9242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9244 (s : N.State) (i : N.Inputs) :
  R.v9244 (state s) (inputs i) = Zmod.unsigned (N.v9244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9244 s i)) at 1.
  unfold R.v9244, N.v9244.
  rewrite ?node_9240.
  rewrite ?node_9243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9245 (s : N.State) (i : N.Inputs) :
  R.v9245 (state s) (inputs i) = Zmod.unsigned (N.v9245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9245 s i)) at 1.
  unfold R.v9245, N.v9245.
  rewrite ?node_9237.
  rewrite ?node_9244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9246 (s : N.State) (i : N.Inputs) :
  R.v9246 (state s) (inputs i) = Zmod.unsigned (N.v9246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9246 s i)) at 1.
  unfold R.v9246, N.v9246.
  rewrite !state_r906_nr_5F906.
  rewrite !state_r907_nr_5F907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r906_nr_5F906 s)).
  rewrite ?(bits.mod_to_Z (N.r907_nr_5F907 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9247 (s : N.State) (i : N.Inputs) :
  R.v9247 (state s) (inputs i) = Zmod.unsigned (N.v9247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9247 s i)) at 1.
  unfold R.v9247, N.v9247.
  rewrite ?node_9246.
  rewrite !state_r908_nr_5F908.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r908_nr_5F908 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9248 (s : N.State) (i : N.Inputs) :
  R.v9248 (state s) (inputs i) = Zmod.unsigned (N.v9248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9248 s i)) at 1.
  unfold R.v9248, N.v9248.
  rewrite ?node_9247.
  rewrite !state_r909_nr_5F909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r909_nr_5F909 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9249 (s : N.State) (i : N.Inputs) :
  R.v9249 (state s) (inputs i) = Zmod.unsigned (N.v9249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9249 s i)) at 1.
  unfold R.v9249, N.v9249.
  rewrite !state_r876_nr_5F876.
  rewrite !state_r877_nr_5F877.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r876_nr_5F876 s)).
  rewrite ?(bits.mod_to_Z (N.r877_nr_5F877 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9250 (s : N.State) (i : N.Inputs) :
  R.v9250 (state s) (inputs i) = Zmod.unsigned (N.v9250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9250 s i)) at 1.
  unfold R.v9250, N.v9250.
  rewrite ?node_9106.
  rewrite !state_r878_nr_5F878.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r878_nr_5F878 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9251 (s : N.State) (i : N.Inputs) :
  R.v9251 (state s) (inputs i) = Zmod.unsigned (N.v9251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9251 s i)) at 1.
  unfold R.v9251, N.v9251.
  rewrite ?node_9249.
  rewrite ?node_9250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9252 (s : N.State) (i : N.Inputs) :
  R.v9252 (state s) (inputs i) = Zmod.unsigned (N.v9252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9252 s i)) at 1.
  unfold R.v9252, N.v9252.
  rewrite ?node_9248.
  rewrite ?node_9251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9253 (s : N.State) (i : N.Inputs) :
  R.v9253 (state s) (inputs i) = Zmod.unsigned (N.v9253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9253 s i)) at 1.
  unfold R.v9253, N.v9253.
  rewrite ?node_9245.
  rewrite ?node_9252.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9254 (s : N.State) (i : N.Inputs) :
  R.v9254 (state s) (inputs i) = Zmod.unsigned (N.v9254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9254 s i)) at 1.
  unfold R.v9254, N.v9254.
  rewrite !state_r910_nr_5F910.
  rewrite !state_r911_nr_5F911.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r910_nr_5F910 s)).
  rewrite ?(bits.mod_to_Z (N.r911_nr_5F911 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9255 (s : N.State) (i : N.Inputs) :
  R.v9255 (state s) (inputs i) = Zmod.unsigned (N.v9255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9255 s i)) at 1.
  unfold R.v9255, N.v9255.
  rewrite ?node_9254.
  rewrite !state_r912_nr_5F912.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r912_nr_5F912 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9256 (s : N.State) (i : N.Inputs) :
  R.v9256 (state s) (inputs i) = Zmod.unsigned (N.v9256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9256 s i)) at 1.
  unfold R.v9256, N.v9256.
  rewrite ?node_9255.
  rewrite !state_r913_nr_5F913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r913_nr_5F913 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9257 (s : N.State) (i : N.Inputs) :
  R.v9257 (state s) (inputs i) = Zmod.unsigned (N.v9257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9257 s i)) at 1.
  unfold R.v9257, N.v9257.
  rewrite !state_r880_nr_5F880.
  rewrite !state_r881_nr_5F881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r880_nr_5F880 s)).
  rewrite ?(bits.mod_to_Z (N.r881_nr_5F881 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9258 (s : N.State) (i : N.Inputs) :
  R.v9258 (state s) (inputs i) = Zmod.unsigned (N.v9258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9258 s i)) at 1.
  unfold R.v9258, N.v9258.
  rewrite ?node_9114.
  rewrite !state_r882_nr_5F882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r882_nr_5F882 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9259 (s : N.State) (i : N.Inputs) :
  R.v9259 (state s) (inputs i) = Zmod.unsigned (N.v9259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9259 s i)) at 1.
  unfold R.v9259, N.v9259.
  rewrite ?node_9257.
  rewrite ?node_9258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9260 (s : N.State) (i : N.Inputs) :
  R.v9260 (state s) (inputs i) = Zmod.unsigned (N.v9260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9260 s i)) at 1.
  unfold R.v9260, N.v9260.
  rewrite ?node_9256.
  rewrite ?node_9259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9261 (s : N.State) (i : N.Inputs) :
  R.v9261 (state s) (inputs i) = Zmod.unsigned (N.v9261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9261 s i)) at 1.
  unfold R.v9261, N.v9261.
  rewrite ?node_9253.
  rewrite ?node_9260.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9262 (s : N.State) (i : N.Inputs) :
  R.v9262 (state s) (inputs i) = Zmod.unsigned (N.v9262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9262 s i)) at 1.
  unfold R.v9262, N.v9262.
  rewrite ?node_9097.
  rewrite ?node_9104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9263 (s : N.State) (i : N.Inputs) :
  R.v9263 (state s) (inputs i) = Zmod.unsigned (N.v9263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9263 s i)) at 1.
  unfold R.v9263, N.v9263.
  rewrite ?node_9105.
  rewrite ?node_9112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9264 (s : N.State) (i : N.Inputs) :
  R.v9264 (state s) (inputs i) = Zmod.unsigned (N.v9264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9264 s i)) at 1.
  unfold R.v9264, N.v9264.
  rewrite ?node_9262.
  rewrite ?node_9263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9265 (s : N.State) (i : N.Inputs) :
  R.v9265 (state s) (inputs i) = Zmod.unsigned (N.v9265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9265 s i)) at 1.
  unfold R.v9265, N.v9265.
  rewrite ?node_9261.
  rewrite ?node_9264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9266 (s : N.State) (i : N.Inputs) :
  R.v9266 (state s) (inputs i) = Zmod.unsigned (N.v9266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9266 s i)) at 1.
  unfold R.v9266, N.v9266.
  rewrite !state_r914_nr_5F914.
  rewrite !state_r915_nr_5F915.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r914_nr_5F914 s)).
  rewrite ?(bits.mod_to_Z (N.r915_nr_5F915 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9267 (s : N.State) (i : N.Inputs) :
  R.v9267 (state s) (inputs i) = Zmod.unsigned (N.v9267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9267 s i)) at 1.
  unfold R.v9267, N.v9267.
  rewrite ?node_9266.
  rewrite !state_r916_nr_5F916.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r916_nr_5F916 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9268 (s : N.State) (i : N.Inputs) :
  R.v9268 (state s) (inputs i) = Zmod.unsigned (N.v9268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9268 s i)) at 1.
  unfold R.v9268, N.v9268.
  rewrite ?node_9267.
  rewrite !state_r917_nr_5F917.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r917_nr_5F917 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9269 (s : N.State) (i : N.Inputs) :
  R.v9269 (state s) (inputs i) = Zmod.unsigned (N.v9269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9269 s i)) at 1.
  unfold R.v9269, N.v9269.
  rewrite !state_r884_nr_5F884.
  rewrite !state_r885_nr_5F885.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r884_nr_5F884 s)).
  rewrite ?(bits.mod_to_Z (N.r885_nr_5F885 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9270 (s : N.State) (i : N.Inputs) :
  R.v9270 (state s) (inputs i) = Zmod.unsigned (N.v9270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9270 s i)) at 1.
  unfold R.v9270, N.v9270.
  rewrite ?node_9126.
  rewrite !state_r886_nr_5F886.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r886_nr_5F886 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9271 (s : N.State) (i : N.Inputs) :
  R.v9271 (state s) (inputs i) = Zmod.unsigned (N.v9271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9271 s i)) at 1.
  unfold R.v9271, N.v9271.
  rewrite ?node_9269.
  rewrite ?node_9270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9272 (s : N.State) (i : N.Inputs) :
  R.v9272 (state s) (inputs i) = Zmod.unsigned (N.v9272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9272 s i)) at 1.
  unfold R.v9272, N.v9272.
  rewrite ?node_9268.
  rewrite ?node_9271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9273 (s : N.State) (i : N.Inputs) :
  R.v9273 (state s) (inputs i) = Zmod.unsigned (N.v9273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9273 s i)) at 1.
  unfold R.v9273, N.v9273.
  rewrite !state_r918_nr_5F918.
  rewrite !state_r919_nr_5F919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r918_nr_5F918 s)).
  rewrite ?(bits.mod_to_Z (N.r919_nr_5F919 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9274 (s : N.State) (i : N.Inputs) :
  R.v9274 (state s) (inputs i) = Zmod.unsigned (N.v9274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9274 s i)) at 1.
  unfold R.v9274, N.v9274.
  rewrite ?node_9273.
  rewrite !state_r920_nr_5F920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r920_nr_5F920 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9275 (s : N.State) (i : N.Inputs) :
  R.v9275 (state s) (inputs i) = Zmod.unsigned (N.v9275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9275 s i)) at 1.
  unfold R.v9275, N.v9275.
  rewrite ?node_9274.
  rewrite !state_r921_nr_5F921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r921_nr_5F921 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9276 (s : N.State) (i : N.Inputs) :
  R.v9276 (state s) (inputs i) = Zmod.unsigned (N.v9276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9276 s i)) at 1.
  unfold R.v9276, N.v9276.
  rewrite !state_r888_nr_5F888.
  rewrite !state_r889_nr_5F889.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r888_nr_5F888 s)).
  rewrite ?(bits.mod_to_Z (N.r889_nr_5F889 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9277 (s : N.State) (i : N.Inputs) :
  R.v9277 (state s) (inputs i) = Zmod.unsigned (N.v9277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9277 s i)) at 1.
  unfold R.v9277, N.v9277.
  rewrite ?node_9133.
  rewrite !state_r890_nr_5F890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r890_nr_5F890 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9278 (s : N.State) (i : N.Inputs) :
  R.v9278 (state s) (inputs i) = Zmod.unsigned (N.v9278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9278 s i)) at 1.
  unfold R.v9278, N.v9278.
  rewrite ?node_9276.
  rewrite ?node_9277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9279 (s : N.State) (i : N.Inputs) :
  R.v9279 (state s) (inputs i) = Zmod.unsigned (N.v9279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9279 s i)) at 1.
  unfold R.v9279, N.v9279.
  rewrite ?node_9275.
  rewrite ?node_9278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9280 (s : N.State) (i : N.Inputs) :
  R.v9280 (state s) (inputs i) = Zmod.unsigned (N.v9280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9280 s i)) at 1.
  unfold R.v9280, N.v9280.
  rewrite ?node_9272.
  rewrite ?node_9279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9281 (s : N.State) (i : N.Inputs) :
  R.v9281 (state s) (inputs i) = Zmod.unsigned (N.v9281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9281 s i)) at 1.
  unfold R.v9281, N.v9281.
  rewrite !state_r922_nr_5F922.
  rewrite !state_r923_nr_5F923.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r922_nr_5F922 s)).
  rewrite ?(bits.mod_to_Z (N.r923_nr_5F923 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9282 (s : N.State) (i : N.Inputs) :
  R.v9282 (state s) (inputs i) = Zmod.unsigned (N.v9282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9282 s i)) at 1.
  unfold R.v9282, N.v9282.
  rewrite ?node_9281.
  rewrite !state_r924_nr_5F924.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r924_nr_5F924 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9283 (s : N.State) (i : N.Inputs) :
  R.v9283 (state s) (inputs i) = Zmod.unsigned (N.v9283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9283 s i)) at 1.
  unfold R.v9283, N.v9283.
  rewrite ?node_9282.
  rewrite !state_r925_nr_5F925.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r925_nr_5F925 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9284 (s : N.State) (i : N.Inputs) :
  R.v9284 (state s) (inputs i) = Zmod.unsigned (N.v9284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9284 s i)) at 1.
  unfold R.v9284, N.v9284.
  rewrite !state_r892_nr_5F892.
  rewrite !state_r893_nr_5F893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r892_nr_5F892 s)).
  rewrite ?(bits.mod_to_Z (N.r893_nr_5F893 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9285 (s : N.State) (i : N.Inputs) :
  R.v9285 (state s) (inputs i) = Zmod.unsigned (N.v9285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9285 s i)) at 1.
  unfold R.v9285, N.v9285.
  rewrite ?node_9141.
  rewrite !state_r894_nr_5F894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r894_nr_5F894 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9286 (s : N.State) (i : N.Inputs) :
  R.v9286 (state s) (inputs i) = Zmod.unsigned (N.v9286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9286 s i)) at 1.
  unfold R.v9286, N.v9286.
  rewrite ?node_9284.
  rewrite ?node_9285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9287 (s : N.State) (i : N.Inputs) :
  R.v9287 (state s) (inputs i) = Zmod.unsigned (N.v9287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9287 s i)) at 1.
  unfold R.v9287, N.v9287.
  rewrite ?node_9283.
  rewrite ?node_9286.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9288 (s : N.State) (i : N.Inputs) :
  R.v9288 (state s) (inputs i) = Zmod.unsigned (N.v9288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9288 s i)) at 1.
  unfold R.v9288, N.v9288.
  rewrite ?node_9280.
  rewrite ?node_9287.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9289 (s : N.State) (i : N.Inputs) :
  R.v9289 (state s) (inputs i) = Zmod.unsigned (N.v9289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9289 s i)) at 1.
  unfold R.v9289, N.v9289.
  rewrite !state_r926_nr_5F926.
  rewrite !state_r927_nr_5F927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r926_nr_5F926 s)).
  rewrite ?(bits.mod_to_Z (N.r927_nr_5F927 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9290 (s : N.State) (i : N.Inputs) :
  R.v9290 (state s) (inputs i) = Zmod.unsigned (N.v9290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9290 s i)) at 1.
  unfold R.v9290, N.v9290.
  rewrite ?node_9288.
  rewrite ?node_9289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9291 (s : N.State) (i : N.Inputs) :
  R.v9291 (state s) (inputs i) = Zmod.unsigned (N.v9291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9291 s i)) at 1.
  unfold R.v9291, N.v9291.
  rewrite ?node_9132.
  rewrite ?node_9139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9292 (s : N.State) (i : N.Inputs) :
  R.v9292 (state s) (inputs i) = Zmod.unsigned (N.v9292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9292 s i)) at 1.
  unfold R.v9292, N.v9292.
  rewrite ?node_9140.
  rewrite ?node_9147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9293 (s : N.State) (i : N.Inputs) :
  R.v9293 (state s) (inputs i) = Zmod.unsigned (N.v9293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9293 s i)) at 1.
  unfold R.v9293, N.v9293.
  rewrite ?node_9291.
  rewrite ?node_9292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9294 (s : N.State) (i : N.Inputs) :
  R.v9294 (state s) (inputs i) = Zmod.unsigned (N.v9294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9294 s i)) at 1.
  unfold R.v9294, N.v9294.
  rewrite ?node_9290.
  rewrite ?node_9293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9295 (s : N.State) (i : N.Inputs) :
  R.v9295 (state s) (inputs i) = Zmod.unsigned (N.v9295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9295 s i)) at 1.
  unfold R.v9295, N.v9295.
  rewrite ?node_9265.
  rewrite ?node_9294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9296 (s : N.State) (i : N.Inputs) :
  R.v9296 (state s) (inputs i) = Zmod.unsigned (N.v9296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9296 s i)) at 1.
  unfold R.v9296, N.v9296.
  rewrite ?node_9092.
  rewrite !state_r871_nr_5F871.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r871_nr_5F871 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9297 (s : N.State) (i : N.Inputs) :
  R.v9297 (state s) (inputs i) = Zmod.unsigned (N.v9297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9297 s i)) at 1.
  unfold R.v9297, N.v9297.
  rewrite ?node_9093.
  rewrite ?node_9096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9298 (s : N.State) (i : N.Inputs) :
  R.v9298 (state s) (inputs i) = Zmod.unsigned (N.v9298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9298 s i)) at 1.
  unfold R.v9298, N.v9298.
  rewrite ?node_9296.
  rewrite ?node_9297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9299 (s : N.State) (i : N.Inputs) :
  R.v9299 (state s) (inputs i) = Zmod.unsigned (N.v9299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9299 s i)) at 1.
  unfold R.v9299, N.v9299.
  rewrite ?node_9099.
  rewrite !state_r875_nr_5F875.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r875_nr_5F875 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9300 (s : N.State) (i : N.Inputs) :
  R.v9300 (state s) (inputs i) = Zmod.unsigned (N.v9300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9300 s i)) at 1.
  unfold R.v9300, N.v9300.
  rewrite ?node_9100.
  rewrite ?node_9103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9301 (s : N.State) (i : N.Inputs) :
  R.v9301 (state s) (inputs i) = Zmod.unsigned (N.v9301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9301 s i)) at 1.
  unfold R.v9301, N.v9301.
  rewrite ?node_9299.
  rewrite ?node_9300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9302 (s : N.State) (i : N.Inputs) :
  R.v9302 (state s) (inputs i) = Zmod.unsigned (N.v9302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9302 s i)) at 1.
  unfold R.v9302, N.v9302.
  rewrite ?node_9298.
  rewrite ?node_9301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9303 (s : N.State) (i : N.Inputs) :
  R.v9303 (state s) (inputs i) = Zmod.unsigned (N.v9303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9303 s i)) at 1.
  unfold R.v9303, N.v9303.
  rewrite ?node_9107.
  rewrite !state_r879_nr_5F879.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r879_nr_5F879 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9304 (s : N.State) (i : N.Inputs) :
  R.v9304 (state s) (inputs i) = Zmod.unsigned (N.v9304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9304 s i)) at 1.
  unfold R.v9304, N.v9304.
  rewrite ?node_9108.
  rewrite ?node_9111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9305 (s : N.State) (i : N.Inputs) :
  R.v9305 (state s) (inputs i) = Zmod.unsigned (N.v9305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9305 s i)) at 1.
  unfold R.v9305, N.v9305.
  rewrite ?node_9303.
  rewrite ?node_9304.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9306 (s : N.State) (i : N.Inputs) :
  R.v9306 (state s) (inputs i) = Zmod.unsigned (N.v9306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9306 s i)) at 1.
  unfold R.v9306, N.v9306.
  rewrite ?node_9302.
  rewrite ?node_9305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9307 (s : N.State) (i : N.Inputs) :
  R.v9307 (state s) (inputs i) = Zmod.unsigned (N.v9307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9307 s i)) at 1.
  unfold R.v9307, N.v9307.
  rewrite ?node_9115.
  rewrite !state_r883_nr_5F883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r883_nr_5F883 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9308 (s : N.State) (i : N.Inputs) :
  R.v9308 (state s) (inputs i) = Zmod.unsigned (N.v9308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9308 s i)) at 1.
  unfold R.v9308, N.v9308.
  rewrite ?node_9116.
  rewrite ?node_9119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9309 (s : N.State) (i : N.Inputs) :
  R.v9309 (state s) (inputs i) = Zmod.unsigned (N.v9309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9309 s i)) at 1.
  unfold R.v9309, N.v9309.
  rewrite ?node_9307.
  rewrite ?node_9308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9310 (s : N.State) (i : N.Inputs) :
  R.v9310 (state s) (inputs i) = Zmod.unsigned (N.v9310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9310 s i)) at 1.
  unfold R.v9310, N.v9310.
  rewrite ?node_9306.
  rewrite ?node_9309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9311 (s : N.State) (i : N.Inputs) :
  R.v9311 (state s) (inputs i) = Zmod.unsigned (N.v9311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9311 s i)) at 1.
  unfold R.v9311, N.v9311.
  rewrite ?node_9158.
  rewrite ?node_9161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9312 (s : N.State) (i : N.Inputs) :
  R.v9312 (state s) (inputs i) = Zmod.unsigned (N.v9312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9312 s i)) at 1.
  unfold R.v9312, N.v9312.
  rewrite ?node_9162.
  rewrite ?node_9165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9313 (s : N.State) (i : N.Inputs) :
  R.v9313 (state s) (inputs i) = Zmod.unsigned (N.v9313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9313 s i)) at 1.
  unfold R.v9313, N.v9313.
  rewrite ?node_9311.
  rewrite ?node_9312.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9314 (s : N.State) (i : N.Inputs) :
  R.v9314 (state s) (inputs i) = Zmod.unsigned (N.v9314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9314 s i)) at 1.
  unfold R.v9314, N.v9314.
  rewrite ?node_9310.
  rewrite ?node_9313.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9315 (s : N.State) (i : N.Inputs) :
  R.v9315 (state s) (inputs i) = Zmod.unsigned (N.v9315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9315 s i)) at 1.
  unfold R.v9315, N.v9315.
  rewrite ?node_9295.
  rewrite ?node_9314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9316 (s : N.State) (i : N.Inputs) :
  R.v9316 (state s) (inputs i) = Zmod.unsigned (N.v9316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9316 s i)) at 1.
  unfold R.v9316, N.v9316.
  rewrite ?node_9127.
  rewrite !state_r887_nr_5F887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r887_nr_5F887 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9317 (s : N.State) (i : N.Inputs) :
  R.v9317 (state s) (inputs i) = Zmod.unsigned (N.v9317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9317 s i)) at 1.
  unfold R.v9317, N.v9317.
  rewrite ?node_9128.
  rewrite ?node_9131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9318 (s : N.State) (i : N.Inputs) :
  R.v9318 (state s) (inputs i) = Zmod.unsigned (N.v9318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9318 s i)) at 1.
  unfold R.v9318, N.v9318.
  rewrite ?node_9316.
  rewrite ?node_9317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9319 (s : N.State) (i : N.Inputs) :
  R.v9319 (state s) (inputs i) = Zmod.unsigned (N.v9319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9319 s i)) at 1.
  unfold R.v9319, N.v9319.
  rewrite ?node_9134.
  rewrite !state_r891_nr_5F891.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r891_nr_5F891 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9320 (s : N.State) (i : N.Inputs) :
  R.v9320 (state s) (inputs i) = Zmod.unsigned (N.v9320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9320 s i)) at 1.
  unfold R.v9320, N.v9320.
  rewrite ?node_9135.
  rewrite ?node_9138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9321 (s : N.State) (i : N.Inputs) :
  R.v9321 (state s) (inputs i) = Zmod.unsigned (N.v9321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9321 s i)) at 1.
  unfold R.v9321, N.v9321.
  rewrite ?node_9319.
  rewrite ?node_9320.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9322 (s : N.State) (i : N.Inputs) :
  R.v9322 (state s) (inputs i) = Zmod.unsigned (N.v9322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9322 s i)) at 1.
  unfold R.v9322, N.v9322.
  rewrite ?node_9318.
  rewrite ?node_9321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9323 (s : N.State) (i : N.Inputs) :
  R.v9323 (state s) (inputs i) = Zmod.unsigned (N.v9323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9323 s i)) at 1.
  unfold R.v9323, N.v9323.
  rewrite ?node_9142.
  rewrite !state_r895_nr_5F895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r895_nr_5F895 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9324 (s : N.State) (i : N.Inputs) :
  R.v9324 (state s) (inputs i) = Zmod.unsigned (N.v9324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9324 s i)) at 1.
  unfold R.v9324, N.v9324.
  rewrite ?node_9143.
  rewrite ?node_9146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9325 (s : N.State) (i : N.Inputs) :
  R.v9325 (state s) (inputs i) = Zmod.unsigned (N.v9325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9325 s i)) at 1.
  unfold R.v9325, N.v9325.
  rewrite ?node_9323.
  rewrite ?node_9324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9326 (s : N.State) (i : N.Inputs) :
  R.v9326 (state s) (inputs i) = Zmod.unsigned (N.v9326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9326 s i)) at 1.
  unfold R.v9326, N.v9326.
  rewrite ?node_9322.
  rewrite ?node_9325.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9327 (s : N.State) (i : N.Inputs) :
  R.v9327 (state s) (inputs i) = Zmod.unsigned (N.v9327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9327 s i)) at 1.
  unfold R.v9327, N.v9327.
  rewrite !state_r896_nr_5F896.
  rewrite !state_r897_nr_5F897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r896_nr_5F896 s)).
  rewrite ?(bits.mod_to_Z (N.r897_nr_5F897 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9328 (s : N.State) (i : N.Inputs) :
  R.v9328 (state s) (inputs i) = Zmod.unsigned (N.v9328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9328 s i)) at 1.
  unfold R.v9328, N.v9328.
  rewrite ?node_9326.
  rewrite ?node_9327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9329 (s : N.State) (i : N.Inputs) :
  R.v9329 (state s) (inputs i) = Zmod.unsigned (N.v9329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9329 s i)) at 1.
  unfold R.v9329, N.v9329.
  rewrite ?node_9315.
  rewrite ?node_9328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9330 (s : N.State) (i : N.Inputs) :
  R.v9330 (state s) (inputs i) = Zmod.unsigned (N.v9330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9330 s i)) at 1.
  unfold R.v9330, N.v9330.
  rewrite ?node_9125.
  rewrite ?node_9154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9331 (s : N.State) (i : N.Inputs) :
  R.v9331 (state s) (inputs i) = Zmod.unsigned (N.v9331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9331 s i)) at 1.
  unfold R.v9331, N.v9331.
  rewrite ?node_9155.
  rewrite ?node_9174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9332 (s : N.State) (i : N.Inputs) :
  R.v9332 (state s) (inputs i) = Zmod.unsigned (N.v9332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9332 s i)) at 1.
  unfold R.v9332, N.v9332.
  rewrite ?node_9330.
  rewrite ?node_9331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9333 (s : N.State) (i : N.Inputs) :
  R.v9333 (state s) (inputs i) = Zmod.unsigned (N.v9333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9333 s i)) at 1.
  unfold R.v9333, N.v9333.
  rewrite ?node_9329.
  rewrite ?node_9332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9334 (s : N.State) (i : N.Inputs) :
  R.v9334 (state s) (inputs i) = Zmod.unsigned (N.v9334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9334 s i)) at 1.
  unfold R.v9334, N.v9334.
  rewrite ?node_9113.
  rewrite ?node_9120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9335 (s : N.State) (i : N.Inputs) :
  R.v9335 (state s) (inputs i) = Zmod.unsigned (N.v9335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9335 s i)) at 1.
  unfold R.v9335, N.v9335.
  rewrite ?node_9121.
  rewrite ?node_9124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9336 (s : N.State) (i : N.Inputs) :
  R.v9336 (state s) (inputs i) = Zmod.unsigned (N.v9336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9336 s i)) at 1.
  unfold R.v9336, N.v9336.
  rewrite ?node_9334.
  rewrite ?node_9335.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9337 (s : N.State) (i : N.Inputs) :
  R.v9337 (state s) (inputs i) = Zmod.unsigned (N.v9337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9337 s i)) at 1.
  unfold R.v9337, N.v9337.
  rewrite ?node_9148.
  rewrite ?node_9149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9338 (s : N.State) (i : N.Inputs) :
  R.v9338 (state s) (inputs i) = Zmod.unsigned (N.v9338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9338 s i)) at 1.
  unfold R.v9338, N.v9338.
  rewrite ?node_9150.
  rewrite ?node_9153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9339 (s : N.State) (i : N.Inputs) :
  R.v9339 (state s) (inputs i) = Zmod.unsigned (N.v9339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9339 s i)) at 1.
  unfold R.v9339, N.v9339.
  rewrite ?node_9337.
  rewrite ?node_9338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9340 (s : N.State) (i : N.Inputs) :
  R.v9340 (state s) (inputs i) = Zmod.unsigned (N.v9340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9340 s i)) at 1.
  unfold R.v9340, N.v9340.
  rewrite ?node_9336.
  rewrite ?node_9339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9341 (s : N.State) (i : N.Inputs) :
  R.v9341 (state s) (inputs i) = Zmod.unsigned (N.v9341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9341 s i)) at 1.
  unfold R.v9341, N.v9341.
  rewrite ?node_9166.
  rewrite ?node_9169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9342 (s : N.State) (i : N.Inputs) :
  R.v9342 (state s) (inputs i) = Zmod.unsigned (N.v9342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9342 s i)) at 1.
  unfold R.v9342, N.v9342.
  rewrite ?node_9170.
  rewrite ?node_9173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9343 (s : N.State) (i : N.Inputs) :
  R.v9343 (state s) (inputs i) = Zmod.unsigned (N.v9343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9343 s i)) at 1.
  unfold R.v9343, N.v9343.
  rewrite ?node_9341.
  rewrite ?node_9342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9344 (s : N.State) (i : N.Inputs) :
  R.v9344 (state s) (inputs i) = Zmod.unsigned (N.v9344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9344 s i)) at 1.
  unfold R.v9344, N.v9344.
  rewrite ?node_9340.
  rewrite ?node_9343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9345 (s : N.State) (i : N.Inputs) :
  R.v9345 (state s) (inputs i) = Zmod.unsigned (N.v9345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9345 s i)) at 1.
  unfold R.v9345, N.v9345.
  rewrite ?node_9178.
  rewrite ?node_9181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9346 (s : N.State) (i : N.Inputs) :
  R.v9346 (state s) (inputs i) = Zmod.unsigned (N.v9346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9346 s i)) at 1.
  unfold R.v9346, N.v9346.
  rewrite ?node_9182.
  rewrite ?node_9185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9347 (s : N.State) (i : N.Inputs) :
  R.v9347 (state s) (inputs i) = Zmod.unsigned (N.v9347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9347 s i)) at 1.
  unfold R.v9347, N.v9347.
  rewrite ?node_9345.
  rewrite ?node_9346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9348 (s : N.State) (i : N.Inputs) :
  R.v9348 (state s) (inputs i) = Zmod.unsigned (N.v9348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9348 s i)) at 1.
  unfold R.v9348, N.v9348.
  rewrite ?node_9344.
  rewrite ?node_9347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9349 (s : N.State) (i : N.Inputs) :
  R.v9349 (state s) (inputs i) = Zmod.unsigned (N.v9349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9349 s i)) at 1.
  unfold R.v9349, N.v9349.
  rewrite ?node_9194.
  rewrite ?node_9197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9350 (s : N.State) (i : N.Inputs) :
  R.v9350 (state s) (inputs i) = Zmod.unsigned (N.v9350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9350 s i)) at 1.
  unfold R.v9350, N.v9350.
  rewrite ?node_9198.
  rewrite ?node_9201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9351 (s : N.State) (i : N.Inputs) :
  R.v9351 (state s) (inputs i) = Zmod.unsigned (N.v9351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9351 s i)) at 1.
  unfold R.v9351, N.v9351.
  rewrite ?node_9349.
  rewrite ?node_9350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9352 (s : N.State) (i : N.Inputs) :
  R.v9352 (state s) (inputs i) = Zmod.unsigned (N.v9352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9352 s i)) at 1.
  unfold R.v9352, N.v9352.
  rewrite ?node_9348.
  rewrite ?node_9351.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9353 (s : N.State) (i : N.Inputs) :
  R.v9353 (state s) (inputs i) = Zmod.unsigned (N.v9353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9353 s i)) at 1.
  unfold R.v9353, N.v9353.
  rewrite ?node_9333.
  rewrite ?node_9352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9354 (s : N.State) (i : N.Inputs) :
  R.v9354 (state s) (inputs i) = Zmod.unsigned (N.v9354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9354 s i)) at 1.
  unfold R.v9354, N.v9354.
  rewrite ?node_9175.
  rewrite ?node_9186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9355 (s : N.State) (i : N.Inputs) :
  R.v9355 (state s) (inputs i) = Zmod.unsigned (N.v9355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9355 s i)) at 1.
  unfold R.v9355, N.v9355.
  rewrite ?node_9187.
  rewrite ?node_9190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9356 (s : N.State) (i : N.Inputs) :
  R.v9356 (state s) (inputs i) = Zmod.unsigned (N.v9356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9356 s i)) at 1.
  unfold R.v9356, N.v9356.
  rewrite ?node_9354.
  rewrite ?node_9355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9357 (s : N.State) (i : N.Inputs) :
  R.v9357 (state s) (inputs i) = Zmod.unsigned (N.v9357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9357 s i)) at 1.
  unfold R.v9357, N.v9357.
  rewrite ?node_9353.
  rewrite ?node_9356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9358 (s : N.State) (i : N.Inputs) :
  R.v9358 (state s) (inputs i) = Zmod.unsigned (N.v9358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9358 s i)) at 1.
  unfold R.v9358, N.v9358.
  rewrite ?node_9202.
  rewrite ?node_9205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9359 (s : N.State) (i : N.Inputs) :
  R.v9359 (state s) (inputs i) = Zmod.unsigned (N.v9359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9359 s i)) at 1.
  unfold R.v9359, N.v9359.
  rewrite ?node_9206.
  rewrite ?node_9209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9360 (s : N.State) (i : N.Inputs) :
  R.v9360 (state s) (inputs i) = Zmod.unsigned (N.v9360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9360 s i)) at 1.
  unfold R.v9360, N.v9360.
  rewrite ?node_9358.
  rewrite ?node_9359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9361 (s : N.State) (i : N.Inputs) :
  R.v9361 (state s) (inputs i) = Zmod.unsigned (N.v9361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9361 s i)) at 1.
  unfold R.v9361, N.v9361.
  rewrite ?node_9357.
  rewrite ?node_9360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9362 (s : N.State) (i : N.Inputs) :
  R.v9362 (state s) (inputs i) = Zmod.unsigned (N.v9362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9362 s i)) at 1.
  unfold R.v9362, N.v9362.
  rewrite ?node_9191.
  rewrite ?node_9210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9363 (s : N.State) (i : N.Inputs) :
  R.v9363 (state s) (inputs i) = Zmod.unsigned (N.v9363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9363 s i)) at 1.
  unfold R.v9363, N.v9363.
  rewrite ?node_9211.
  rewrite ?node_9214.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9364 (s : N.State) (i : N.Inputs) :
  R.v9364 (state s) (inputs i) = Zmod.unsigned (N.v9364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9364 s i)) at 1.
  unfold R.v9364, N.v9364.
  rewrite ?node_9362.
  rewrite ?node_9363.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9365 (s : N.State) (i : N.Inputs) :
  R.v9365 (state s) (inputs i) = Zmod.unsigned (N.v9365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9365 s i)) at 1.
  unfold R.v9365, N.v9365.
  rewrite ?node_9361.
  rewrite ?node_9364.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9366 (s : N.State) (i : N.Inputs) :
  R.v9366 (state s) (inputs i) = Zmod.unsigned (N.v9366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9366 s i)) at 1.
  unfold R.v9366, N.v9366.
  rewrite ?node_9215.
  rewrite ?node_9218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9367 (s : N.State) (i : N.Inputs) :
  R.v9367 (state s) (inputs i) = Zmod.unsigned (N.v9367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9367 s i)) at 1.
  unfold R.v9367, N.v9367.
  rewrite ?node_9219.
  rewrite ?node_9222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9368 (s : N.State) (i : N.Inputs) :
  R.v9368 (state s) (inputs i) = Zmod.unsigned (N.v9368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9368 s i)) at 1.
  unfold R.v9368, N.v9368.
  rewrite ?node_9366.
  rewrite ?node_9367.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9369 (s : N.State) (i : N.Inputs) :
  R.v9369 (state s) (inputs i) = Zmod.unsigned (N.v9369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9369 s i)) at 1.
  unfold R.v9369, N.v9369.
  rewrite ?node_9365.
  rewrite ?node_9368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9370 (s : N.State) (i : N.Inputs) :
  R.v9370 (state s) (inputs i) = Zmod.unsigned (N.v9370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9370 s i)) at 1.
  unfold R.v9370, N.v9370.
  rewrite ?node_9369.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2387_nr_5F2418.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2387_nr_5F2418 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9371 (s : N.State) (i : N.Inputs) :
  R.v9371 (state s) (inputs i) = Zmod.unsigned (N.v9371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9371 s i)) at 1.
  unfold R.v9371, N.v9371.
  rewrite ?node_9223.
  rewrite ?node_9226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9372 (s : N.State) (i : N.Inputs) :
  R.v9372 (state s) (inputs i) = Zmod.unsigned (N.v9372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9372 s i)) at 1.
  unfold R.v9372, N.v9372.
  rewrite ?node_9371.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2388_nr_5F2419.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2388_nr_5F2419 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9373 (s : N.State) (i : N.Inputs) :
  R.v9373 (state s) (inputs i) = Zmod.unsigned (N.v9373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9373 s i)) at 1.
  unfold R.v9373, N.v9373.
  rewrite !state_r928_nr_5F928.
  rewrite !state_r929_nr_5F929.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r928_nr_5F928 s)).
  rewrite ?(bits.mod_to_Z (N.r929_nr_5F929 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9374 (s : N.State) (i : N.Inputs) :
  R.v9374 (state s) (inputs i) = Zmod.unsigned (N.v9374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9374 s i)) at 1.
  unfold R.v9374, N.v9374.
  rewrite ?node_9373.
  rewrite !state_r930_nr_5F930.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r930_nr_5F930 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9375 (s : N.State) (i : N.Inputs) :
  R.v9375 (state s) (inputs i) = Zmod.unsigned (N.v9375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9375 s i)) at 1.
  unfold R.v9375, N.v9375.
  rewrite ?node_9374.
  rewrite !state_r931_nr_5F931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r931_nr_5F931 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9376 (s : N.State) (i : N.Inputs) :
  R.v9376 (state s) (inputs i) = Zmod.unsigned (N.v9376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9376 s i)) at 1.
  unfold R.v9376, N.v9376.
  rewrite !state_r898_nr_5F898.
  rewrite !state_r899_nr_5F899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r898_nr_5F898 s)).
  rewrite ?(bits.mod_to_Z (N.r899_nr_5F899 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9377 (s : N.State) (i : N.Inputs) :
  R.v9377 (state s) (inputs i) = Zmod.unsigned (N.v9377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9377 s i)) at 1.
  unfold R.v9377, N.v9377.
  rewrite ?node_9231.
  rewrite !state_r900_nr_5F900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r900_nr_5F900 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9378 (s : N.State) (i : N.Inputs) :
  R.v9378 (state s) (inputs i) = Zmod.unsigned (N.v9378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9378 s i)) at 1.
  unfold R.v9378, N.v9378.
  rewrite ?node_9376.
  rewrite ?node_9377.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9379 (s : N.State) (i : N.Inputs) :
  R.v9379 (state s) (inputs i) = Zmod.unsigned (N.v9379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9379 s i)) at 1.
  unfold R.v9379, N.v9379.
  rewrite ?node_9375.
  rewrite ?node_9378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9380 (s : N.State) (i : N.Inputs) :
  R.v9380 (state s) (inputs i) = Zmod.unsigned (N.v9380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9380 s i)) at 1.
  unfold R.v9380, N.v9380.
  rewrite !state_r932_nr_5F932.
  rewrite !state_r933_nr_5F933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r932_nr_5F932 s)).
  rewrite ?(bits.mod_to_Z (N.r933_nr_5F933 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9381 (s : N.State) (i : N.Inputs) :
  R.v9381 (state s) (inputs i) = Zmod.unsigned (N.v9381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9381 s i)) at 1.
  unfold R.v9381, N.v9381.
  rewrite ?node_9380.
  rewrite !state_r934_nr_5F934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r934_nr_5F934 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9382 (s : N.State) (i : N.Inputs) :
  R.v9382 (state s) (inputs i) = Zmod.unsigned (N.v9382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9382 s i)) at 1.
  unfold R.v9382, N.v9382.
  rewrite ?node_9381.
  rewrite !state_r935_nr_5F935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r935_nr_5F935 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9383 (s : N.State) (i : N.Inputs) :
  R.v9383 (state s) (inputs i) = Zmod.unsigned (N.v9383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9383 s i)) at 1.
  unfold R.v9383, N.v9383.
  rewrite !state_r902_nr_5F902.
  rewrite !state_r903_nr_5F903.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r902_nr_5F902 s)).
  rewrite ?(bits.mod_to_Z (N.r903_nr_5F903 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9384 (s : N.State) (i : N.Inputs) :
  R.v9384 (state s) (inputs i) = Zmod.unsigned (N.v9384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9384 s i)) at 1.
  unfold R.v9384, N.v9384.
  rewrite ?node_9238.
  rewrite !state_r904_nr_5F904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r904_nr_5F904 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9385 (s : N.State) (i : N.Inputs) :
  R.v9385 (state s) (inputs i) = Zmod.unsigned (N.v9385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9385 s i)) at 1.
  unfold R.v9385, N.v9385.
  rewrite ?node_9383.
  rewrite ?node_9384.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9386 (s : N.State) (i : N.Inputs) :
  R.v9386 (state s) (inputs i) = Zmod.unsigned (N.v9386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9386 s i)) at 1.
  unfold R.v9386, N.v9386.
  rewrite ?node_9382.
  rewrite ?node_9385.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9387 (s : N.State) (i : N.Inputs) :
  R.v9387 (state s) (inputs i) = Zmod.unsigned (N.v9387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9387 s i)) at 1.
  unfold R.v9387, N.v9387.
  rewrite ?node_9379.
  rewrite ?node_9386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9388 (s : N.State) (i : N.Inputs) :
  R.v9388 (state s) (inputs i) = Zmod.unsigned (N.v9388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9388 s i)) at 1.
  unfold R.v9388, N.v9388.
  rewrite !state_r936_nr_5F936.
  rewrite !state_r937_nr_5F937.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r936_nr_5F936 s)).
  rewrite ?(bits.mod_to_Z (N.r937_nr_5F937 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9389 (s : N.State) (i : N.Inputs) :
  R.v9389 (state s) (inputs i) = Zmod.unsigned (N.v9389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9389 s i)) at 1.
  unfold R.v9389, N.v9389.
  rewrite ?node_9388.
  rewrite !state_r938_nr_5F938.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r938_nr_5F938 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9390 (s : N.State) (i : N.Inputs) :
  R.v9390 (state s) (inputs i) = Zmod.unsigned (N.v9390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9390 s i)) at 1.
  unfold R.v9390, N.v9390.
  rewrite ?node_9389.
  rewrite !state_r939_nr_5F939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r939_nr_5F939 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9391 (s : N.State) (i : N.Inputs) :
  R.v9391 (state s) (inputs i) = Zmod.unsigned (N.v9391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9391 s i)) at 1.
  unfold R.v9391, N.v9391.
  rewrite !state_r906_nr_5F906.
  rewrite !state_r907_nr_5F907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r906_nr_5F906 s)).
  rewrite ?(bits.mod_to_Z (N.r907_nr_5F907 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9392 (s : N.State) (i : N.Inputs) :
  R.v9392 (state s) (inputs i) = Zmod.unsigned (N.v9392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9392 s i)) at 1.
  unfold R.v9392, N.v9392.
  rewrite ?node_9246.
  rewrite !state_r908_nr_5F908.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r908_nr_5F908 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9393 (s : N.State) (i : N.Inputs) :
  R.v9393 (state s) (inputs i) = Zmod.unsigned (N.v9393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9393 s i)) at 1.
  unfold R.v9393, N.v9393.
  rewrite ?node_9391.
  rewrite ?node_9392.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9394 (s : N.State) (i : N.Inputs) :
  R.v9394 (state s) (inputs i) = Zmod.unsigned (N.v9394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9394 s i)) at 1.
  unfold R.v9394, N.v9394.
  rewrite ?node_9390.
  rewrite ?node_9393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9395 (s : N.State) (i : N.Inputs) :
  R.v9395 (state s) (inputs i) = Zmod.unsigned (N.v9395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9395 s i)) at 1.
  unfold R.v9395, N.v9395.
  rewrite ?node_9387.
  rewrite ?node_9394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9396 (s : N.State) (i : N.Inputs) :
  R.v9396 (state s) (inputs i) = Zmod.unsigned (N.v9396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9396 s i)) at 1.
  unfold R.v9396, N.v9396.
  rewrite !state_r940_nr_5F940.
  rewrite !state_r941_nr_5F941.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r940_nr_5F940 s)).
  rewrite ?(bits.mod_to_Z (N.r941_nr_5F941 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9397 (s : N.State) (i : N.Inputs) :
  R.v9397 (state s) (inputs i) = Zmod.unsigned (N.v9397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9397 s i)) at 1.
  unfold R.v9397, N.v9397.
  rewrite ?node_9396.
  rewrite !state_r942_nr_5F942.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r942_nr_5F942 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9398 (s : N.State) (i : N.Inputs) :
  R.v9398 (state s) (inputs i) = Zmod.unsigned (N.v9398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9398 s i)) at 1.
  unfold R.v9398, N.v9398.
  rewrite ?node_9397.
  rewrite !state_r943_nr_5F943.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r943_nr_5F943 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9399 (s : N.State) (i : N.Inputs) :
  R.v9399 (state s) (inputs i) = Zmod.unsigned (N.v9399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9399 s i)) at 1.
  unfold R.v9399, N.v9399.
  rewrite !state_r910_nr_5F910.
  rewrite !state_r911_nr_5F911.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r910_nr_5F910 s)).
  rewrite ?(bits.mod_to_Z (N.r911_nr_5F911 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9400 (s : N.State) (i : N.Inputs) :
  R.v9400 (state s) (inputs i) = Zmod.unsigned (N.v9400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9400 s i)) at 1.
  unfold R.v9400, N.v9400.
  rewrite ?node_9254.
  rewrite !state_r912_nr_5F912.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r912_nr_5F912 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9401 (s : N.State) (i : N.Inputs) :
  R.v9401 (state s) (inputs i) = Zmod.unsigned (N.v9401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9401 s i)) at 1.
  unfold R.v9401, N.v9401.
  rewrite ?node_9399.
  rewrite ?node_9400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9402 (s : N.State) (i : N.Inputs) :
  R.v9402 (state s) (inputs i) = Zmod.unsigned (N.v9402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9402 s i)) at 1.
  unfold R.v9402, N.v9402.
  rewrite ?node_9398.
  rewrite ?node_9401.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9403 (s : N.State) (i : N.Inputs) :
  R.v9403 (state s) (inputs i) = Zmod.unsigned (N.v9403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9403 s i)) at 1.
  unfold R.v9403, N.v9403.
  rewrite ?node_9395.
  rewrite ?node_9402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9404 (s : N.State) (i : N.Inputs) :
  R.v9404 (state s) (inputs i) = Zmod.unsigned (N.v9404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9404 s i)) at 1.
  unfold R.v9404, N.v9404.
  rewrite ?node_9237.
  rewrite ?node_9244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9405 (s : N.State) (i : N.Inputs) :
  R.v9405 (state s) (inputs i) = Zmod.unsigned (N.v9405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9405 s i)) at 1.
  unfold R.v9405, N.v9405.
  rewrite ?node_9245.
  rewrite ?node_9252.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9406 (s : N.State) (i : N.Inputs) :
  R.v9406 (state s) (inputs i) = Zmod.unsigned (N.v9406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9406 s i)) at 1.
  unfold R.v9406, N.v9406.
  rewrite ?node_9404.
  rewrite ?node_9405.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9407 (s : N.State) (i : N.Inputs) :
  R.v9407 (state s) (inputs i) = Zmod.unsigned (N.v9407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9407 s i)) at 1.
  unfold R.v9407, N.v9407.
  rewrite ?node_9403.
  rewrite ?node_9406.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9408 (s : N.State) (i : N.Inputs) :
  R.v9408 (state s) (inputs i) = Zmod.unsigned (N.v9408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9408 s i)) at 1.
  unfold R.v9408, N.v9408.
  rewrite !state_r944_nr_5F944.
  rewrite !state_r945_nr_5F945.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r944_nr_5F944 s)).
  rewrite ?(bits.mod_to_Z (N.r945_nr_5F945 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9409 (s : N.State) (i : N.Inputs) :
  R.v9409 (state s) (inputs i) = Zmod.unsigned (N.v9409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9409 s i)) at 1.
  unfold R.v9409, N.v9409.
  rewrite ?node_9408.
  rewrite !state_r946_nr_5F946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r946_nr_5F946 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9410 (s : N.State) (i : N.Inputs) :
  R.v9410 (state s) (inputs i) = Zmod.unsigned (N.v9410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9410 s i)) at 1.
  unfold R.v9410, N.v9410.
  rewrite ?node_9409.
  rewrite !state_r947_nr_5F947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r947_nr_5F947 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9411 (s : N.State) (i : N.Inputs) :
  R.v9411 (state s) (inputs i) = Zmod.unsigned (N.v9411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9411 s i)) at 1.
  unfold R.v9411, N.v9411.
  rewrite !state_r914_nr_5F914.
  rewrite !state_r915_nr_5F915.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r914_nr_5F914 s)).
  rewrite ?(bits.mod_to_Z (N.r915_nr_5F915 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9412 (s : N.State) (i : N.Inputs) :
  R.v9412 (state s) (inputs i) = Zmod.unsigned (N.v9412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9412 s i)) at 1.
  unfold R.v9412, N.v9412.
  rewrite ?node_9266.
  rewrite !state_r916_nr_5F916.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r916_nr_5F916 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9413 (s : N.State) (i : N.Inputs) :
  R.v9413 (state s) (inputs i) = Zmod.unsigned (N.v9413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9413 s i)) at 1.
  unfold R.v9413, N.v9413.
  rewrite ?node_9411.
  rewrite ?node_9412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9414 (s : N.State) (i : N.Inputs) :
  R.v9414 (state s) (inputs i) = Zmod.unsigned (N.v9414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9414 s i)) at 1.
  unfold R.v9414, N.v9414.
  rewrite ?node_9410.
  rewrite ?node_9413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9415 (s : N.State) (i : N.Inputs) :
  R.v9415 (state s) (inputs i) = Zmod.unsigned (N.v9415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9415 s i)) at 1.
  unfold R.v9415, N.v9415.
  rewrite !state_r948_nr_5F948.
  rewrite !state_r949_nr_5F949.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r948_nr_5F948 s)).
  rewrite ?(bits.mod_to_Z (N.r949_nr_5F949 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9416 (s : N.State) (i : N.Inputs) :
  R.v9416 (state s) (inputs i) = Zmod.unsigned (N.v9416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9416 s i)) at 1.
  unfold R.v9416, N.v9416.
  rewrite ?node_9415.
  rewrite !state_r950_nr_5F950.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r950_nr_5F950 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9417 (s : N.State) (i : N.Inputs) :
  R.v9417 (state s) (inputs i) = Zmod.unsigned (N.v9417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9417 s i)) at 1.
  unfold R.v9417, N.v9417.
  rewrite ?node_9416.
  rewrite !state_r951_nr_5F951.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r951_nr_5F951 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9418 (s : N.State) (i : N.Inputs) :
  R.v9418 (state s) (inputs i) = Zmod.unsigned (N.v9418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9418 s i)) at 1.
  unfold R.v9418, N.v9418.
  rewrite !state_r918_nr_5F918.
  rewrite !state_r919_nr_5F919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r918_nr_5F918 s)).
  rewrite ?(bits.mod_to_Z (N.r919_nr_5F919 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9419 (s : N.State) (i : N.Inputs) :
  R.v9419 (state s) (inputs i) = Zmod.unsigned (N.v9419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9419 s i)) at 1.
  unfold R.v9419, N.v9419.
  rewrite ?node_9273.
  rewrite !state_r920_nr_5F920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r920_nr_5F920 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9420 (s : N.State) (i : N.Inputs) :
  R.v9420 (state s) (inputs i) = Zmod.unsigned (N.v9420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9420 s i)) at 1.
  unfold R.v9420, N.v9420.
  rewrite ?node_9418.
  rewrite ?node_9419.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9421 (s : N.State) (i : N.Inputs) :
  R.v9421 (state s) (inputs i) = Zmod.unsigned (N.v9421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9421 s i)) at 1.
  unfold R.v9421, N.v9421.
  rewrite ?node_9417.
  rewrite ?node_9420.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9422 (s : N.State) (i : N.Inputs) :
  R.v9422 (state s) (inputs i) = Zmod.unsigned (N.v9422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9422 s i)) at 1.
  unfold R.v9422, N.v9422.
  rewrite ?node_9414.
  rewrite ?node_9421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9423 (s : N.State) (i : N.Inputs) :
  R.v9423 (state s) (inputs i) = Zmod.unsigned (N.v9423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9423 s i)) at 1.
  unfold R.v9423, N.v9423.
  rewrite !state_r952_nr_5F952.
  rewrite !state_r953_nr_5F953.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r952_nr_5F952 s)).
  rewrite ?(bits.mod_to_Z (N.r953_nr_5F953 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9424 (s : N.State) (i : N.Inputs) :
  R.v9424 (state s) (inputs i) = Zmod.unsigned (N.v9424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9424 s i)) at 1.
  unfold R.v9424, N.v9424.
  rewrite ?node_9423.
  rewrite !state_r954_nr_5F954.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r954_nr_5F954 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9425 (s : N.State) (i : N.Inputs) :
  R.v9425 (state s) (inputs i) = Zmod.unsigned (N.v9425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9425 s i)) at 1.
  unfold R.v9425, N.v9425.
  rewrite ?node_9424.
  rewrite !state_r955_nr_5F955.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r955_nr_5F955 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9426 (s : N.State) (i : N.Inputs) :
  R.v9426 (state s) (inputs i) = Zmod.unsigned (N.v9426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9426 s i)) at 1.
  unfold R.v9426, N.v9426.
  rewrite !state_r922_nr_5F922.
  rewrite !state_r923_nr_5F923.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r922_nr_5F922 s)).
  rewrite ?(bits.mod_to_Z (N.r923_nr_5F923 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9427 (s : N.State) (i : N.Inputs) :
  R.v9427 (state s) (inputs i) = Zmod.unsigned (N.v9427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9427 s i)) at 1.
  unfold R.v9427, N.v9427.
  rewrite ?node_9281.
  rewrite !state_r924_nr_5F924.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r924_nr_5F924 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9428 (s : N.State) (i : N.Inputs) :
  R.v9428 (state s) (inputs i) = Zmod.unsigned (N.v9428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9428 s i)) at 1.
  unfold R.v9428, N.v9428.
  rewrite ?node_9426.
  rewrite ?node_9427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9429 (s : N.State) (i : N.Inputs) :
  R.v9429 (state s) (inputs i) = Zmod.unsigned (N.v9429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9429 s i)) at 1.
  unfold R.v9429, N.v9429.
  rewrite ?node_9425.
  rewrite ?node_9428.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9430 (s : N.State) (i : N.Inputs) :
  R.v9430 (state s) (inputs i) = Zmod.unsigned (N.v9430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9430 s i)) at 1.
  unfold R.v9430, N.v9430.
  rewrite ?node_9422.
  rewrite ?node_9429.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9431 (s : N.State) (i : N.Inputs) :
  R.v9431 (state s) (inputs i) = Zmod.unsigned (N.v9431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9431 s i)) at 1.
  unfold R.v9431, N.v9431.
  rewrite !state_r956_nr_5F956.
  rewrite !state_r957_nr_5F957.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r956_nr_5F956 s)).
  rewrite ?(bits.mod_to_Z (N.r957_nr_5F957 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9432 (s : N.State) (i : N.Inputs) :
  R.v9432 (state s) (inputs i) = Zmod.unsigned (N.v9432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9432 s i)) at 1.
  unfold R.v9432, N.v9432.
  rewrite ?node_9431.
  rewrite !state_r958_nr_5F958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r958_nr_5F958 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9433 (s : N.State) (i : N.Inputs) :
  R.v9433 (state s) (inputs i) = Zmod.unsigned (N.v9433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9433 s i)) at 1.
  unfold R.v9433, N.v9433.
  rewrite ?node_9430.
  rewrite ?node_9432.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9434 (s : N.State) (i : N.Inputs) :
  R.v9434 (state s) (inputs i) = Zmod.unsigned (N.v9434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9434 s i)) at 1.
  unfold R.v9434, N.v9434.
  rewrite ?node_9272.
  rewrite ?node_9279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9435 (s : N.State) (i : N.Inputs) :
  R.v9435 (state s) (inputs i) = Zmod.unsigned (N.v9435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9435 s i)) at 1.
  unfold R.v9435, N.v9435.
  rewrite ?node_9280.
  rewrite ?node_9287.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9436 (s : N.State) (i : N.Inputs) :
  R.v9436 (state s) (inputs i) = Zmod.unsigned (N.v9436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9436 s i)) at 1.
  unfold R.v9436, N.v9436.
  rewrite ?node_9434.
  rewrite ?node_9435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9437 (s : N.State) (i : N.Inputs) :
  R.v9437 (state s) (inputs i) = Zmod.unsigned (N.v9437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9437 s i)) at 1.
  unfold R.v9437, N.v9437.
  rewrite ?node_9433.
  rewrite ?node_9436.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9438 (s : N.State) (i : N.Inputs) :
  R.v9438 (state s) (inputs i) = Zmod.unsigned (N.v9438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9438 s i)) at 1.
  unfold R.v9438, N.v9438.
  rewrite ?node_9407.
  rewrite ?node_9437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9439 (s : N.State) (i : N.Inputs) :
  R.v9439 (state s) (inputs i) = Zmod.unsigned (N.v9439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9439 s i)) at 1.
  unfold R.v9439, N.v9439.
  rewrite ?node_9232.
  rewrite !state_r901_nr_5F901.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r901_nr_5F901 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9440 (s : N.State) (i : N.Inputs) :
  R.v9440 (state s) (inputs i) = Zmod.unsigned (N.v9440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9440 s i)) at 1.
  unfold R.v9440, N.v9440.
  rewrite ?node_9233.
  rewrite ?node_9236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9441 (s : N.State) (i : N.Inputs) :
  R.v9441 (state s) (inputs i) = Zmod.unsigned (N.v9441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9441 s i)) at 1.
  unfold R.v9441, N.v9441.
  rewrite ?node_9439.
  rewrite ?node_9440.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9442 (s : N.State) (i : N.Inputs) :
  R.v9442 (state s) (inputs i) = Zmod.unsigned (N.v9442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9442 s i)) at 1.
  unfold R.v9442, N.v9442.
  rewrite ?node_9239.
  rewrite !state_r905_nr_5F905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r905_nr_5F905 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9443 (s : N.State) (i : N.Inputs) :
  R.v9443 (state s) (inputs i) = Zmod.unsigned (N.v9443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9443 s i)) at 1.
  unfold R.v9443, N.v9443.
  rewrite ?node_9240.
  rewrite ?node_9243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9444 (s : N.State) (i : N.Inputs) :
  R.v9444 (state s) (inputs i) = Zmod.unsigned (N.v9444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9444 s i)) at 1.
  unfold R.v9444, N.v9444.
  rewrite ?node_9442.
  rewrite ?node_9443.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9445 (s : N.State) (i : N.Inputs) :
  R.v9445 (state s) (inputs i) = Zmod.unsigned (N.v9445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9445 s i)) at 1.
  unfold R.v9445, N.v9445.
  rewrite ?node_9441.
  rewrite ?node_9444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9446 (s : N.State) (i : N.Inputs) :
  R.v9446 (state s) (inputs i) = Zmod.unsigned (N.v9446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9446 s i)) at 1.
  unfold R.v9446, N.v9446.
  rewrite ?node_9247.
  rewrite !state_r909_nr_5F909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r909_nr_5F909 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9447 (s : N.State) (i : N.Inputs) :
  R.v9447 (state s) (inputs i) = Zmod.unsigned (N.v9447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9447 s i)) at 1.
  unfold R.v9447, N.v9447.
  rewrite ?node_9248.
  rewrite ?node_9251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9448 (s : N.State) (i : N.Inputs) :
  R.v9448 (state s) (inputs i) = Zmod.unsigned (N.v9448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9448 s i)) at 1.
  unfold R.v9448, N.v9448.
  rewrite ?node_9446.
  rewrite ?node_9447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9449 (s : N.State) (i : N.Inputs) :
  R.v9449 (state s) (inputs i) = Zmod.unsigned (N.v9449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9449 s i)) at 1.
  unfold R.v9449, N.v9449.
  rewrite ?node_9445.
  rewrite ?node_9448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9450 (s : N.State) (i : N.Inputs) :
  R.v9450 (state s) (inputs i) = Zmod.unsigned (N.v9450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9450 s i)) at 1.
  unfold R.v9450, N.v9450.
  rewrite ?node_9255.
  rewrite !state_r913_nr_5F913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r913_nr_5F913 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9451 (s : N.State) (i : N.Inputs) :
  R.v9451 (state s) (inputs i) = Zmod.unsigned (N.v9451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9451 s i)) at 1.
  unfold R.v9451, N.v9451.
  rewrite ?node_9256.
  rewrite ?node_9259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9452 (s : N.State) (i : N.Inputs) :
  R.v9452 (state s) (inputs i) = Zmod.unsigned (N.v9452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9452 s i)) at 1.
  unfold R.v9452, N.v9452.
  rewrite ?node_9450.
  rewrite ?node_9451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9453 (s : N.State) (i : N.Inputs) :
  R.v9453 (state s) (inputs i) = Zmod.unsigned (N.v9453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9453 s i)) at 1.
  unfold R.v9453, N.v9453.
  rewrite ?node_9449.
  rewrite ?node_9452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9454 (s : N.State) (i : N.Inputs) :
  R.v9454 (state s) (inputs i) = Zmod.unsigned (N.v9454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9454 s i)) at 1.
  unfold R.v9454, N.v9454.
  rewrite ?node_9298.
  rewrite ?node_9301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9455 (s : N.State) (i : N.Inputs) :
  R.v9455 (state s) (inputs i) = Zmod.unsigned (N.v9455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9455 s i)) at 1.
  unfold R.v9455, N.v9455.
  rewrite ?node_9302.
  rewrite ?node_9305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9456 (s : N.State) (i : N.Inputs) :
  R.v9456 (state s) (inputs i) = Zmod.unsigned (N.v9456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9456 s i)) at 1.
  unfold R.v9456, N.v9456.
  rewrite ?node_9454.
  rewrite ?node_9455.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9457 (s : N.State) (i : N.Inputs) :
  R.v9457 (state s) (inputs i) = Zmod.unsigned (N.v9457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9457 s i)) at 1.
  unfold R.v9457, N.v9457.
  rewrite ?node_9453.
  rewrite ?node_9456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9458 (s : N.State) (i : N.Inputs) :
  R.v9458 (state s) (inputs i) = Zmod.unsigned (N.v9458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9458 s i)) at 1.
  unfold R.v9458, N.v9458.
  rewrite ?node_9438.
  rewrite ?node_9457.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9459 (s : N.State) (i : N.Inputs) :
  R.v9459 (state s) (inputs i) = Zmod.unsigned (N.v9459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9459 s i)) at 1.
  unfold R.v9459, N.v9459.
  rewrite ?node_9267.
  rewrite !state_r917_nr_5F917.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r917_nr_5F917 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9460 (s : N.State) (i : N.Inputs) :
  R.v9460 (state s) (inputs i) = Zmod.unsigned (N.v9460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9460 s i)) at 1.
  unfold R.v9460, N.v9460.
  rewrite ?node_9268.
  rewrite ?node_9271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9461 (s : N.State) (i : N.Inputs) :
  R.v9461 (state s) (inputs i) = Zmod.unsigned (N.v9461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9461 s i)) at 1.
  unfold R.v9461, N.v9461.
  rewrite ?node_9459.
  rewrite ?node_9460.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9462 (s : N.State) (i : N.Inputs) :
  R.v9462 (state s) (inputs i) = Zmod.unsigned (N.v9462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9462 s i)) at 1.
  unfold R.v9462, N.v9462.
  rewrite ?node_9274.
  rewrite !state_r921_nr_5F921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r921_nr_5F921 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9463 (s : N.State) (i : N.Inputs) :
  R.v9463 (state s) (inputs i) = Zmod.unsigned (N.v9463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9463 s i)) at 1.
  unfold R.v9463, N.v9463.
  rewrite ?node_9275.
  rewrite ?node_9278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9464 (s : N.State) (i : N.Inputs) :
  R.v9464 (state s) (inputs i) = Zmod.unsigned (N.v9464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9464 s i)) at 1.
  unfold R.v9464, N.v9464.
  rewrite ?node_9462.
  rewrite ?node_9463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9465 (s : N.State) (i : N.Inputs) :
  R.v9465 (state s) (inputs i) = Zmod.unsigned (N.v9465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9465 s i)) at 1.
  unfold R.v9465, N.v9465.
  rewrite ?node_9461.
  rewrite ?node_9464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9466 (s : N.State) (i : N.Inputs) :
  R.v9466 (state s) (inputs i) = Zmod.unsigned (N.v9466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9466 s i)) at 1.
  unfold R.v9466, N.v9466.
  rewrite ?node_9282.
  rewrite !state_r925_nr_5F925.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r925_nr_5F925 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9467 (s : N.State) (i : N.Inputs) :
  R.v9467 (state s) (inputs i) = Zmod.unsigned (N.v9467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9467 s i)) at 1.
  unfold R.v9467, N.v9467.
  rewrite ?node_9283.
  rewrite ?node_9286.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9468 (s : N.State) (i : N.Inputs) :
  R.v9468 (state s) (inputs i) = Zmod.unsigned (N.v9468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9468 s i)) at 1.
  unfold R.v9468, N.v9468.
  rewrite ?node_9466.
  rewrite ?node_9467.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9469 (s : N.State) (i : N.Inputs) :
  R.v9469 (state s) (inputs i) = Zmod.unsigned (N.v9469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9469 s i)) at 1.
  unfold R.v9469, N.v9469.
  rewrite ?node_9465.
  rewrite ?node_9468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9470 (s : N.State) (i : N.Inputs) :
  R.v9470 (state s) (inputs i) = Zmod.unsigned (N.v9470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9470 s i)) at 1.
  unfold R.v9470, N.v9470.
  rewrite !state_r926_nr_5F926.
  rewrite !state_r927_nr_5F927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r926_nr_5F926 s)).
  rewrite ?(bits.mod_to_Z (N.r927_nr_5F927 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9471 (s : N.State) (i : N.Inputs) :
  R.v9471 (state s) (inputs i) = Zmod.unsigned (N.v9471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9471 s i)) at 1.
  unfold R.v9471, N.v9471.
  rewrite ?node_9469.
  rewrite ?node_9470.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9472 (s : N.State) (i : N.Inputs) :
  R.v9472 (state s) (inputs i) = Zmod.unsigned (N.v9472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9472 s i)) at 1.
  unfold R.v9472, N.v9472.
  rewrite ?node_9318.
  rewrite ?node_9321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9473 (s : N.State) (i : N.Inputs) :
  R.v9473 (state s) (inputs i) = Zmod.unsigned (N.v9473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9473 s i)) at 1.
  unfold R.v9473, N.v9473.
  rewrite ?node_9322.
  rewrite ?node_9325.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9474 (s : N.State) (i : N.Inputs) :
  R.v9474 (state s) (inputs i) = Zmod.unsigned (N.v9474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9474 s i)) at 1.
  unfold R.v9474, N.v9474.
  rewrite ?node_9472.
  rewrite ?node_9473.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9475 (s : N.State) (i : N.Inputs) :
  R.v9475 (state s) (inputs i) = Zmod.unsigned (N.v9475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9475 s i)) at 1.
  unfold R.v9475, N.v9475.
  rewrite ?node_9471.
  rewrite ?node_9474.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9476 (s : N.State) (i : N.Inputs) :
  R.v9476 (state s) (inputs i) = Zmod.unsigned (N.v9476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9476 s i)) at 1.
  unfold R.v9476, N.v9476.
  rewrite ?node_9458.
  rewrite ?node_9475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9477 (s : N.State) (i : N.Inputs) :
  R.v9477 (state s) (inputs i) = Zmod.unsigned (N.v9477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9477 s i)) at 1.
  unfold R.v9477, N.v9477.
  rewrite ?node_9265.
  rewrite ?node_9294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9478 (s : N.State) (i : N.Inputs) :
  R.v9478 (state s) (inputs i) = Zmod.unsigned (N.v9478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9478 s i)) at 1.
  unfold R.v9478, N.v9478.
  rewrite ?node_9295.
  rewrite ?node_9314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9479 (s : N.State) (i : N.Inputs) :
  R.v9479 (state s) (inputs i) = Zmod.unsigned (N.v9479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9479 s i)) at 1.
  unfold R.v9479, N.v9479.
  rewrite ?node_9477.
  rewrite ?node_9478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9480 (s : N.State) (i : N.Inputs) :
  R.v9480 (state s) (inputs i) = Zmod.unsigned (N.v9480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9480 s i)) at 1.
  unfold R.v9480, N.v9480.
  rewrite ?node_9476.
  rewrite ?node_9479.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9481 (s : N.State) (i : N.Inputs) :
  R.v9481 (state s) (inputs i) = Zmod.unsigned (N.v9481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9481 s i)) at 1.
  unfold R.v9481, N.v9481.
  rewrite ?node_9253.
  rewrite ?node_9260.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9482 (s : N.State) (i : N.Inputs) :
  R.v9482 (state s) (inputs i) = Zmod.unsigned (N.v9482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9482 s i)) at 1.
  unfold R.v9482, N.v9482.
  rewrite ?node_9261.
  rewrite ?node_9264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9483 (s : N.State) (i : N.Inputs) :
  R.v9483 (state s) (inputs i) = Zmod.unsigned (N.v9483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9483 s i)) at 1.
  unfold R.v9483, N.v9483.
  rewrite ?node_9481.
  rewrite ?node_9482.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9484 (s : N.State) (i : N.Inputs) :
  R.v9484 (state s) (inputs i) = Zmod.unsigned (N.v9484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9484 s i)) at 1.
  unfold R.v9484, N.v9484.
  rewrite ?node_9288.
  rewrite ?node_9289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9485 (s : N.State) (i : N.Inputs) :
  R.v9485 (state s) (inputs i) = Zmod.unsigned (N.v9485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9485 s i)) at 1.
  unfold R.v9485, N.v9485.
  rewrite ?node_9290.
  rewrite ?node_9293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9486 (s : N.State) (i : N.Inputs) :
  R.v9486 (state s) (inputs i) = Zmod.unsigned (N.v9486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9486 s i)) at 1.
  unfold R.v9486, N.v9486.
  rewrite ?node_9484.
  rewrite ?node_9485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9487 (s : N.State) (i : N.Inputs) :
  R.v9487 (state s) (inputs i) = Zmod.unsigned (N.v9487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9487 s i)) at 1.
  unfold R.v9487, N.v9487.
  rewrite ?node_9483.
  rewrite ?node_9486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9488 (s : N.State) (i : N.Inputs) :
  R.v9488 (state s) (inputs i) = Zmod.unsigned (N.v9488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9488 s i)) at 1.
  unfold R.v9488, N.v9488.
  rewrite ?node_9306.
  rewrite ?node_9309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9489 (s : N.State) (i : N.Inputs) :
  R.v9489 (state s) (inputs i) = Zmod.unsigned (N.v9489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9489 s i)) at 1.
  unfold R.v9489, N.v9489.
  rewrite ?node_9310.
  rewrite ?node_9313.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9490 (s : N.State) (i : N.Inputs) :
  R.v9490 (state s) (inputs i) = Zmod.unsigned (N.v9490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9490 s i)) at 1.
  unfold R.v9490, N.v9490.
  rewrite ?node_9488.
  rewrite ?node_9489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9491 (s : N.State) (i : N.Inputs) :
  R.v9491 (state s) (inputs i) = Zmod.unsigned (N.v9491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9491 s i)) at 1.
  unfold R.v9491, N.v9491.
  rewrite ?node_9487.
  rewrite ?node_9490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9492 (s : N.State) (i : N.Inputs) :
  R.v9492 (state s) (inputs i) = Zmod.unsigned (N.v9492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9492 s i)) at 1.
  unfold R.v9492, N.v9492.
  rewrite ?node_9326.
  rewrite ?node_9327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9493 (s : N.State) (i : N.Inputs) :
  R.v9493 (state s) (inputs i) = Zmod.unsigned (N.v9493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9493 s i)) at 1.
  unfold R.v9493, N.v9493.
  rewrite ?node_9491.
  rewrite ?node_9492.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9494 (s : N.State) (i : N.Inputs) :
  R.v9494 (state s) (inputs i) = Zmod.unsigned (N.v9494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9494 s i)) at 1.
  unfold R.v9494, N.v9494.
  rewrite ?node_9336.
  rewrite ?node_9339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9495 (s : N.State) (i : N.Inputs) :
  R.v9495 (state s) (inputs i) = Zmod.unsigned (N.v9495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9495 s i)) at 1.
  unfold R.v9495, N.v9495.
  rewrite ?node_9340.
  rewrite ?node_9343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9496 (s : N.State) (i : N.Inputs) :
  R.v9496 (state s) (inputs i) = Zmod.unsigned (N.v9496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9496 s i)) at 1.
  unfold R.v9496, N.v9496.
  rewrite ?node_9494.
  rewrite ?node_9495.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9497 (s : N.State) (i : N.Inputs) :
  R.v9497 (state s) (inputs i) = Zmod.unsigned (N.v9497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9497 s i)) at 1.
  unfold R.v9497, N.v9497.
  rewrite ?node_9493.
  rewrite ?node_9496.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9498 (s : N.State) (i : N.Inputs) :
  R.v9498 (state s) (inputs i) = Zmod.unsigned (N.v9498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9498 s i)) at 1.
  unfold R.v9498, N.v9498.
  rewrite ?node_9480.
  rewrite ?node_9497.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9499 (s : N.State) (i : N.Inputs) :
  R.v9499 (state s) (inputs i) = Zmod.unsigned (N.v9499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9499 s i)) at 1.
  unfold R.v9499, N.v9499.
  rewrite ?node_9315.
  rewrite ?node_9328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9500 (s : N.State) (i : N.Inputs) :
  R.v9500 (state s) (inputs i) = Zmod.unsigned (N.v9500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9500 s i)) at 1.
  unfold R.v9500, N.v9500.
  rewrite ?node_9329.
  rewrite ?node_9332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9501 (s : N.State) (i : N.Inputs) :
  R.v9501 (state s) (inputs i) = Zmod.unsigned (N.v9501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9501 s i)) at 1.
  unfold R.v9501, N.v9501.
  rewrite ?node_9499.
  rewrite ?node_9500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9502 (s : N.State) (i : N.Inputs) :
  R.v9502 (state s) (inputs i) = Zmod.unsigned (N.v9502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9502 s i)) at 1.
  unfold R.v9502, N.v9502.
  rewrite ?node_9498.
  rewrite ?node_9501.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9503 (s : N.State) (i : N.Inputs) :
  R.v9503 (state s) (inputs i) = Zmod.unsigned (N.v9503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9503 s i)) at 1.
  unfold R.v9503, N.v9503.
  rewrite ?node_9344.
  rewrite ?node_9347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9504 (s : N.State) (i : N.Inputs) :
  R.v9504 (state s) (inputs i) = Zmod.unsigned (N.v9504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9504 s i)) at 1.
  unfold R.v9504, N.v9504.
  rewrite ?node_9348.
  rewrite ?node_9351.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9505 (s : N.State) (i : N.Inputs) :
  R.v9505 (state s) (inputs i) = Zmod.unsigned (N.v9505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9505 s i)) at 1.
  unfold R.v9505, N.v9505.
  rewrite ?node_9503.
  rewrite ?node_9504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9506 (s : N.State) (i : N.Inputs) :
  R.v9506 (state s) (inputs i) = Zmod.unsigned (N.v9506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9506 s i)) at 1.
  unfold R.v9506, N.v9506.
  rewrite ?node_9502.
  rewrite ?node_9505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9507 (s : N.State) (i : N.Inputs) :
  R.v9507 (state s) (inputs i) = Zmod.unsigned (N.v9507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9507 s i)) at 1.
  unfold R.v9507, N.v9507.
  rewrite ?node_9333.
  rewrite ?node_9352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9508 (s : N.State) (i : N.Inputs) :
  R.v9508 (state s) (inputs i) = Zmod.unsigned (N.v9508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9508 s i)) at 1.
  unfold R.v9508, N.v9508.
  rewrite ?node_9353.
  rewrite ?node_9356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9509 (s : N.State) (i : N.Inputs) :
  R.v9509 (state s) (inputs i) = Zmod.unsigned (N.v9509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9509 s i)) at 1.
  unfold R.v9509, N.v9509.
  rewrite ?node_9507.
  rewrite ?node_9508.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9510 (s : N.State) (i : N.Inputs) :
  R.v9510 (state s) (inputs i) = Zmod.unsigned (N.v9510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9510 s i)) at 1.
  unfold R.v9510, N.v9510.
  rewrite ?node_9506.
  rewrite ?node_9509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9511 (s : N.State) (i : N.Inputs) :
  R.v9511 (state s) (inputs i) = Zmod.unsigned (N.v9511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9511 s i)) at 1.
  unfold R.v9511, N.v9511.
  rewrite ?node_9357.
  rewrite ?node_9360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9512 (s : N.State) (i : N.Inputs) :
  R.v9512 (state s) (inputs i) = Zmod.unsigned (N.v9512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9512 s i)) at 1.
  unfold R.v9512, N.v9512.
  rewrite ?node_9361.
  rewrite ?node_9364.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9513 (s : N.State) (i : N.Inputs) :
  R.v9513 (state s) (inputs i) = Zmod.unsigned (N.v9513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9513 s i)) at 1.
  unfold R.v9513, N.v9513.
  rewrite ?node_9511.
  rewrite ?node_9512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9514 (s : N.State) (i : N.Inputs) :
  R.v9514 (state s) (inputs i) = Zmod.unsigned (N.v9514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9514 s i)) at 1.
  unfold R.v9514, N.v9514.
  rewrite ?node_9510.
  rewrite ?node_9513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9515 (s : N.State) (i : N.Inputs) :
  R.v9515 (state s) (inputs i) = Zmod.unsigned (N.v9515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9515 s i)) at 1.
  unfold R.v9515, N.v9515.
  rewrite ?node_9514.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2389_nr_5F2420.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2389_nr_5F2420 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9516 (s : N.State) (i : N.Inputs) :
  R.v9516 (state s) (inputs i) = Zmod.unsigned (N.v9516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9516 s i)) at 1.
  unfold R.v9516, N.v9516.
  rewrite ?node_9365.
  rewrite ?node_9368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9517 (s : N.State) (i : N.Inputs) :
  R.v9517 (state s) (inputs i) = Zmod.unsigned (N.v9517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9517 s i)) at 1.
  unfold R.v9517, N.v9517.
  rewrite ?node_9516.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2390_nr_5F2421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2390_nr_5F2421 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9518 (s : N.State) (i : N.Inputs) :
  R.v9518 (state s) (inputs i) = Zmod.unsigned (N.v9518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9518 s i)) at 1.
  unfold R.v9518, N.v9518.
  rewrite !state_r959_nr_5F959.
  rewrite !state_r960_nr_5F960.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r959_nr_5F959 s)).
  rewrite ?(bits.mod_to_Z (N.r960_nr_5F960 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9519 (s : N.State) (i : N.Inputs) :
  R.v9519 (state s) (inputs i) = Zmod.unsigned (N.v9519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9519 s i)) at 1.
  unfold R.v9519, N.v9519.
  rewrite ?node_9518.
  rewrite !state_r961_nr_5F961.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r961_nr_5F961 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9520 (s : N.State) (i : N.Inputs) :
  R.v9520 (state s) (inputs i) = Zmod.unsigned (N.v9520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9520 s i)) at 1.
  unfold R.v9520, N.v9520.
  rewrite ?node_9519.
  rewrite !state_r962_nr_5F962.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r962_nr_5F962 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9521 (s : N.State) (i : N.Inputs) :
  R.v9521 (state s) (inputs i) = Zmod.unsigned (N.v9521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9521 s i)) at 1.
  unfold R.v9521, N.v9521.
  rewrite !state_r928_nr_5F928.
  rewrite !state_r929_nr_5F929.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r928_nr_5F928 s)).
  rewrite ?(bits.mod_to_Z (N.r929_nr_5F929 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9522 (s : N.State) (i : N.Inputs) :
  R.v9522 (state s) (inputs i) = Zmod.unsigned (N.v9522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9522 s i)) at 1.
  unfold R.v9522, N.v9522.
  rewrite ?node_9373.
  rewrite !state_r930_nr_5F930.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r930_nr_5F930 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9523 (s : N.State) (i : N.Inputs) :
  R.v9523 (state s) (inputs i) = Zmod.unsigned (N.v9523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9523 s i)) at 1.
  unfold R.v9523, N.v9523.
  rewrite ?node_9521.
  rewrite ?node_9522.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9524 (s : N.State) (i : N.Inputs) :
  R.v9524 (state s) (inputs i) = Zmod.unsigned (N.v9524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9524 s i)) at 1.
  unfold R.v9524, N.v9524.
  rewrite ?node_9520.
  rewrite ?node_9523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9525 (s : N.State) (i : N.Inputs) :
  R.v9525 (state s) (inputs i) = Zmod.unsigned (N.v9525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9525 s i)) at 1.
  unfold R.v9525, N.v9525.
  rewrite !state_r963_nr_5F963.
  rewrite !state_r964_nr_5F964.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r963_nr_5F963 s)).
  rewrite ?(bits.mod_to_Z (N.r964_nr_5F964 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9526 (s : N.State) (i : N.Inputs) :
  R.v9526 (state s) (inputs i) = Zmod.unsigned (N.v9526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9526 s i)) at 1.
  unfold R.v9526, N.v9526.
  rewrite ?node_9525.
  rewrite !state_r965_nr_5F965.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r965_nr_5F965 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9527 (s : N.State) (i : N.Inputs) :
  R.v9527 (state s) (inputs i) = Zmod.unsigned (N.v9527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9527 s i)) at 1.
  unfold R.v9527, N.v9527.
  rewrite ?node_9526.
  rewrite !state_r966_nr_5F966.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r966_nr_5F966 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9528 (s : N.State) (i : N.Inputs) :
  R.v9528 (state s) (inputs i) = Zmod.unsigned (N.v9528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9528 s i)) at 1.
  unfold R.v9528, N.v9528.
  rewrite !state_r932_nr_5F932.
  rewrite !state_r933_nr_5F933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r932_nr_5F932 s)).
  rewrite ?(bits.mod_to_Z (N.r933_nr_5F933 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9529 (s : N.State) (i : N.Inputs) :
  R.v9529 (state s) (inputs i) = Zmod.unsigned (N.v9529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9529 s i)) at 1.
  unfold R.v9529, N.v9529.
  rewrite ?node_9380.
  rewrite !state_r934_nr_5F934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r934_nr_5F934 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9530 (s : N.State) (i : N.Inputs) :
  R.v9530 (state s) (inputs i) = Zmod.unsigned (N.v9530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9530 s i)) at 1.
  unfold R.v9530, N.v9530.
  rewrite ?node_9528.
  rewrite ?node_9529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9531 (s : N.State) (i : N.Inputs) :
  R.v9531 (state s) (inputs i) = Zmod.unsigned (N.v9531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9531 s i)) at 1.
  unfold R.v9531, N.v9531.
  rewrite ?node_9527.
  rewrite ?node_9530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9532 (s : N.State) (i : N.Inputs) :
  R.v9532 (state s) (inputs i) = Zmod.unsigned (N.v9532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9532 s i)) at 1.
  unfold R.v9532, N.v9532.
  rewrite ?node_9524.
  rewrite ?node_9531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9533 (s : N.State) (i : N.Inputs) :
  R.v9533 (state s) (inputs i) = Zmod.unsigned (N.v9533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9533 s i)) at 1.
  unfold R.v9533, N.v9533.
  rewrite !state_r967_nr_5F967.
  rewrite !state_r968_nr_5F968.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r967_nr_5F967 s)).
  rewrite ?(bits.mod_to_Z (N.r968_nr_5F968 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9534 (s : N.State) (i : N.Inputs) :
  R.v9534 (state s) (inputs i) = Zmod.unsigned (N.v9534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9534 s i)) at 1.
  unfold R.v9534, N.v9534.
  rewrite ?node_9533.
  rewrite !state_r969_nr_5F969.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r969_nr_5F969 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9535 (s : N.State) (i : N.Inputs) :
  R.v9535 (state s) (inputs i) = Zmod.unsigned (N.v9535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9535 s i)) at 1.
  unfold R.v9535, N.v9535.
  rewrite ?node_9534.
  rewrite !state_r970_nr_5F970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r970_nr_5F970 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9536 (s : N.State) (i : N.Inputs) :
  R.v9536 (state s) (inputs i) = Zmod.unsigned (N.v9536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9536 s i)) at 1.
  unfold R.v9536, N.v9536.
  rewrite !state_r936_nr_5F936.
  rewrite !state_r937_nr_5F937.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r936_nr_5F936 s)).
  rewrite ?(bits.mod_to_Z (N.r937_nr_5F937 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9537 (s : N.State) (i : N.Inputs) :
  R.v9537 (state s) (inputs i) = Zmod.unsigned (N.v9537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9537 s i)) at 1.
  unfold R.v9537, N.v9537.
  rewrite ?node_9388.
  rewrite !state_r938_nr_5F938.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r938_nr_5F938 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9538 (s : N.State) (i : N.Inputs) :
  R.v9538 (state s) (inputs i) = Zmod.unsigned (N.v9538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9538 s i)) at 1.
  unfold R.v9538, N.v9538.
  rewrite ?node_9536.
  rewrite ?node_9537.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9539 (s : N.State) (i : N.Inputs) :
  R.v9539 (state s) (inputs i) = Zmod.unsigned (N.v9539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9539 s i)) at 1.
  unfold R.v9539, N.v9539.
  rewrite ?node_9535.
  rewrite ?node_9538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9540 (s : N.State) (i : N.Inputs) :
  R.v9540 (state s) (inputs i) = Zmod.unsigned (N.v9540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9540 s i)) at 1.
  unfold R.v9540, N.v9540.
  rewrite ?node_9532.
  rewrite ?node_9539.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9541 (s : N.State) (i : N.Inputs) :
  R.v9541 (state s) (inputs i) = Zmod.unsigned (N.v9541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9541 s i)) at 1.
  unfold R.v9541, N.v9541.
  rewrite !state_r971_nr_5F971.
  rewrite !state_r972_nr_5F972.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r971_nr_5F971 s)).
  rewrite ?(bits.mod_to_Z (N.r972_nr_5F972 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9542 (s : N.State) (i : N.Inputs) :
  R.v9542 (state s) (inputs i) = Zmod.unsigned (N.v9542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9542 s i)) at 1.
  unfold R.v9542, N.v9542.
  rewrite ?node_9541.
  rewrite !state_r973_nr_5F973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r973_nr_5F973 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9543 (s : N.State) (i : N.Inputs) :
  R.v9543 (state s) (inputs i) = Zmod.unsigned (N.v9543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9543 s i)) at 1.
  unfold R.v9543, N.v9543.
  rewrite ?node_9542.
  rewrite !state_r974_nr_5F974.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r974_nr_5F974 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9544 (s : N.State) (i : N.Inputs) :
  R.v9544 (state s) (inputs i) = Zmod.unsigned (N.v9544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9544 s i)) at 1.
  unfold R.v9544, N.v9544.
  rewrite !state_r940_nr_5F940.
  rewrite !state_r941_nr_5F941.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r940_nr_5F940 s)).
  rewrite ?(bits.mod_to_Z (N.r941_nr_5F941 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9545 (s : N.State) (i : N.Inputs) :
  R.v9545 (state s) (inputs i) = Zmod.unsigned (N.v9545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9545 s i)) at 1.
  unfold R.v9545, N.v9545.
  rewrite ?node_9396.
  rewrite !state_r942_nr_5F942.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r942_nr_5F942 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9546 (s : N.State) (i : N.Inputs) :
  R.v9546 (state s) (inputs i) = Zmod.unsigned (N.v9546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9546 s i)) at 1.
  unfold R.v9546, N.v9546.
  rewrite ?node_9544.
  rewrite ?node_9545.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9547 (s : N.State) (i : N.Inputs) :
  R.v9547 (state s) (inputs i) = Zmod.unsigned (N.v9547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9547 s i)) at 1.
  unfold R.v9547, N.v9547.
  rewrite ?node_9543.
  rewrite ?node_9546.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9548 (s : N.State) (i : N.Inputs) :
  R.v9548 (state s) (inputs i) = Zmod.unsigned (N.v9548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9548 s i)) at 1.
  unfold R.v9548, N.v9548.
  rewrite ?node_9540.
  rewrite ?node_9547.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9549 (s : N.State) (i : N.Inputs) :
  R.v9549 (state s) (inputs i) = Zmod.unsigned (N.v9549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9549 s i)) at 1.
  unfold R.v9549, N.v9549.
  rewrite ?node_9379.
  rewrite ?node_9386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9550 (s : N.State) (i : N.Inputs) :
  R.v9550 (state s) (inputs i) = Zmod.unsigned (N.v9550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9550 s i)) at 1.
  unfold R.v9550, N.v9550.
  rewrite ?node_9387.
  rewrite ?node_9394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9551 (s : N.State) (i : N.Inputs) :
  R.v9551 (state s) (inputs i) = Zmod.unsigned (N.v9551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9551 s i)) at 1.
  unfold R.v9551, N.v9551.
  rewrite ?node_9549.
  rewrite ?node_9550.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9552 (s : N.State) (i : N.Inputs) :
  R.v9552 (state s) (inputs i) = Zmod.unsigned (N.v9552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9552 s i)) at 1.
  unfold R.v9552, N.v9552.
  rewrite ?node_9548.
  rewrite ?node_9551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9553 (s : N.State) (i : N.Inputs) :
  R.v9553 (state s) (inputs i) = Zmod.unsigned (N.v9553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9553 s i)) at 1.
  unfold R.v9553, N.v9553.
  rewrite !state_r975_nr_5F975.
  rewrite !state_r976_nr_5F976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r975_nr_5F975 s)).
  rewrite ?(bits.mod_to_Z (N.r976_nr_5F976 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9554 (s : N.State) (i : N.Inputs) :
  R.v9554 (state s) (inputs i) = Zmod.unsigned (N.v9554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9554 s i)) at 1.
  unfold R.v9554, N.v9554.
  rewrite ?node_9553.
  rewrite !state_r977_nr_5F977.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r977_nr_5F977 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9555 (s : N.State) (i : N.Inputs) :
  R.v9555 (state s) (inputs i) = Zmod.unsigned (N.v9555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9555 s i)) at 1.
  unfold R.v9555, N.v9555.
  rewrite ?node_9554.
  rewrite !state_r978_nr_5F978.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r978_nr_5F978 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9556 (s : N.State) (i : N.Inputs) :
  R.v9556 (state s) (inputs i) = Zmod.unsigned (N.v9556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9556 s i)) at 1.
  unfold R.v9556, N.v9556.
  rewrite !state_r944_nr_5F944.
  rewrite !state_r945_nr_5F945.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r944_nr_5F944 s)).
  rewrite ?(bits.mod_to_Z (N.r945_nr_5F945 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9557 (s : N.State) (i : N.Inputs) :
  R.v9557 (state s) (inputs i) = Zmod.unsigned (N.v9557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9557 s i)) at 1.
  unfold R.v9557, N.v9557.
  rewrite ?node_9408.
  rewrite !state_r946_nr_5F946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r946_nr_5F946 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9558 (s : N.State) (i : N.Inputs) :
  R.v9558 (state s) (inputs i) = Zmod.unsigned (N.v9558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9558 s i)) at 1.
  unfold R.v9558, N.v9558.
  rewrite ?node_9556.
  rewrite ?node_9557.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9559 (s : N.State) (i : N.Inputs) :
  R.v9559 (state s) (inputs i) = Zmod.unsigned (N.v9559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9559 s i)) at 1.
  unfold R.v9559, N.v9559.
  rewrite ?node_9555.
  rewrite ?node_9558.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9560 (s : N.State) (i : N.Inputs) :
  R.v9560 (state s) (inputs i) = Zmod.unsigned (N.v9560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9560 s i)) at 1.
  unfold R.v9560, N.v9560.
  rewrite !state_r979_nr_5F979.
  rewrite !state_r980_nr_5F980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r979_nr_5F979 s)).
  rewrite ?(bits.mod_to_Z (N.r980_nr_5F980 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9561 (s : N.State) (i : N.Inputs) :
  R.v9561 (state s) (inputs i) = Zmod.unsigned (N.v9561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9561 s i)) at 1.
  unfold R.v9561, N.v9561.
  rewrite ?node_9560.
  rewrite !state_r981_nr_5F981.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r981_nr_5F981 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9562 (s : N.State) (i : N.Inputs) :
  R.v9562 (state s) (inputs i) = Zmod.unsigned (N.v9562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9562 s i)) at 1.
  unfold R.v9562, N.v9562.
  rewrite ?node_9561.
  rewrite !state_r982_nr_5F982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r982_nr_5F982 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9563 (s : N.State) (i : N.Inputs) :
  R.v9563 (state s) (inputs i) = Zmod.unsigned (N.v9563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9563 s i)) at 1.
  unfold R.v9563, N.v9563.
  rewrite !state_r948_nr_5F948.
  rewrite !state_r949_nr_5F949.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r948_nr_5F948 s)).
  rewrite ?(bits.mod_to_Z (N.r949_nr_5F949 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9564 (s : N.State) (i : N.Inputs) :
  R.v9564 (state s) (inputs i) = Zmod.unsigned (N.v9564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9564 s i)) at 1.
  unfold R.v9564, N.v9564.
  rewrite ?node_9415.
  rewrite !state_r950_nr_5F950.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r950_nr_5F950 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9565 (s : N.State) (i : N.Inputs) :
  R.v9565 (state s) (inputs i) = Zmod.unsigned (N.v9565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9565 s i)) at 1.
  unfold R.v9565, N.v9565.
  rewrite ?node_9563.
  rewrite ?node_9564.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9566 (s : N.State) (i : N.Inputs) :
  R.v9566 (state s) (inputs i) = Zmod.unsigned (N.v9566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9566 s i)) at 1.
  unfold R.v9566, N.v9566.
  rewrite ?node_9562.
  rewrite ?node_9565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9567 (s : N.State) (i : N.Inputs) :
  R.v9567 (state s) (inputs i) = Zmod.unsigned (N.v9567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9567 s i)) at 1.
  unfold R.v9567, N.v9567.
  rewrite ?node_9559.
  rewrite ?node_9566.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9568 (s : N.State) (i : N.Inputs) :
  R.v9568 (state s) (inputs i) = Zmod.unsigned (N.v9568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9568 s i)) at 1.
  unfold R.v9568, N.v9568.
  rewrite !state_r983_nr_5F983.
  rewrite !state_r984_nr_5F984.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r983_nr_5F983 s)).
  rewrite ?(bits.mod_to_Z (N.r984_nr_5F984 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9569 (s : N.State) (i : N.Inputs) :
  R.v9569 (state s) (inputs i) = Zmod.unsigned (N.v9569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9569 s i)) at 1.
  unfold R.v9569, N.v9569.
  rewrite ?node_9568.
  rewrite !state_r985_nr_5F985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r985_nr_5F985 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9570 (s : N.State) (i : N.Inputs) :
  R.v9570 (state s) (inputs i) = Zmod.unsigned (N.v9570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9570 s i)) at 1.
  unfold R.v9570, N.v9570.
  rewrite ?node_9569.
  rewrite !state_r986_nr_5F986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r986_nr_5F986 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9571 (s : N.State) (i : N.Inputs) :
  R.v9571 (state s) (inputs i) = Zmod.unsigned (N.v9571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9571 s i)) at 1.
  unfold R.v9571, N.v9571.
  rewrite !state_r952_nr_5F952.
  rewrite !state_r953_nr_5F953.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r952_nr_5F952 s)).
  rewrite ?(bits.mod_to_Z (N.r953_nr_5F953 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9572 (s : N.State) (i : N.Inputs) :
  R.v9572 (state s) (inputs i) = Zmod.unsigned (N.v9572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9572 s i)) at 1.
  unfold R.v9572, N.v9572.
  rewrite ?node_9423.
  rewrite !state_r954_nr_5F954.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r954_nr_5F954 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9573 (s : N.State) (i : N.Inputs) :
  R.v9573 (state s) (inputs i) = Zmod.unsigned (N.v9573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9573 s i)) at 1.
  unfold R.v9573, N.v9573.
  rewrite ?node_9571.
  rewrite ?node_9572.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9574 (s : N.State) (i : N.Inputs) :
  R.v9574 (state s) (inputs i) = Zmod.unsigned (N.v9574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9574 s i)) at 1.
  unfold R.v9574, N.v9574.
  rewrite ?node_9570.
  rewrite ?node_9573.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9575 (s : N.State) (i : N.Inputs) :
  R.v9575 (state s) (inputs i) = Zmod.unsigned (N.v9575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9575 s i)) at 1.
  unfold R.v9575, N.v9575.
  rewrite ?node_9567.
  rewrite ?node_9574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9576 (s : N.State) (i : N.Inputs) :
  R.v9576 (state s) (inputs i) = Zmod.unsigned (N.v9576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9576 s i)) at 1.
  unfold R.v9576, N.v9576.
  rewrite !state_r987_nr_5F987.
  rewrite !state_r988_nr_5F988.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r987_nr_5F987 s)).
  rewrite ?(bits.mod_to_Z (N.r988_nr_5F988 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9577 (s : N.State) (i : N.Inputs) :
  R.v9577 (state s) (inputs i) = Zmod.unsigned (N.v9577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9577 s i)) at 1.
  unfold R.v9577, N.v9577.
  rewrite ?node_9576.
  rewrite !state_r989_nr_5F989.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r989_nr_5F989 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9578 (s : N.State) (i : N.Inputs) :
  R.v9578 (state s) (inputs i) = Zmod.unsigned (N.v9578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9578 s i)) at 1.
  unfold R.v9578, N.v9578.
  rewrite ?node_9575.
  rewrite ?node_9577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9579 (s : N.State) (i : N.Inputs) :
  R.v9579 (state s) (inputs i) = Zmod.unsigned (N.v9579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9579 s i)) at 1.
  unfold R.v9579, N.v9579.
  rewrite ?node_9414.
  rewrite ?node_9421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9580 (s : N.State) (i : N.Inputs) :
  R.v9580 (state s) (inputs i) = Zmod.unsigned (N.v9580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9580 s i)) at 1.
  unfold R.v9580, N.v9580.
  rewrite ?node_9422.
  rewrite ?node_9429.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9581 (s : N.State) (i : N.Inputs) :
  R.v9581 (state s) (inputs i) = Zmod.unsigned (N.v9581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9581 s i)) at 1.
  unfold R.v9581, N.v9581.
  rewrite ?node_9579.
  rewrite ?node_9580.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9582 (s : N.State) (i : N.Inputs) :
  R.v9582 (state s) (inputs i) = Zmod.unsigned (N.v9582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9582 s i)) at 1.
  unfold R.v9582, N.v9582.
  rewrite ?node_9578.
  rewrite ?node_9581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9583 (s : N.State) (i : N.Inputs) :
  R.v9583 (state s) (inputs i) = Zmod.unsigned (N.v9583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9583 s i)) at 1.
  unfold R.v9583, N.v9583.
  rewrite ?node_9552.
  rewrite ?node_9582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9584 (s : N.State) (i : N.Inputs) :
  R.v9584 (state s) (inputs i) = Zmod.unsigned (N.v9584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9584 s i)) at 1.
  unfold R.v9584, N.v9584.
  rewrite ?node_9374.
  rewrite !state_r931_nr_5F931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r931_nr_5F931 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9585 (s : N.State) (i : N.Inputs) :
  R.v9585 (state s) (inputs i) = Zmod.unsigned (N.v9585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9585 s i)) at 1.
  unfold R.v9585, N.v9585.
  rewrite ?node_9375.
  rewrite ?node_9378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9586 (s : N.State) (i : N.Inputs) :
  R.v9586 (state s) (inputs i) = Zmod.unsigned (N.v9586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9586 s i)) at 1.
  unfold R.v9586, N.v9586.
  rewrite ?node_9584.
  rewrite ?node_9585.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9587 (s : N.State) (i : N.Inputs) :
  R.v9587 (state s) (inputs i) = Zmod.unsigned (N.v9587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9587 s i)) at 1.
  unfold R.v9587, N.v9587.
  rewrite ?node_9381.
  rewrite !state_r935_nr_5F935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r935_nr_5F935 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9588 (s : N.State) (i : N.Inputs) :
  R.v9588 (state s) (inputs i) = Zmod.unsigned (N.v9588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9588 s i)) at 1.
  unfold R.v9588, N.v9588.
  rewrite ?node_9382.
  rewrite ?node_9385.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9589 (s : N.State) (i : N.Inputs) :
  R.v9589 (state s) (inputs i) = Zmod.unsigned (N.v9589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9589 s i)) at 1.
  unfold R.v9589, N.v9589.
  rewrite ?node_9587.
  rewrite ?node_9588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9590 (s : N.State) (i : N.Inputs) :
  R.v9590 (state s) (inputs i) = Zmod.unsigned (N.v9590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9590 s i)) at 1.
  unfold R.v9590, N.v9590.
  rewrite ?node_9586.
  rewrite ?node_9589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9591 (s : N.State) (i : N.Inputs) :
  R.v9591 (state s) (inputs i) = Zmod.unsigned (N.v9591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9591 s i)) at 1.
  unfold R.v9591, N.v9591.
  rewrite ?node_9389.
  rewrite !state_r939_nr_5F939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r939_nr_5F939 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9592 (s : N.State) (i : N.Inputs) :
  R.v9592 (state s) (inputs i) = Zmod.unsigned (N.v9592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9592 s i)) at 1.
  unfold R.v9592, N.v9592.
  rewrite ?node_9390.
  rewrite ?node_9393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9593 (s : N.State) (i : N.Inputs) :
  R.v9593 (state s) (inputs i) = Zmod.unsigned (N.v9593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9593 s i)) at 1.
  unfold R.v9593, N.v9593.
  rewrite ?node_9591.
  rewrite ?node_9592.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9594 (s : N.State) (i : N.Inputs) :
  R.v9594 (state s) (inputs i) = Zmod.unsigned (N.v9594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9594 s i)) at 1.
  unfold R.v9594, N.v9594.
  rewrite ?node_9590.
  rewrite ?node_9593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9595 (s : N.State) (i : N.Inputs) :
  R.v9595 (state s) (inputs i) = Zmod.unsigned (N.v9595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9595 s i)) at 1.
  unfold R.v9595, N.v9595.
  rewrite ?node_9397.
  rewrite !state_r943_nr_5F943.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r943_nr_5F943 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9596 (s : N.State) (i : N.Inputs) :
  R.v9596 (state s) (inputs i) = Zmod.unsigned (N.v9596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9596 s i)) at 1.
  unfold R.v9596, N.v9596.
  rewrite ?node_9398.
  rewrite ?node_9401.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9597 (s : N.State) (i : N.Inputs) :
  R.v9597 (state s) (inputs i) = Zmod.unsigned (N.v9597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9597 s i)) at 1.
  unfold R.v9597, N.v9597.
  rewrite ?node_9595.
  rewrite ?node_9596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9598 (s : N.State) (i : N.Inputs) :
  R.v9598 (state s) (inputs i) = Zmod.unsigned (N.v9598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9598 s i)) at 1.
  unfold R.v9598, N.v9598.
  rewrite ?node_9594.
  rewrite ?node_9597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9599 (s : N.State) (i : N.Inputs) :
  R.v9599 (state s) (inputs i) = Zmod.unsigned (N.v9599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9599 s i)) at 1.
  unfold R.v9599, N.v9599.
  rewrite ?node_9441.
  rewrite ?node_9444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9600 (s : N.State) (i : N.Inputs) :
  R.v9600 (state s) (inputs i) = Zmod.unsigned (N.v9600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9600 s i)) at 1.
  unfold R.v9600, N.v9600.
  rewrite ?node_9445.
  rewrite ?node_9448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9601 (s : N.State) (i : N.Inputs) :
  R.v9601 (state s) (inputs i) = Zmod.unsigned (N.v9601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9601 s i)) at 1.
  unfold R.v9601, N.v9601.
  rewrite ?node_9599.
  rewrite ?node_9600.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9602 (s : N.State) (i : N.Inputs) :
  R.v9602 (state s) (inputs i) = Zmod.unsigned (N.v9602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9602 s i)) at 1.
  unfold R.v9602, N.v9602.
  rewrite ?node_9598.
  rewrite ?node_9601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9603 (s : N.State) (i : N.Inputs) :
  R.v9603 (state s) (inputs i) = Zmod.unsigned (N.v9603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9603 s i)) at 1.
  unfold R.v9603, N.v9603.
  rewrite ?node_9583.
  rewrite ?node_9602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9604 (s : N.State) (i : N.Inputs) :
  R.v9604 (state s) (inputs i) = Zmod.unsigned (N.v9604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9604 s i)) at 1.
  unfold R.v9604, N.v9604.
  rewrite ?node_9409.
  rewrite !state_r947_nr_5F947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r947_nr_5F947 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9605 (s : N.State) (i : N.Inputs) :
  R.v9605 (state s) (inputs i) = Zmod.unsigned (N.v9605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9605 s i)) at 1.
  unfold R.v9605, N.v9605.
  rewrite ?node_9410.
  rewrite ?node_9413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9606 (s : N.State) (i : N.Inputs) :
  R.v9606 (state s) (inputs i) = Zmod.unsigned (N.v9606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9606 s i)) at 1.
  unfold R.v9606, N.v9606.
  rewrite ?node_9604.
  rewrite ?node_9605.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9607 (s : N.State) (i : N.Inputs) :
  R.v9607 (state s) (inputs i) = Zmod.unsigned (N.v9607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9607 s i)) at 1.
  unfold R.v9607, N.v9607.
  rewrite ?node_9416.
  rewrite !state_r951_nr_5F951.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r951_nr_5F951 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9608 (s : N.State) (i : N.Inputs) :
  R.v9608 (state s) (inputs i) = Zmod.unsigned (N.v9608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9608 s i)) at 1.
  unfold R.v9608, N.v9608.
  rewrite ?node_9417.
  rewrite ?node_9420.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9609 (s : N.State) (i : N.Inputs) :
  R.v9609 (state s) (inputs i) = Zmod.unsigned (N.v9609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9609 s i)) at 1.
  unfold R.v9609, N.v9609.
  rewrite ?node_9607.
  rewrite ?node_9608.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9610 (s : N.State) (i : N.Inputs) :
  R.v9610 (state s) (inputs i) = Zmod.unsigned (N.v9610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9610 s i)) at 1.
  unfold R.v9610, N.v9610.
  rewrite ?node_9606.
  rewrite ?node_9609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9611 (s : N.State) (i : N.Inputs) :
  R.v9611 (state s) (inputs i) = Zmod.unsigned (N.v9611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9611 s i)) at 1.
  unfold R.v9611, N.v9611.
  rewrite ?node_9424.
  rewrite !state_r955_nr_5F955.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r955_nr_5F955 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9612 (s : N.State) (i : N.Inputs) :
  R.v9612 (state s) (inputs i) = Zmod.unsigned (N.v9612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9612 s i)) at 1.
  unfold R.v9612, N.v9612.
  rewrite ?node_9425.
  rewrite ?node_9428.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9613 (s : N.State) (i : N.Inputs) :
  R.v9613 (state s) (inputs i) = Zmod.unsigned (N.v9613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9613 s i)) at 1.
  unfold R.v9613, N.v9613.
  rewrite ?node_9611.
  rewrite ?node_9612.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9614 (s : N.State) (i : N.Inputs) :
  R.v9614 (state s) (inputs i) = Zmod.unsigned (N.v9614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9614 s i)) at 1.
  unfold R.v9614, N.v9614.
  rewrite ?node_9610.
  rewrite ?node_9613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9615 (s : N.State) (i : N.Inputs) :
  R.v9615 (state s) (inputs i) = Zmod.unsigned (N.v9615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9615 s i)) at 1.
  unfold R.v9615, N.v9615.
  rewrite !state_r956_nr_5F956.
  rewrite !state_r957_nr_5F957.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r956_nr_5F956 s)).
  rewrite ?(bits.mod_to_Z (N.r957_nr_5F957 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9616 (s : N.State) (i : N.Inputs) :
  R.v9616 (state s) (inputs i) = Zmod.unsigned (N.v9616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9616 s i)) at 1.
  unfold R.v9616, N.v9616.
  rewrite ?node_9431.
  rewrite !state_r958_nr_5F958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r958_nr_5F958 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9617 (s : N.State) (i : N.Inputs) :
  R.v9617 (state s) (inputs i) = Zmod.unsigned (N.v9617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9617 s i)) at 1.
  unfold R.v9617, N.v9617.
  rewrite ?node_9615.
  rewrite ?node_9616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9618 (s : N.State) (i : N.Inputs) :
  R.v9618 (state s) (inputs i) = Zmod.unsigned (N.v9618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9618 s i)) at 1.
  unfold R.v9618, N.v9618.
  rewrite ?node_9614.
  rewrite ?node_9617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9619 (s : N.State) (i : N.Inputs) :
  R.v9619 (state s) (inputs i) = Zmod.unsigned (N.v9619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9619 s i)) at 1.
  unfold R.v9619, N.v9619.
  rewrite ?node_9461.
  rewrite ?node_9464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9620 (s : N.State) (i : N.Inputs) :
  R.v9620 (state s) (inputs i) = Zmod.unsigned (N.v9620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9620 s i)) at 1.
  unfold R.v9620, N.v9620.
  rewrite ?node_9465.
  rewrite ?node_9468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9621 (s : N.State) (i : N.Inputs) :
  R.v9621 (state s) (inputs i) = Zmod.unsigned (N.v9621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9621 s i)) at 1.
  unfold R.v9621, N.v9621.
  rewrite ?node_9619.
  rewrite ?node_9620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9622 (s : N.State) (i : N.Inputs) :
  R.v9622 (state s) (inputs i) = Zmod.unsigned (N.v9622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9622 s i)) at 1.
  unfold R.v9622, N.v9622.
  rewrite ?node_9618.
  rewrite ?node_9621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9623 (s : N.State) (i : N.Inputs) :
  R.v9623 (state s) (inputs i) = Zmod.unsigned (N.v9623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9623 s i)) at 1.
  unfold R.v9623, N.v9623.
  rewrite ?node_9603.
  rewrite ?node_9622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9624 (s : N.State) (i : N.Inputs) :
  R.v9624 (state s) (inputs i) = Zmod.unsigned (N.v9624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9624 s i)) at 1.
  unfold R.v9624, N.v9624.
  rewrite ?node_9407.
  rewrite ?node_9437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9625 (s : N.State) (i : N.Inputs) :
  R.v9625 (state s) (inputs i) = Zmod.unsigned (N.v9625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9625 s i)) at 1.
  unfold R.v9625, N.v9625.
  rewrite ?node_9438.
  rewrite ?node_9457.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9626 (s : N.State) (i : N.Inputs) :
  R.v9626 (state s) (inputs i) = Zmod.unsigned (N.v9626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9626 s i)) at 1.
  unfold R.v9626, N.v9626.
  rewrite ?node_9624.
  rewrite ?node_9625.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9627 (s : N.State) (i : N.Inputs) :
  R.v9627 (state s) (inputs i) = Zmod.unsigned (N.v9627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9627 s i)) at 1.
  unfold R.v9627, N.v9627.
  rewrite ?node_9623.
  rewrite ?node_9626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9628 (s : N.State) (i : N.Inputs) :
  R.v9628 (state s) (inputs i) = Zmod.unsigned (N.v9628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9628 s i)) at 1.
  unfold R.v9628, N.v9628.
  rewrite ?node_9395.
  rewrite ?node_9402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9629 (s : N.State) (i : N.Inputs) :
  R.v9629 (state s) (inputs i) = Zmod.unsigned (N.v9629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9629 s i)) at 1.
  unfold R.v9629, N.v9629.
  rewrite ?node_9403.
  rewrite ?node_9406.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9630 (s : N.State) (i : N.Inputs) :
  R.v9630 (state s) (inputs i) = Zmod.unsigned (N.v9630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9630 s i)) at 1.
  unfold R.v9630, N.v9630.
  rewrite ?node_9628.
  rewrite ?node_9629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9631 (s : N.State) (i : N.Inputs) :
  R.v9631 (state s) (inputs i) = Zmod.unsigned (N.v9631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9631 s i)) at 1.
  unfold R.v9631, N.v9631.
  rewrite ?node_9430.
  rewrite ?node_9432.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9632 (s : N.State) (i : N.Inputs) :
  R.v9632 (state s) (inputs i) = Zmod.unsigned (N.v9632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9632 s i)) at 1.
  unfold R.v9632, N.v9632.
  rewrite ?node_9433.
  rewrite ?node_9436.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9633 (s : N.State) (i : N.Inputs) :
  R.v9633 (state s) (inputs i) = Zmod.unsigned (N.v9633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9633 s i)) at 1.
  unfold R.v9633, N.v9633.
  rewrite ?node_9631.
  rewrite ?node_9632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9634 (s : N.State) (i : N.Inputs) :
  R.v9634 (state s) (inputs i) = Zmod.unsigned (N.v9634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9634 s i)) at 1.
  unfold R.v9634, N.v9634.
  rewrite ?node_9630.
  rewrite ?node_9633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9635 (s : N.State) (i : N.Inputs) :
  R.v9635 (state s) (inputs i) = Zmod.unsigned (N.v9635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9635 s i)) at 1.
  unfold R.v9635, N.v9635.
  rewrite ?node_9449.
  rewrite ?node_9452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9636 (s : N.State) (i : N.Inputs) :
  R.v9636 (state s) (inputs i) = Zmod.unsigned (N.v9636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9636 s i)) at 1.
  unfold R.v9636, N.v9636.
  rewrite ?node_9453.
  rewrite ?node_9456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9637 (s : N.State) (i : N.Inputs) :
  R.v9637 (state s) (inputs i) = Zmod.unsigned (N.v9637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9637 s i)) at 1.
  unfold R.v9637, N.v9637.
  rewrite ?node_9635.
  rewrite ?node_9636.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9638 (s : N.State) (i : N.Inputs) :
  R.v9638 (state s) (inputs i) = Zmod.unsigned (N.v9638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9638 s i)) at 1.
  unfold R.v9638, N.v9638.
  rewrite ?node_9634.
  rewrite ?node_9637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9639 (s : N.State) (i : N.Inputs) :
  R.v9639 (state s) (inputs i) = Zmod.unsigned (N.v9639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9639 s i)) at 1.
  unfold R.v9639, N.v9639.
  rewrite ?node_9469.
  rewrite ?node_9470.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9640 (s : N.State) (i : N.Inputs) :
  R.v9640 (state s) (inputs i) = Zmod.unsigned (N.v9640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9640 s i)) at 1.
  unfold R.v9640, N.v9640.
  rewrite ?node_9471.
  rewrite ?node_9474.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9641 (s : N.State) (i : N.Inputs) :
  R.v9641 (state s) (inputs i) = Zmod.unsigned (N.v9641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9641 s i)) at 1.
  unfold R.v9641, N.v9641.
  rewrite ?node_9639.
  rewrite ?node_9640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9642 (s : N.State) (i : N.Inputs) :
  R.v9642 (state s) (inputs i) = Zmod.unsigned (N.v9642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9642 s i)) at 1.
  unfold R.v9642, N.v9642.
  rewrite ?node_9638.
  rewrite ?node_9641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9643 (s : N.State) (i : N.Inputs) :
  R.v9643 (state s) (inputs i) = Zmod.unsigned (N.v9643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9643 s i)) at 1.
  unfold R.v9643, N.v9643.
  rewrite ?node_9483.
  rewrite ?node_9486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9644 (s : N.State) (i : N.Inputs) :
  R.v9644 (state s) (inputs i) = Zmod.unsigned (N.v9644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9644 s i)) at 1.
  unfold R.v9644, N.v9644.
  rewrite ?node_9487.
  rewrite ?node_9490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9645 (s : N.State) (i : N.Inputs) :
  R.v9645 (state s) (inputs i) = Zmod.unsigned (N.v9645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9645 s i)) at 1.
  unfold R.v9645, N.v9645.
  rewrite ?node_9643.
  rewrite ?node_9644.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9646 (s : N.State) (i : N.Inputs) :
  R.v9646 (state s) (inputs i) = Zmod.unsigned (N.v9646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9646 s i)) at 1.
  unfold R.v9646, N.v9646.
  rewrite ?node_9642.
  rewrite ?node_9645.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9647 (s : N.State) (i : N.Inputs) :
  R.v9647 (state s) (inputs i) = Zmod.unsigned (N.v9647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9647 s i)) at 1.
  unfold R.v9647, N.v9647.
  rewrite ?node_9627.
  rewrite ?node_9646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9648 (s : N.State) (i : N.Inputs) :
  R.v9648 (state s) (inputs i) = Zmod.unsigned (N.v9648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9648 s i)) at 1.
  unfold R.v9648, N.v9648.
  rewrite ?node_9458.
  rewrite ?node_9475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9649 (s : N.State) (i : N.Inputs) :
  R.v9649 (state s) (inputs i) = Zmod.unsigned (N.v9649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9649 s i)) at 1.
  unfold R.v9649, N.v9649.
  rewrite ?node_9476.
  rewrite ?node_9479.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9650 (s : N.State) (i : N.Inputs) :
  R.v9650 (state s) (inputs i) = Zmod.unsigned (N.v9650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9650 s i)) at 1.
  unfold R.v9650, N.v9650.
  rewrite ?node_9648.
  rewrite ?node_9649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9651 (s : N.State) (i : N.Inputs) :
  R.v9651 (state s) (inputs i) = Zmod.unsigned (N.v9651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9651 s i)) at 1.
  unfold R.v9651, N.v9651.
  rewrite ?node_9647.
  rewrite ?node_9650.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9652 (s : N.State) (i : N.Inputs) :
  R.v9652 (state s) (inputs i) = Zmod.unsigned (N.v9652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9652 s i)) at 1.
  unfold R.v9652, N.v9652.
  rewrite ?node_9491.
  rewrite ?node_9492.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9653 (s : N.State) (i : N.Inputs) :
  R.v9653 (state s) (inputs i) = Zmod.unsigned (N.v9653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9653 s i)) at 1.
  unfold R.v9653, N.v9653.
  rewrite ?node_9493.
  rewrite ?node_9496.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9654 (s : N.State) (i : N.Inputs) :
  R.v9654 (state s) (inputs i) = Zmod.unsigned (N.v9654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9654 s i)) at 1.
  unfold R.v9654, N.v9654.
  rewrite ?node_9652.
  rewrite ?node_9653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9655 (s : N.State) (i : N.Inputs) :
  R.v9655 (state s) (inputs i) = Zmod.unsigned (N.v9655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9655 s i)) at 1.
  unfold R.v9655, N.v9655.
  rewrite ?node_9651.
  rewrite ?node_9654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9656 (s : N.State) (i : N.Inputs) :
  R.v9656 (state s) (inputs i) = Zmod.unsigned (N.v9656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9656 s i)) at 1.
  unfold R.v9656, N.v9656.
  rewrite ?node_9480.
  rewrite ?node_9497.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9657 (s : N.State) (i : N.Inputs) :
  R.v9657 (state s) (inputs i) = Zmod.unsigned (N.v9657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9657 s i)) at 1.
  unfold R.v9657, N.v9657.
  rewrite ?node_9498.
  rewrite ?node_9501.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9658 (s : N.State) (i : N.Inputs) :
  R.v9658 (state s) (inputs i) = Zmod.unsigned (N.v9658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9658 s i)) at 1.
  unfold R.v9658, N.v9658.
  rewrite ?node_9656.
  rewrite ?node_9657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9659 (s : N.State) (i : N.Inputs) :
  R.v9659 (state s) (inputs i) = Zmod.unsigned (N.v9659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9659 s i)) at 1.
  unfold R.v9659, N.v9659.
  rewrite ?node_9655.
  rewrite ?node_9658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9660 (s : N.State) (i : N.Inputs) :
  R.v9660 (state s) (inputs i) = Zmod.unsigned (N.v9660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9660 s i)) at 1.
  unfold R.v9660, N.v9660.
  rewrite ?node_9502.
  rewrite ?node_9505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9661 (s : N.State) (i : N.Inputs) :
  R.v9661 (state s) (inputs i) = Zmod.unsigned (N.v9661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9661 s i)) at 1.
  unfold R.v9661, N.v9661.
  rewrite ?node_9506.
  rewrite ?node_9509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9662 (s : N.State) (i : N.Inputs) :
  R.v9662 (state s) (inputs i) = Zmod.unsigned (N.v9662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9662 s i)) at 1.
  unfold R.v9662, N.v9662.
  rewrite ?node_9660.
  rewrite ?node_9661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9663 (s : N.State) (i : N.Inputs) :
  R.v9663 (state s) (inputs i) = Zmod.unsigned (N.v9663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9663 s i)) at 1.
  unfold R.v9663, N.v9663.
  rewrite ?node_9659.
  rewrite ?node_9662.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9664 (s : N.State) (i : N.Inputs) :
  R.v9664 (state s) (inputs i) = Zmod.unsigned (N.v9664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9664 s i)) at 1.
  unfold R.v9664, N.v9664.
  rewrite ?node_9663.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2391_nr_5F2422.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2391_nr_5F2422 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9665 (s : N.State) (i : N.Inputs) :
  R.v9665 (state s) (inputs i) = Zmod.unsigned (N.v9665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9665 s i)) at 1.
  unfold R.v9665, N.v9665.
  rewrite ?node_9510.
  rewrite ?node_9513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9666 (s : N.State) (i : N.Inputs) :
  R.v9666 (state s) (inputs i) = Zmod.unsigned (N.v9666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9666 s i)) at 1.
  unfold R.v9666, N.v9666.
  rewrite ?node_9665.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2392_nr_5F2423.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2392_nr_5F2423 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9667 (s : N.State) (i : N.Inputs) :
  R.v9667 (state s) (inputs i) = Zmod.unsigned (N.v9667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9667 s i)) at 1.
  unfold R.v9667, N.v9667.
  rewrite !state_r990_nr_5F990.
  rewrite !state_r991_nr_5F991.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r990_nr_5F990 s)).
  rewrite ?(bits.mod_to_Z (N.r991_nr_5F991 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9668 (s : N.State) (i : N.Inputs) :
  R.v9668 (state s) (inputs i) = Zmod.unsigned (N.v9668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9668 s i)) at 1.
  unfold R.v9668, N.v9668.
  rewrite ?node_9667.
  rewrite !state_r992_nr_5F992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r992_nr_5F992 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9669 (s : N.State) (i : N.Inputs) :
  R.v9669 (state s) (inputs i) = Zmod.unsigned (N.v9669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9669 s i)) at 1.
  unfold R.v9669, N.v9669.
  rewrite ?node_9668.
  rewrite !state_r993_nr_5F993.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r993_nr_5F993 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9670 (s : N.State) (i : N.Inputs) :
  R.v9670 (state s) (inputs i) = Zmod.unsigned (N.v9670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9670 s i)) at 1.
  unfold R.v9670, N.v9670.
  rewrite !state_r959_nr_5F959.
  rewrite !state_r960_nr_5F960.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r959_nr_5F959 s)).
  rewrite ?(bits.mod_to_Z (N.r960_nr_5F960 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9671 (s : N.State) (i : N.Inputs) :
  R.v9671 (state s) (inputs i) = Zmod.unsigned (N.v9671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9671 s i)) at 1.
  unfold R.v9671, N.v9671.
  rewrite ?node_9518.
  rewrite !state_r961_nr_5F961.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r961_nr_5F961 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9672 (s : N.State) (i : N.Inputs) :
  R.v9672 (state s) (inputs i) = Zmod.unsigned (N.v9672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9672 s i)) at 1.
  unfold R.v9672, N.v9672.
  rewrite ?node_9670.
  rewrite ?node_9671.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9673 (s : N.State) (i : N.Inputs) :
  R.v9673 (state s) (inputs i) = Zmod.unsigned (N.v9673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9673 s i)) at 1.
  unfold R.v9673, N.v9673.
  rewrite ?node_9669.
  rewrite ?node_9672.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9674 (s : N.State) (i : N.Inputs) :
  R.v9674 (state s) (inputs i) = Zmod.unsigned (N.v9674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9674 s i)) at 1.
  unfold R.v9674, N.v9674.
  rewrite !state_r994_nr_5F994.
  rewrite !state_r995_nr_5F995.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r994_nr_5F994 s)).
  rewrite ?(bits.mod_to_Z (N.r995_nr_5F995 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9675 (s : N.State) (i : N.Inputs) :
  R.v9675 (state s) (inputs i) = Zmod.unsigned (N.v9675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9675 s i)) at 1.
  unfold R.v9675, N.v9675.
  rewrite ?node_9674.
  rewrite !state_r996_nr_5F996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r996_nr_5F996 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9676 (s : N.State) (i : N.Inputs) :
  R.v9676 (state s) (inputs i) = Zmod.unsigned (N.v9676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9676 s i)) at 1.
  unfold R.v9676, N.v9676.
  rewrite ?node_9675.
  rewrite !state_r997_nr_5F997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r997_nr_5F997 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9677 (s : N.State) (i : N.Inputs) :
  R.v9677 (state s) (inputs i) = Zmod.unsigned (N.v9677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9677 s i)) at 1.
  unfold R.v9677, N.v9677.
  rewrite !state_r963_nr_5F963.
  rewrite !state_r964_nr_5F964.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r963_nr_5F963 s)).
  rewrite ?(bits.mod_to_Z (N.r964_nr_5F964 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9678 (s : N.State) (i : N.Inputs) :
  R.v9678 (state s) (inputs i) = Zmod.unsigned (N.v9678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9678 s i)) at 1.
  unfold R.v9678, N.v9678.
  rewrite ?node_9525.
  rewrite !state_r965_nr_5F965.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r965_nr_5F965 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9679 (s : N.State) (i : N.Inputs) :
  R.v9679 (state s) (inputs i) = Zmod.unsigned (N.v9679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9679 s i)) at 1.
  unfold R.v9679, N.v9679.
  rewrite ?node_9677.
  rewrite ?node_9678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9680 (s : N.State) (i : N.Inputs) :
  R.v9680 (state s) (inputs i) = Zmod.unsigned (N.v9680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9680 s i)) at 1.
  unfold R.v9680, N.v9680.
  rewrite ?node_9676.
  rewrite ?node_9679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9681 (s : N.State) (i : N.Inputs) :
  R.v9681 (state s) (inputs i) = Zmod.unsigned (N.v9681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9681 s i)) at 1.
  unfold R.v9681, N.v9681.
  rewrite ?node_9673.
  rewrite ?node_9680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9682 (s : N.State) (i : N.Inputs) :
  R.v9682 (state s) (inputs i) = Zmod.unsigned (N.v9682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9682 s i)) at 1.
  unfold R.v9682, N.v9682.
  rewrite !state_r998_nr_5F998.
  rewrite !state_r999_nr_5F999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r998_nr_5F998 s)).
  rewrite ?(bits.mod_to_Z (N.r999_nr_5F999 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9683 (s : N.State) (i : N.Inputs) :
  R.v9683 (state s) (inputs i) = Zmod.unsigned (N.v9683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9683 s i)) at 1.
  unfold R.v9683, N.v9683.
  rewrite ?node_9682.
  rewrite !state_r1000_nr_5F1000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1000_nr_5F1000 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9684 (s : N.State) (i : N.Inputs) :
  R.v9684 (state s) (inputs i) = Zmod.unsigned (N.v9684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9684 s i)) at 1.
  unfold R.v9684, N.v9684.
  rewrite ?node_9683.
  rewrite !state_r1001_nr_5F1001.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1001_nr_5F1001 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9685 (s : N.State) (i : N.Inputs) :
  R.v9685 (state s) (inputs i) = Zmod.unsigned (N.v9685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9685 s i)) at 1.
  unfold R.v9685, N.v9685.
  rewrite !state_r967_nr_5F967.
  rewrite !state_r968_nr_5F968.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r967_nr_5F967 s)).
  rewrite ?(bits.mod_to_Z (N.r968_nr_5F968 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9686 (s : N.State) (i : N.Inputs) :
  R.v9686 (state s) (inputs i) = Zmod.unsigned (N.v9686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9686 s i)) at 1.
  unfold R.v9686, N.v9686.
  rewrite ?node_9533.
  rewrite !state_r969_nr_5F969.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r969_nr_5F969 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9687 (s : N.State) (i : N.Inputs) :
  R.v9687 (state s) (inputs i) = Zmod.unsigned (N.v9687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9687 s i)) at 1.
  unfold R.v9687, N.v9687.
  rewrite ?node_9685.
  rewrite ?node_9686.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9688 (s : N.State) (i : N.Inputs) :
  R.v9688 (state s) (inputs i) = Zmod.unsigned (N.v9688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9688 s i)) at 1.
  unfold R.v9688, N.v9688.
  rewrite ?node_9684.
  rewrite ?node_9687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9689 (s : N.State) (i : N.Inputs) :
  R.v9689 (state s) (inputs i) = Zmod.unsigned (N.v9689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9689 s i)) at 1.
  unfold R.v9689, N.v9689.
  rewrite ?node_9681.
  rewrite ?node_9688.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9690 (s : N.State) (i : N.Inputs) :
  R.v9690 (state s) (inputs i) = Zmod.unsigned (N.v9690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9690 s i)) at 1.
  unfold R.v9690, N.v9690.
  rewrite !state_r1002_nr_5F1002.
  rewrite !state_r1003_nr_5F1003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1002_nr_5F1002 s)).
  rewrite ?(bits.mod_to_Z (N.r1003_nr_5F1003 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9691 (s : N.State) (i : N.Inputs) :
  R.v9691 (state s) (inputs i) = Zmod.unsigned (N.v9691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9691 s i)) at 1.
  unfold R.v9691, N.v9691.
  rewrite ?node_9690.
  rewrite !state_r1004_nr_5F1004.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1004_nr_5F1004 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9692 (s : N.State) (i : N.Inputs) :
  R.v9692 (state s) (inputs i) = Zmod.unsigned (N.v9692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9692 s i)) at 1.
  unfold R.v9692, N.v9692.
  rewrite ?node_9691.
  rewrite !state_r1005_nr_5F1005.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1005_nr_5F1005 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9693 (s : N.State) (i : N.Inputs) :
  R.v9693 (state s) (inputs i) = Zmod.unsigned (N.v9693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9693 s i)) at 1.
  unfold R.v9693, N.v9693.
  rewrite !state_r971_nr_5F971.
  rewrite !state_r972_nr_5F972.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r971_nr_5F971 s)).
  rewrite ?(bits.mod_to_Z (N.r972_nr_5F972 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9694 (s : N.State) (i : N.Inputs) :
  R.v9694 (state s) (inputs i) = Zmod.unsigned (N.v9694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9694 s i)) at 1.
  unfold R.v9694, N.v9694.
  rewrite ?node_9541.
  rewrite !state_r973_nr_5F973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r973_nr_5F973 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9695 (s : N.State) (i : N.Inputs) :
  R.v9695 (state s) (inputs i) = Zmod.unsigned (N.v9695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9695 s i)) at 1.
  unfold R.v9695, N.v9695.
  rewrite ?node_9693.
  rewrite ?node_9694.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9696 (s : N.State) (i : N.Inputs) :
  R.v9696 (state s) (inputs i) = Zmod.unsigned (N.v9696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9696 s i)) at 1.
  unfold R.v9696, N.v9696.
  rewrite ?node_9692.
  rewrite ?node_9695.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9697 (s : N.State) (i : N.Inputs) :
  R.v9697 (state s) (inputs i) = Zmod.unsigned (N.v9697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9697 s i)) at 1.
  unfold R.v9697, N.v9697.
  rewrite ?node_9689.
  rewrite ?node_9696.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9698 (s : N.State) (i : N.Inputs) :
  R.v9698 (state s) (inputs i) = Zmod.unsigned (N.v9698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9698 s i)) at 1.
  unfold R.v9698, N.v9698.
  rewrite ?node_9524.
  rewrite ?node_9531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9699 (s : N.State) (i : N.Inputs) :
  R.v9699 (state s) (inputs i) = Zmod.unsigned (N.v9699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9699 s i)) at 1.
  unfold R.v9699, N.v9699.
  rewrite ?node_9532.
  rewrite ?node_9539.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9700 (s : N.State) (i : N.Inputs) :
  R.v9700 (state s) (inputs i) = Zmod.unsigned (N.v9700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9700 s i)) at 1.
  unfold R.v9700, N.v9700.
  rewrite ?node_9698.
  rewrite ?node_9699.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9701 (s : N.State) (i : N.Inputs) :
  R.v9701 (state s) (inputs i) = Zmod.unsigned (N.v9701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9701 s i)) at 1.
  unfold R.v9701, N.v9701.
  rewrite ?node_9697.
  rewrite ?node_9700.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9702 (s : N.State) (i : N.Inputs) :
  R.v9702 (state s) (inputs i) = Zmod.unsigned (N.v9702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9702 s i)) at 1.
  unfold R.v9702, N.v9702.
  rewrite !state_r1006_nr_5F1006.
  rewrite !state_r1007_nr_5F1007.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1006_nr_5F1006 s)).
  rewrite ?(bits.mod_to_Z (N.r1007_nr_5F1007 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9703 (s : N.State) (i : N.Inputs) :
  R.v9703 (state s) (inputs i) = Zmod.unsigned (N.v9703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9703 s i)) at 1.
  unfold R.v9703, N.v9703.
  rewrite ?node_9702.
  rewrite !state_r1008_nr_5F1008.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1008_nr_5F1008 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9704 (s : N.State) (i : N.Inputs) :
  R.v9704 (state s) (inputs i) = Zmod.unsigned (N.v9704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9704 s i)) at 1.
  unfold R.v9704, N.v9704.
  rewrite ?node_9703.
  rewrite !state_r1009_nr_5F1009.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1009_nr_5F1009 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9705 (s : N.State) (i : N.Inputs) :
  R.v9705 (state s) (inputs i) = Zmod.unsigned (N.v9705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9705 s i)) at 1.
  unfold R.v9705, N.v9705.
  rewrite !state_r975_nr_5F975.
  rewrite !state_r976_nr_5F976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r975_nr_5F975 s)).
  rewrite ?(bits.mod_to_Z (N.r976_nr_5F976 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9706 (s : N.State) (i : N.Inputs) :
  R.v9706 (state s) (inputs i) = Zmod.unsigned (N.v9706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9706 s i)) at 1.
  unfold R.v9706, N.v9706.
  rewrite ?node_9553.
  rewrite !state_r977_nr_5F977.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r977_nr_5F977 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9707 (s : N.State) (i : N.Inputs) :
  R.v9707 (state s) (inputs i) = Zmod.unsigned (N.v9707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9707 s i)) at 1.
  unfold R.v9707, N.v9707.
  rewrite ?node_9705.
  rewrite ?node_9706.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9708 (s : N.State) (i : N.Inputs) :
  R.v9708 (state s) (inputs i) = Zmod.unsigned (N.v9708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9708 s i)) at 1.
  unfold R.v9708, N.v9708.
  rewrite ?node_9704.
  rewrite ?node_9707.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9709 (s : N.State) (i : N.Inputs) :
  R.v9709 (state s) (inputs i) = Zmod.unsigned (N.v9709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9709 s i)) at 1.
  unfold R.v9709, N.v9709.
  rewrite !state_r1010_nr_5F1010.
  rewrite !state_r1011_nr_5F1011.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1010_nr_5F1010 s)).
  rewrite ?(bits.mod_to_Z (N.r1011_nr_5F1011 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9710 (s : N.State) (i : N.Inputs) :
  R.v9710 (state s) (inputs i) = Zmod.unsigned (N.v9710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9710 s i)) at 1.
  unfold R.v9710, N.v9710.
  rewrite ?node_9709.
  rewrite !state_r1012_nr_5F1012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1012_nr_5F1012 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9711 (s : N.State) (i : N.Inputs) :
  R.v9711 (state s) (inputs i) = Zmod.unsigned (N.v9711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9711 s i)) at 1.
  unfold R.v9711, N.v9711.
  rewrite ?node_9710.
  rewrite !state_r1013_nr_5F1013.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1013_nr_5F1013 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9712 (s : N.State) (i : N.Inputs) :
  R.v9712 (state s) (inputs i) = Zmod.unsigned (N.v9712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9712 s i)) at 1.
  unfold R.v9712, N.v9712.
  rewrite !state_r979_nr_5F979.
  rewrite !state_r980_nr_5F980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r979_nr_5F979 s)).
  rewrite ?(bits.mod_to_Z (N.r980_nr_5F980 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9713 (s : N.State) (i : N.Inputs) :
  R.v9713 (state s) (inputs i) = Zmod.unsigned (N.v9713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9713 s i)) at 1.
  unfold R.v9713, N.v9713.
  rewrite ?node_9560.
  rewrite !state_r981_nr_5F981.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r981_nr_5F981 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9714 (s : N.State) (i : N.Inputs) :
  R.v9714 (state s) (inputs i) = Zmod.unsigned (N.v9714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9714 s i)) at 1.
  unfold R.v9714, N.v9714.
  rewrite ?node_9712.
  rewrite ?node_9713.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9715 (s : N.State) (i : N.Inputs) :
  R.v9715 (state s) (inputs i) = Zmod.unsigned (N.v9715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9715 s i)) at 1.
  unfold R.v9715, N.v9715.
  rewrite ?node_9711.
  rewrite ?node_9714.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9716 (s : N.State) (i : N.Inputs) :
  R.v9716 (state s) (inputs i) = Zmod.unsigned (N.v9716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9716 s i)) at 1.
  unfold R.v9716, N.v9716.
  rewrite ?node_9708.
  rewrite ?node_9715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9717 (s : N.State) (i : N.Inputs) :
  R.v9717 (state s) (inputs i) = Zmod.unsigned (N.v9717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9717 s i)) at 1.
  unfold R.v9717, N.v9717.
  rewrite !state_r1014_nr_5F1014.
  rewrite !state_r1015_nr_5F1015.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1014_nr_5F1014 s)).
  rewrite ?(bits.mod_to_Z (N.r1015_nr_5F1015 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9718 (s : N.State) (i : N.Inputs) :
  R.v9718 (state s) (inputs i) = Zmod.unsigned (N.v9718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9718 s i)) at 1.
  unfold R.v9718, N.v9718.
  rewrite ?node_9717.
  rewrite !state_r1016_nr_5F1016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1016_nr_5F1016 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9719 (s : N.State) (i : N.Inputs) :
  R.v9719 (state s) (inputs i) = Zmod.unsigned (N.v9719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9719 s i)) at 1.
  unfold R.v9719, N.v9719.
  rewrite ?node_9718.
  rewrite !state_r1017_nr_5F1017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1017_nr_5F1017 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9720 (s : N.State) (i : N.Inputs) :
  R.v9720 (state s) (inputs i) = Zmod.unsigned (N.v9720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9720 s i)) at 1.
  unfold R.v9720, N.v9720.
  rewrite !state_r983_nr_5F983.
  rewrite !state_r984_nr_5F984.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r983_nr_5F983 s)).
  rewrite ?(bits.mod_to_Z (N.r984_nr_5F984 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9721 (s : N.State) (i : N.Inputs) :
  R.v9721 (state s) (inputs i) = Zmod.unsigned (N.v9721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9721 s i)) at 1.
  unfold R.v9721, N.v9721.
  rewrite ?node_9568.
  rewrite !state_r985_nr_5F985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r985_nr_5F985 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9722 (s : N.State) (i : N.Inputs) :
  R.v9722 (state s) (inputs i) = Zmod.unsigned (N.v9722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9722 s i)) at 1.
  unfold R.v9722, N.v9722.
  rewrite ?node_9720.
  rewrite ?node_9721.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9723 (s : N.State) (i : N.Inputs) :
  R.v9723 (state s) (inputs i) = Zmod.unsigned (N.v9723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9723 s i)) at 1.
  unfold R.v9723, N.v9723.
  rewrite ?node_9719.
  rewrite ?node_9722.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9724 (s : N.State) (i : N.Inputs) :
  R.v9724 (state s) (inputs i) = Zmod.unsigned (N.v9724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9724 s i)) at 1.
  unfold R.v9724, N.v9724.
  rewrite ?node_9716.
  rewrite ?node_9723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9725 (s : N.State) (i : N.Inputs) :
  R.v9725 (state s) (inputs i) = Zmod.unsigned (N.v9725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9725 s i)) at 1.
  unfold R.v9725, N.v9725.
  rewrite !state_r1018_nr_5F1018.
  rewrite !state_r1019_nr_5F1019.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1018_nr_5F1018 s)).
  rewrite ?(bits.mod_to_Z (N.r1019_nr_5F1019 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9726 (s : N.State) (i : N.Inputs) :
  R.v9726 (state s) (inputs i) = Zmod.unsigned (N.v9726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9726 s i)) at 1.
  unfold R.v9726, N.v9726.
  rewrite ?node_9725.
  rewrite !state_r1020_nr_5F1020.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1020_nr_5F1020 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9727 (s : N.State) (i : N.Inputs) :
  R.v9727 (state s) (inputs i) = Zmod.unsigned (N.v9727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9727 s i)) at 1.
  unfold R.v9727, N.v9727.
  rewrite ?node_9726.
  rewrite !state_r1021_nr_5F1021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1021_nr_5F1021 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9728 (s : N.State) (i : N.Inputs) :
  R.v9728 (state s) (inputs i) = Zmod.unsigned (N.v9728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9728 s i)) at 1.
  unfold R.v9728, N.v9728.
  rewrite ?node_9724.
  rewrite ?node_9727.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9729 (s : N.State) (i : N.Inputs) :
  R.v9729 (state s) (inputs i) = Zmod.unsigned (N.v9729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9729 s i)) at 1.
  unfold R.v9729, N.v9729.
  rewrite ?node_9559.
  rewrite ?node_9566.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9730 (s : N.State) (i : N.Inputs) :
  R.v9730 (state s) (inputs i) = Zmod.unsigned (N.v9730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9730 s i)) at 1.
  unfold R.v9730, N.v9730.
  rewrite ?node_9567.
  rewrite ?node_9574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9731 (s : N.State) (i : N.Inputs) :
  R.v9731 (state s) (inputs i) = Zmod.unsigned (N.v9731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9731 s i)) at 1.
  unfold R.v9731, N.v9731.
  rewrite ?node_9729.
  rewrite ?node_9730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9732 (s : N.State) (i : N.Inputs) :
  R.v9732 (state s) (inputs i) = Zmod.unsigned (N.v9732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9732 s i)) at 1.
  unfold R.v9732, N.v9732.
  rewrite ?node_9728.
  rewrite ?node_9731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9733 (s : N.State) (i : N.Inputs) :
  R.v9733 (state s) (inputs i) = Zmod.unsigned (N.v9733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9733 s i)) at 1.
  unfold R.v9733, N.v9733.
  rewrite ?node_9701.
  rewrite ?node_9732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9734 (s : N.State) (i : N.Inputs) :
  R.v9734 (state s) (inputs i) = Zmod.unsigned (N.v9734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9734 s i)) at 1.
  unfold R.v9734, N.v9734.
  rewrite ?node_9519.
  rewrite !state_r962_nr_5F962.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r962_nr_5F962 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9735 (s : N.State) (i : N.Inputs) :
  R.v9735 (state s) (inputs i) = Zmod.unsigned (N.v9735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9735 s i)) at 1.
  unfold R.v9735, N.v9735.
  rewrite ?node_9520.
  rewrite ?node_9523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9736 (s : N.State) (i : N.Inputs) :
  R.v9736 (state s) (inputs i) = Zmod.unsigned (N.v9736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9736 s i)) at 1.
  unfold R.v9736, N.v9736.
  rewrite ?node_9734.
  rewrite ?node_9735.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9737 (s : N.State) (i : N.Inputs) :
  R.v9737 (state s) (inputs i) = Zmod.unsigned (N.v9737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9737 s i)) at 1.
  unfold R.v9737, N.v9737.
  rewrite ?node_9526.
  rewrite !state_r966_nr_5F966.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r966_nr_5F966 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9738 (s : N.State) (i : N.Inputs) :
  R.v9738 (state s) (inputs i) = Zmod.unsigned (N.v9738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9738 s i)) at 1.
  unfold R.v9738, N.v9738.
  rewrite ?node_9527.
  rewrite ?node_9530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9739 (s : N.State) (i : N.Inputs) :
  R.v9739 (state s) (inputs i) = Zmod.unsigned (N.v9739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9739 s i)) at 1.
  unfold R.v9739, N.v9739.
  rewrite ?node_9737.
  rewrite ?node_9738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9740 (s : N.State) (i : N.Inputs) :
  R.v9740 (state s) (inputs i) = Zmod.unsigned (N.v9740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9740 s i)) at 1.
  unfold R.v9740, N.v9740.
  rewrite ?node_9736.
  rewrite ?node_9739.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9741 (s : N.State) (i : N.Inputs) :
  R.v9741 (state s) (inputs i) = Zmod.unsigned (N.v9741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9741 s i)) at 1.
  unfold R.v9741, N.v9741.
  rewrite ?node_9534.
  rewrite !state_r970_nr_5F970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r970_nr_5F970 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9742 (s : N.State) (i : N.Inputs) :
  R.v9742 (state s) (inputs i) = Zmod.unsigned (N.v9742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9742 s i)) at 1.
  unfold R.v9742, N.v9742.
  rewrite ?node_9535.
  rewrite ?node_9538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9743 (s : N.State) (i : N.Inputs) :
  R.v9743 (state s) (inputs i) = Zmod.unsigned (N.v9743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9743 s i)) at 1.
  unfold R.v9743, N.v9743.
  rewrite ?node_9741.
  rewrite ?node_9742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9744 (s : N.State) (i : N.Inputs) :
  R.v9744 (state s) (inputs i) = Zmod.unsigned (N.v9744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9744 s i)) at 1.
  unfold R.v9744, N.v9744.
  rewrite ?node_9740.
  rewrite ?node_9743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9745 (s : N.State) (i : N.Inputs) :
  R.v9745 (state s) (inputs i) = Zmod.unsigned (N.v9745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9745 s i)) at 1.
  unfold R.v9745, N.v9745.
  rewrite ?node_9542.
  rewrite !state_r974_nr_5F974.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r974_nr_5F974 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9746 (s : N.State) (i : N.Inputs) :
  R.v9746 (state s) (inputs i) = Zmod.unsigned (N.v9746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9746 s i)) at 1.
  unfold R.v9746, N.v9746.
  rewrite ?node_9543.
  rewrite ?node_9546.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9747 (s : N.State) (i : N.Inputs) :
  R.v9747 (state s) (inputs i) = Zmod.unsigned (N.v9747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9747 s i)) at 1.
  unfold R.v9747, N.v9747.
  rewrite ?node_9745.
  rewrite ?node_9746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9748 (s : N.State) (i : N.Inputs) :
  R.v9748 (state s) (inputs i) = Zmod.unsigned (N.v9748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9748 s i)) at 1.
  unfold R.v9748, N.v9748.
  rewrite ?node_9744.
  rewrite ?node_9747.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9749 (s : N.State) (i : N.Inputs) :
  R.v9749 (state s) (inputs i) = Zmod.unsigned (N.v9749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9749 s i)) at 1.
  unfold R.v9749, N.v9749.
  rewrite ?node_9586.
  rewrite ?node_9589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9750 (s : N.State) (i : N.Inputs) :
  R.v9750 (state s) (inputs i) = Zmod.unsigned (N.v9750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9750 s i)) at 1.
  unfold R.v9750, N.v9750.
  rewrite ?node_9590.
  rewrite ?node_9593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9751 (s : N.State) (i : N.Inputs) :
  R.v9751 (state s) (inputs i) = Zmod.unsigned (N.v9751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9751 s i)) at 1.
  unfold R.v9751, N.v9751.
  rewrite ?node_9749.
  rewrite ?node_9750.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9752 (s : N.State) (i : N.Inputs) :
  R.v9752 (state s) (inputs i) = Zmod.unsigned (N.v9752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9752 s i)) at 1.
  unfold R.v9752, N.v9752.
  rewrite ?node_9748.
  rewrite ?node_9751.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9753 (s : N.State) (i : N.Inputs) :
  R.v9753 (state s) (inputs i) = Zmod.unsigned (N.v9753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9753 s i)) at 1.
  unfold R.v9753, N.v9753.
  rewrite ?node_9733.
  rewrite ?node_9752.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9754 (s : N.State) (i : N.Inputs) :
  R.v9754 (state s) (inputs i) = Zmod.unsigned (N.v9754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9754 s i)) at 1.
  unfold R.v9754, N.v9754.
  rewrite ?node_9554.
  rewrite !state_r978_nr_5F978.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r978_nr_5F978 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9755 (s : N.State) (i : N.Inputs) :
  R.v9755 (state s) (inputs i) = Zmod.unsigned (N.v9755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9755 s i)) at 1.
  unfold R.v9755, N.v9755.
  rewrite ?node_9555.
  rewrite ?node_9558.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9756 (s : N.State) (i : N.Inputs) :
  R.v9756 (state s) (inputs i) = Zmod.unsigned (N.v9756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9756 s i)) at 1.
  unfold R.v9756, N.v9756.
  rewrite ?node_9754.
  rewrite ?node_9755.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9757 (s : N.State) (i : N.Inputs) :
  R.v9757 (state s) (inputs i) = Zmod.unsigned (N.v9757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9757 s i)) at 1.
  unfold R.v9757, N.v9757.
  rewrite ?node_9561.
  rewrite !state_r982_nr_5F982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r982_nr_5F982 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9758 (s : N.State) (i : N.Inputs) :
  R.v9758 (state s) (inputs i) = Zmod.unsigned (N.v9758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9758 s i)) at 1.
  unfold R.v9758, N.v9758.
  rewrite ?node_9562.
  rewrite ?node_9565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9759 (s : N.State) (i : N.Inputs) :
  R.v9759 (state s) (inputs i) = Zmod.unsigned (N.v9759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9759 s i)) at 1.
  unfold R.v9759, N.v9759.
  rewrite ?node_9757.
  rewrite ?node_9758.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9760 (s : N.State) (i : N.Inputs) :
  R.v9760 (state s) (inputs i) = Zmod.unsigned (N.v9760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9760 s i)) at 1.
  unfold R.v9760, N.v9760.
  rewrite ?node_9756.
  rewrite ?node_9759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9761 (s : N.State) (i : N.Inputs) :
  R.v9761 (state s) (inputs i) = Zmod.unsigned (N.v9761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9761 s i)) at 1.
  unfold R.v9761, N.v9761.
  rewrite ?node_9569.
  rewrite !state_r986_nr_5F986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r986_nr_5F986 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9762 (s : N.State) (i : N.Inputs) :
  R.v9762 (state s) (inputs i) = Zmod.unsigned (N.v9762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9762 s i)) at 1.
  unfold R.v9762, N.v9762.
  rewrite ?node_9570.
  rewrite ?node_9573.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9763 (s : N.State) (i : N.Inputs) :
  R.v9763 (state s) (inputs i) = Zmod.unsigned (N.v9763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9763 s i)) at 1.
  unfold R.v9763, N.v9763.
  rewrite ?node_9761.
  rewrite ?node_9762.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9764 (s : N.State) (i : N.Inputs) :
  R.v9764 (state s) (inputs i) = Zmod.unsigned (N.v9764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9764 s i)) at 1.
  unfold R.v9764, N.v9764.
  rewrite ?node_9760.
  rewrite ?node_9763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9765 (s : N.State) (i : N.Inputs) :
  R.v9765 (state s) (inputs i) = Zmod.unsigned (N.v9765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9765 s i)) at 1.
  unfold R.v9765, N.v9765.
  rewrite !state_r987_nr_5F987.
  rewrite !state_r988_nr_5F988.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r987_nr_5F987 s)).
  rewrite ?(bits.mod_to_Z (N.r988_nr_5F988 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9766 (s : N.State) (i : N.Inputs) :
  R.v9766 (state s) (inputs i) = Zmod.unsigned (N.v9766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9766 s i)) at 1.
  unfold R.v9766, N.v9766.
  rewrite ?node_9576.
  rewrite !state_r989_nr_5F989.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r989_nr_5F989 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9767 (s : N.State) (i : N.Inputs) :
  R.v9767 (state s) (inputs i) = Zmod.unsigned (N.v9767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9767 s i)) at 1.
  unfold R.v9767, N.v9767.
  rewrite ?node_9765.
  rewrite ?node_9766.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9768 (s : N.State) (i : N.Inputs) :
  R.v9768 (state s) (inputs i) = Zmod.unsigned (N.v9768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9768 s i)) at 1.
  unfold R.v9768, N.v9768.
  rewrite ?node_9764.
  rewrite ?node_9767.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9769 (s : N.State) (i : N.Inputs) :
  R.v9769 (state s) (inputs i) = Zmod.unsigned (N.v9769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9769 s i)) at 1.
  unfold R.v9769, N.v9769.
  rewrite ?node_9606.
  rewrite ?node_9609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9770 (s : N.State) (i : N.Inputs) :
  R.v9770 (state s) (inputs i) = Zmod.unsigned (N.v9770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9770 s i)) at 1.
  unfold R.v9770, N.v9770.
  rewrite ?node_9610.
  rewrite ?node_9613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9771 (s : N.State) (i : N.Inputs) :
  R.v9771 (state s) (inputs i) = Zmod.unsigned (N.v9771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9771 s i)) at 1.
  unfold R.v9771, N.v9771.
  rewrite ?node_9769.
  rewrite ?node_9770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9772 (s : N.State) (i : N.Inputs) :
  R.v9772 (state s) (inputs i) = Zmod.unsigned (N.v9772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9772 s i)) at 1.
  unfold R.v9772, N.v9772.
  rewrite ?node_9768.
  rewrite ?node_9771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9773 (s : N.State) (i : N.Inputs) :
  R.v9773 (state s) (inputs i) = Zmod.unsigned (N.v9773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9773 s i)) at 1.
  unfold R.v9773, N.v9773.
  rewrite ?node_9753.
  rewrite ?node_9772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9774 (s : N.State) (i : N.Inputs) :
  R.v9774 (state s) (inputs i) = Zmod.unsigned (N.v9774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9774 s i)) at 1.
  unfold R.v9774, N.v9774.
  rewrite ?node_9552.
  rewrite ?node_9582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9775 (s : N.State) (i : N.Inputs) :
  R.v9775 (state s) (inputs i) = Zmod.unsigned (N.v9775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9775 s i)) at 1.
  unfold R.v9775, N.v9775.
  rewrite ?node_9583.
  rewrite ?node_9602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9776 (s : N.State) (i : N.Inputs) :
  R.v9776 (state s) (inputs i) = Zmod.unsigned (N.v9776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9776 s i)) at 1.
  unfold R.v9776, N.v9776.
  rewrite ?node_9774.
  rewrite ?node_9775.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9777 (s : N.State) (i : N.Inputs) :
  R.v9777 (state s) (inputs i) = Zmod.unsigned (N.v9777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9777 s i)) at 1.
  unfold R.v9777, N.v9777.
  rewrite ?node_9773.
  rewrite ?node_9776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9778 (s : N.State) (i : N.Inputs) :
  R.v9778 (state s) (inputs i) = Zmod.unsigned (N.v9778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9778 s i)) at 1.
  unfold R.v9778, N.v9778.
  rewrite ?node_9540.
  rewrite ?node_9547.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9779 (s : N.State) (i : N.Inputs) :
  R.v9779 (state s) (inputs i) = Zmod.unsigned (N.v9779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9779 s i)) at 1.
  unfold R.v9779, N.v9779.
  rewrite ?node_9548.
  rewrite ?node_9551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9780 (s : N.State) (i : N.Inputs) :
  R.v9780 (state s) (inputs i) = Zmod.unsigned (N.v9780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9780 s i)) at 1.
  unfold R.v9780, N.v9780.
  rewrite ?node_9778.
  rewrite ?node_9779.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9781 (s : N.State) (i : N.Inputs) :
  R.v9781 (state s) (inputs i) = Zmod.unsigned (N.v9781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9781 s i)) at 1.
  unfold R.v9781, N.v9781.
  rewrite ?node_9575.
  rewrite ?node_9577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9782 (s : N.State) (i : N.Inputs) :
  R.v9782 (state s) (inputs i) = Zmod.unsigned (N.v9782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9782 s i)) at 1.
  unfold R.v9782, N.v9782.
  rewrite ?node_9578.
  rewrite ?node_9581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9783 (s : N.State) (i : N.Inputs) :
  R.v9783 (state s) (inputs i) = Zmod.unsigned (N.v9783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9783 s i)) at 1.
  unfold R.v9783, N.v9783.
  rewrite ?node_9781.
  rewrite ?node_9782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9784 (s : N.State) (i : N.Inputs) :
  R.v9784 (state s) (inputs i) = Zmod.unsigned (N.v9784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9784 s i)) at 1.
  unfold R.v9784, N.v9784.
  rewrite ?node_9780.
  rewrite ?node_9783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9785 (s : N.State) (i : N.Inputs) :
  R.v9785 (state s) (inputs i) = Zmod.unsigned (N.v9785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9785 s i)) at 1.
  unfold R.v9785, N.v9785.
  rewrite ?node_9594.
  rewrite ?node_9597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9786 (s : N.State) (i : N.Inputs) :
  R.v9786 (state s) (inputs i) = Zmod.unsigned (N.v9786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9786 s i)) at 1.
  unfold R.v9786, N.v9786.
  rewrite ?node_9598.
  rewrite ?node_9601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9787 (s : N.State) (i : N.Inputs) :
  R.v9787 (state s) (inputs i) = Zmod.unsigned (N.v9787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9787 s i)) at 1.
  unfold R.v9787, N.v9787.
  rewrite ?node_9785.
  rewrite ?node_9786.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9788 (s : N.State) (i : N.Inputs) :
  R.v9788 (state s) (inputs i) = Zmod.unsigned (N.v9788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9788 s i)) at 1.
  unfold R.v9788, N.v9788.
  rewrite ?node_9784.
  rewrite ?node_9787.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9789 (s : N.State) (i : N.Inputs) :
  R.v9789 (state s) (inputs i) = Zmod.unsigned (N.v9789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9789 s i)) at 1.
  unfold R.v9789, N.v9789.
  rewrite ?node_9614.
  rewrite ?node_9617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9790 (s : N.State) (i : N.Inputs) :
  R.v9790 (state s) (inputs i) = Zmod.unsigned (N.v9790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9790 s i)) at 1.
  unfold R.v9790, N.v9790.
  rewrite ?node_9618.
  rewrite ?node_9621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9791 (s : N.State) (i : N.Inputs) :
  R.v9791 (state s) (inputs i) = Zmod.unsigned (N.v9791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9791 s i)) at 1.
  unfold R.v9791, N.v9791.
  rewrite ?node_9789.
  rewrite ?node_9790.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9792 (s : N.State) (i : N.Inputs) :
  R.v9792 (state s) (inputs i) = Zmod.unsigned (N.v9792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9792 s i)) at 1.
  unfold R.v9792, N.v9792.
  rewrite ?node_9788.
  rewrite ?node_9791.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9793 (s : N.State) (i : N.Inputs) :
  R.v9793 (state s) (inputs i) = Zmod.unsigned (N.v9793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9793 s i)) at 1.
  unfold R.v9793, N.v9793.
  rewrite ?node_9630.
  rewrite ?node_9633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9794 (s : N.State) (i : N.Inputs) :
  R.v9794 (state s) (inputs i) = Zmod.unsigned (N.v9794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9794 s i)) at 1.
  unfold R.v9794, N.v9794.
  rewrite ?node_9634.
  rewrite ?node_9637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9795 (s : N.State) (i : N.Inputs) :
  R.v9795 (state s) (inputs i) = Zmod.unsigned (N.v9795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9795 s i)) at 1.
  unfold R.v9795, N.v9795.
  rewrite ?node_9793.
  rewrite ?node_9794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9796 (s : N.State) (i : N.Inputs) :
  R.v9796 (state s) (inputs i) = Zmod.unsigned (N.v9796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9796 s i)) at 1.
  unfold R.v9796, N.v9796.
  rewrite ?node_9792.
  rewrite ?node_9795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9797 (s : N.State) (i : N.Inputs) :
  R.v9797 (state s) (inputs i) = Zmod.unsigned (N.v9797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9797 s i)) at 1.
  unfold R.v9797, N.v9797.
  rewrite ?node_9777.
  rewrite ?node_9796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9798 (s : N.State) (i : N.Inputs) :
  R.v9798 (state s) (inputs i) = Zmod.unsigned (N.v9798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9798 s i)) at 1.
  unfold R.v9798, N.v9798.
  rewrite ?node_9603.
  rewrite ?node_9622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9799 (s : N.State) (i : N.Inputs) :
  R.v9799 (state s) (inputs i) = Zmod.unsigned (N.v9799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9799 s i)) at 1.
  unfold R.v9799, N.v9799.
  rewrite ?node_9623.
  rewrite ?node_9626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9800 (s : N.State) (i : N.Inputs) :
  R.v9800 (state s) (inputs i) = Zmod.unsigned (N.v9800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9800 s i)) at 1.
  unfold R.v9800, N.v9800.
  rewrite ?node_9798.
  rewrite ?node_9799.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9801 (s : N.State) (i : N.Inputs) :
  R.v9801 (state s) (inputs i) = Zmod.unsigned (N.v9801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9801 s i)) at 1.
  unfold R.v9801, N.v9801.
  rewrite ?node_9797.
  rewrite ?node_9800.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9802 (s : N.State) (i : N.Inputs) :
  R.v9802 (state s) (inputs i) = Zmod.unsigned (N.v9802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9802 s i)) at 1.
  unfold R.v9802, N.v9802.
  rewrite ?node_9638.
  rewrite ?node_9641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9803 (s : N.State) (i : N.Inputs) :
  R.v9803 (state s) (inputs i) = Zmod.unsigned (N.v9803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9803 s i)) at 1.
  unfold R.v9803, N.v9803.
  rewrite ?node_9642.
  rewrite ?node_9645.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9804 (s : N.State) (i : N.Inputs) :
  R.v9804 (state s) (inputs i) = Zmod.unsigned (N.v9804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9804 s i)) at 1.
  unfold R.v9804, N.v9804.
  rewrite ?node_9802.
  rewrite ?node_9803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9805 (s : N.State) (i : N.Inputs) :
  R.v9805 (state s) (inputs i) = Zmod.unsigned (N.v9805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9805 s i)) at 1.
  unfold R.v9805, N.v9805.
  rewrite ?node_9801.
  rewrite ?node_9804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9806 (s : N.State) (i : N.Inputs) :
  R.v9806 (state s) (inputs i) = Zmod.unsigned (N.v9806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9806 s i)) at 1.
  unfold R.v9806, N.v9806.
  rewrite ?node_9627.
  rewrite ?node_9646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9807 (s : N.State) (i : N.Inputs) :
  R.v9807 (state s) (inputs i) = Zmod.unsigned (N.v9807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9807 s i)) at 1.
  unfold R.v9807, N.v9807.
  rewrite ?node_9647.
  rewrite ?node_9650.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9808 (s : N.State) (i : N.Inputs) :
  R.v9808 (state s) (inputs i) = Zmod.unsigned (N.v9808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9808 s i)) at 1.
  unfold R.v9808, N.v9808.
  rewrite ?node_9806.
  rewrite ?node_9807.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9809 (s : N.State) (i : N.Inputs) :
  R.v9809 (state s) (inputs i) = Zmod.unsigned (N.v9809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9809 s i)) at 1.
  unfold R.v9809, N.v9809.
  rewrite ?node_9805.
  rewrite ?node_9808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9810 (s : N.State) (i : N.Inputs) :
  R.v9810 (state s) (inputs i) = Zmod.unsigned (N.v9810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9810 s i)) at 1.
  unfold R.v9810, N.v9810.
  rewrite ?node_9651.
  rewrite ?node_9654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9811 (s : N.State) (i : N.Inputs) :
  R.v9811 (state s) (inputs i) = Zmod.unsigned (N.v9811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9811 s i)) at 1.
  unfold R.v9811, N.v9811.
  rewrite ?node_9655.
  rewrite ?node_9658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9812 (s : N.State) (i : N.Inputs) :
  R.v9812 (state s) (inputs i) = Zmod.unsigned (N.v9812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9812 s i)) at 1.
  unfold R.v9812, N.v9812.
  rewrite ?node_9810.
  rewrite ?node_9811.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9813 (s : N.State) (i : N.Inputs) :
  R.v9813 (state s) (inputs i) = Zmod.unsigned (N.v9813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9813 s i)) at 1.
  unfold R.v9813, N.v9813.
  rewrite ?node_9809.
  rewrite ?node_9812.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9814 (s : N.State) (i : N.Inputs) :
  R.v9814 (state s) (inputs i) = Zmod.unsigned (N.v9814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9814 s i)) at 1.
  unfold R.v9814, N.v9814.
  rewrite ?node_9813.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2393_nr_5F2424.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2393_nr_5F2424 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9815 (s : N.State) (i : N.Inputs) :
  R.v9815 (state s) (inputs i) = Zmod.unsigned (N.v9815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9815 s i)) at 1.
  unfold R.v9815, N.v9815.
  rewrite ?node_9659.
  rewrite ?node_9662.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9816 (s : N.State) (i : N.Inputs) :
  R.v9816 (state s) (inputs i) = Zmod.unsigned (N.v9816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9816 s i)) at 1.
  unfold R.v9816, N.v9816.
  rewrite ?node_9815.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2394_nr_5F2425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2394_nr_5F2425 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9817 (s : N.State) (i : N.Inputs) :
  R.v9817 (state s) (inputs i) = Zmod.unsigned (N.v9817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9817 s i)) at 1.
  unfold R.v9817, N.v9817.
  rewrite !state_r1022_nr_5F1022.
  rewrite !state_r1023_nr_5F1023.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1022_nr_5F1022 s)).
  rewrite ?(bits.mod_to_Z (N.r1023_nr_5F1023 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9818 (s : N.State) (i : N.Inputs) :
  R.v9818 (state s) (inputs i) = Zmod.unsigned (N.v9818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9818 s i)) at 1.
  unfold R.v9818, N.v9818.
  rewrite ?node_9817.
  rewrite !state_r1024_nr_5F1024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1024_nr_5F1024 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9819 (s : N.State) (i : N.Inputs) :
  R.v9819 (state s) (inputs i) = Zmod.unsigned (N.v9819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9819 s i)) at 1.
  unfold R.v9819, N.v9819.
  rewrite ?node_9818.
  rewrite !state_r1025_nr_5F1025.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1025_nr_5F1025 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9820 (s : N.State) (i : N.Inputs) :
  R.v9820 (state s) (inputs i) = Zmod.unsigned (N.v9820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9820 s i)) at 1.
  unfold R.v9820, N.v9820.
  rewrite !state_r990_nr_5F990.
  rewrite !state_r991_nr_5F991.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r990_nr_5F990 s)).
  rewrite ?(bits.mod_to_Z (N.r991_nr_5F991 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9821 (s : N.State) (i : N.Inputs) :
  R.v9821 (state s) (inputs i) = Zmod.unsigned (N.v9821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9821 s i)) at 1.
  unfold R.v9821, N.v9821.
  rewrite ?node_9667.
  rewrite !state_r992_nr_5F992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r992_nr_5F992 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9822 (s : N.State) (i : N.Inputs) :
  R.v9822 (state s) (inputs i) = Zmod.unsigned (N.v9822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9822 s i)) at 1.
  unfold R.v9822, N.v9822.
  rewrite ?node_9820.
  rewrite ?node_9821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9823 (s : N.State) (i : N.Inputs) :
  R.v9823 (state s) (inputs i) = Zmod.unsigned (N.v9823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9823 s i)) at 1.
  unfold R.v9823, N.v9823.
  rewrite ?node_9819.
  rewrite ?node_9822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9824 (s : N.State) (i : N.Inputs) :
  R.v9824 (state s) (inputs i) = Zmod.unsigned (N.v9824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9824 s i)) at 1.
  unfold R.v9824, N.v9824.
  rewrite !state_r1026_nr_5F1026.
  rewrite !state_r1027_nr_5F1027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1026_nr_5F1026 s)).
  rewrite ?(bits.mod_to_Z (N.r1027_nr_5F1027 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9825 (s : N.State) (i : N.Inputs) :
  R.v9825 (state s) (inputs i) = Zmod.unsigned (N.v9825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9825 s i)) at 1.
  unfold R.v9825, N.v9825.
  rewrite ?node_9824.
  rewrite !state_r1028_nr_5F1028.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1028_nr_5F1028 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9826 (s : N.State) (i : N.Inputs) :
  R.v9826 (state s) (inputs i) = Zmod.unsigned (N.v9826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9826 s i)) at 1.
  unfold R.v9826, N.v9826.
  rewrite ?node_9825.
  rewrite !state_r1029_nr_5F1029.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1029_nr_5F1029 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9827 (s : N.State) (i : N.Inputs) :
  R.v9827 (state s) (inputs i) = Zmod.unsigned (N.v9827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9827 s i)) at 1.
  unfold R.v9827, N.v9827.
  rewrite !state_r994_nr_5F994.
  rewrite !state_r995_nr_5F995.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r994_nr_5F994 s)).
  rewrite ?(bits.mod_to_Z (N.r995_nr_5F995 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9828 (s : N.State) (i : N.Inputs) :
  R.v9828 (state s) (inputs i) = Zmod.unsigned (N.v9828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9828 s i)) at 1.
  unfold R.v9828, N.v9828.
  rewrite ?node_9674.
  rewrite !state_r996_nr_5F996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r996_nr_5F996 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9829 (s : N.State) (i : N.Inputs) :
  R.v9829 (state s) (inputs i) = Zmod.unsigned (N.v9829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9829 s i)) at 1.
  unfold R.v9829, N.v9829.
  rewrite ?node_9827.
  rewrite ?node_9828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9830 (s : N.State) (i : N.Inputs) :
  R.v9830 (state s) (inputs i) = Zmod.unsigned (N.v9830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9830 s i)) at 1.
  unfold R.v9830, N.v9830.
  rewrite ?node_9826.
  rewrite ?node_9829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9831 (s : N.State) (i : N.Inputs) :
  R.v9831 (state s) (inputs i) = Zmod.unsigned (N.v9831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9831 s i)) at 1.
  unfold R.v9831, N.v9831.
  rewrite ?node_9823.
  rewrite ?node_9830.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9832 (s : N.State) (i : N.Inputs) :
  R.v9832 (state s) (inputs i) = Zmod.unsigned (N.v9832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9832 s i)) at 1.
  unfold R.v9832, N.v9832.
  rewrite !state_r1030_nr_5F1030.
  rewrite !state_r1031_nr_5F1031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1030_nr_5F1030 s)).
  rewrite ?(bits.mod_to_Z (N.r1031_nr_5F1031 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9833 (s : N.State) (i : N.Inputs) :
  R.v9833 (state s) (inputs i) = Zmod.unsigned (N.v9833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9833 s i)) at 1.
  unfold R.v9833, N.v9833.
  rewrite ?node_9832.
  rewrite !state_r1032_nr_5F1032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1032_nr_5F1032 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9834 (s : N.State) (i : N.Inputs) :
  R.v9834 (state s) (inputs i) = Zmod.unsigned (N.v9834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9834 s i)) at 1.
  unfold R.v9834, N.v9834.
  rewrite ?node_9833.
  rewrite !state_r1033_nr_5F1033.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1033_nr_5F1033 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9835 (s : N.State) (i : N.Inputs) :
  R.v9835 (state s) (inputs i) = Zmod.unsigned (N.v9835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9835 s i)) at 1.
  unfold R.v9835, N.v9835.
  rewrite !state_r998_nr_5F998.
  rewrite !state_r999_nr_5F999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r998_nr_5F998 s)).
  rewrite ?(bits.mod_to_Z (N.r999_nr_5F999 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9836 (s : N.State) (i : N.Inputs) :
  R.v9836 (state s) (inputs i) = Zmod.unsigned (N.v9836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9836 s i)) at 1.
  unfold R.v9836, N.v9836.
  rewrite ?node_9682.
  rewrite !state_r1000_nr_5F1000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1000_nr_5F1000 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9837 (s : N.State) (i : N.Inputs) :
  R.v9837 (state s) (inputs i) = Zmod.unsigned (N.v9837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9837 s i)) at 1.
  unfold R.v9837, N.v9837.
  rewrite ?node_9835.
  rewrite ?node_9836.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9838 (s : N.State) (i : N.Inputs) :
  R.v9838 (state s) (inputs i) = Zmod.unsigned (N.v9838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9838 s i)) at 1.
  unfold R.v9838, N.v9838.
  rewrite ?node_9834.
  rewrite ?node_9837.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9839 (s : N.State) (i : N.Inputs) :
  R.v9839 (state s) (inputs i) = Zmod.unsigned (N.v9839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9839 s i)) at 1.
  unfold R.v9839, N.v9839.
  rewrite ?node_9831.
  rewrite ?node_9838.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9840 (s : N.State) (i : N.Inputs) :
  R.v9840 (state s) (inputs i) = Zmod.unsigned (N.v9840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9840 s i)) at 1.
  unfold R.v9840, N.v9840.
  rewrite !state_r1034_nr_5F1034.
  rewrite !state_r1035_nr_5F1035.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1034_nr_5F1034 s)).
  rewrite ?(bits.mod_to_Z (N.r1035_nr_5F1035 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9841 (s : N.State) (i : N.Inputs) :
  R.v9841 (state s) (inputs i) = Zmod.unsigned (N.v9841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9841 s i)) at 1.
  unfold R.v9841, N.v9841.
  rewrite ?node_9840.
  rewrite !state_r1036_nr_5F1036.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1036_nr_5F1036 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9842 (s : N.State) (i : N.Inputs) :
  R.v9842 (state s) (inputs i) = Zmod.unsigned (N.v9842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9842 s i)) at 1.
  unfold R.v9842, N.v9842.
  rewrite ?node_9841.
  rewrite !state_r1037_nr_5F1037.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1037_nr_5F1037 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9843 (s : N.State) (i : N.Inputs) :
  R.v9843 (state s) (inputs i) = Zmod.unsigned (N.v9843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9843 s i)) at 1.
  unfold R.v9843, N.v9843.
  rewrite !state_r1002_nr_5F1002.
  rewrite !state_r1003_nr_5F1003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1002_nr_5F1002 s)).
  rewrite ?(bits.mod_to_Z (N.r1003_nr_5F1003 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9844 (s : N.State) (i : N.Inputs) :
  R.v9844 (state s) (inputs i) = Zmod.unsigned (N.v9844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9844 s i)) at 1.
  unfold R.v9844, N.v9844.
  rewrite ?node_9690.
  rewrite !state_r1004_nr_5F1004.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1004_nr_5F1004 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9845 (s : N.State) (i : N.Inputs) :
  R.v9845 (state s) (inputs i) = Zmod.unsigned (N.v9845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9845 s i)) at 1.
  unfold R.v9845, N.v9845.
  rewrite ?node_9843.
  rewrite ?node_9844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9846 (s : N.State) (i : N.Inputs) :
  R.v9846 (state s) (inputs i) = Zmod.unsigned (N.v9846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9846 s i)) at 1.
  unfold R.v9846, N.v9846.
  rewrite ?node_9842.
  rewrite ?node_9845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9847 (s : N.State) (i : N.Inputs) :
  R.v9847 (state s) (inputs i) = Zmod.unsigned (N.v9847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9847 s i)) at 1.
  unfold R.v9847, N.v9847.
  rewrite ?node_9839.
  rewrite ?node_9846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9848 (s : N.State) (i : N.Inputs) :
  R.v9848 (state s) (inputs i) = Zmod.unsigned (N.v9848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9848 s i)) at 1.
  unfold R.v9848, N.v9848.
  rewrite ?node_9673.
  rewrite ?node_9680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9849 (s : N.State) (i : N.Inputs) :
  R.v9849 (state s) (inputs i) = Zmod.unsigned (N.v9849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9849 s i)) at 1.
  unfold R.v9849, N.v9849.
  rewrite ?node_9681.
  rewrite ?node_9688.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9850 (s : N.State) (i : N.Inputs) :
  R.v9850 (state s) (inputs i) = Zmod.unsigned (N.v9850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9850 s i)) at 1.
  unfold R.v9850, N.v9850.
  rewrite ?node_9848.
  rewrite ?node_9849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9851 (s : N.State) (i : N.Inputs) :
  R.v9851 (state s) (inputs i) = Zmod.unsigned (N.v9851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9851 s i)) at 1.
  unfold R.v9851, N.v9851.
  rewrite ?node_9847.
  rewrite ?node_9850.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9852 (s : N.State) (i : N.Inputs) :
  R.v9852 (state s) (inputs i) = Zmod.unsigned (N.v9852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9852 s i)) at 1.
  unfold R.v9852, N.v9852.
  rewrite !state_r1038_nr_5F1038.
  rewrite !state_r1039_nr_5F1039.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1038_nr_5F1038 s)).
  rewrite ?(bits.mod_to_Z (N.r1039_nr_5F1039 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9853 (s : N.State) (i : N.Inputs) :
  R.v9853 (state s) (inputs i) = Zmod.unsigned (N.v9853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9853 s i)) at 1.
  unfold R.v9853, N.v9853.
  rewrite ?node_9852.
  rewrite !state_r1040_nr_5F1040.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1040_nr_5F1040 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9854 (s : N.State) (i : N.Inputs) :
  R.v9854 (state s) (inputs i) = Zmod.unsigned (N.v9854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9854 s i)) at 1.
  unfold R.v9854, N.v9854.
  rewrite ?node_9853.
  rewrite !state_r1041_nr_5F1041.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1041_nr_5F1041 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9855 (s : N.State) (i : N.Inputs) :
  R.v9855 (state s) (inputs i) = Zmod.unsigned (N.v9855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9855 s i)) at 1.
  unfold R.v9855, N.v9855.
  rewrite !state_r1006_nr_5F1006.
  rewrite !state_r1007_nr_5F1007.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1006_nr_5F1006 s)).
  rewrite ?(bits.mod_to_Z (N.r1007_nr_5F1007 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9856 (s : N.State) (i : N.Inputs) :
  R.v9856 (state s) (inputs i) = Zmod.unsigned (N.v9856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9856 s i)) at 1.
  unfold R.v9856, N.v9856.
  rewrite ?node_9702.
  rewrite !state_r1008_nr_5F1008.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1008_nr_5F1008 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9857 (s : N.State) (i : N.Inputs) :
  R.v9857 (state s) (inputs i) = Zmod.unsigned (N.v9857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9857 s i)) at 1.
  unfold R.v9857, N.v9857.
  rewrite ?node_9855.
  rewrite ?node_9856.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9858 (s : N.State) (i : N.Inputs) :
  R.v9858 (state s) (inputs i) = Zmod.unsigned (N.v9858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9858 s i)) at 1.
  unfold R.v9858, N.v9858.
  rewrite ?node_9854.
  rewrite ?node_9857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9859 (s : N.State) (i : N.Inputs) :
  R.v9859 (state s) (inputs i) = Zmod.unsigned (N.v9859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9859 s i)) at 1.
  unfold R.v9859, N.v9859.
  rewrite !state_r1042_nr_5F1042.
  rewrite !state_r1043_nr_5F1043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1042_nr_5F1042 s)).
  rewrite ?(bits.mod_to_Z (N.r1043_nr_5F1043 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9860 (s : N.State) (i : N.Inputs) :
  R.v9860 (state s) (inputs i) = Zmod.unsigned (N.v9860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9860 s i)) at 1.
  unfold R.v9860, N.v9860.
  rewrite ?node_9859.
  rewrite !state_r1044_nr_5F1044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1044_nr_5F1044 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9861 (s : N.State) (i : N.Inputs) :
  R.v9861 (state s) (inputs i) = Zmod.unsigned (N.v9861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9861 s i)) at 1.
  unfold R.v9861, N.v9861.
  rewrite ?node_9860.
  rewrite !state_r1045_nr_5F1045.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1045_nr_5F1045 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9862 (s : N.State) (i : N.Inputs) :
  R.v9862 (state s) (inputs i) = Zmod.unsigned (N.v9862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9862 s i)) at 1.
  unfold R.v9862, N.v9862.
  rewrite !state_r1010_nr_5F1010.
  rewrite !state_r1011_nr_5F1011.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1010_nr_5F1010 s)).
  rewrite ?(bits.mod_to_Z (N.r1011_nr_5F1011 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9863 (s : N.State) (i : N.Inputs) :
  R.v9863 (state s) (inputs i) = Zmod.unsigned (N.v9863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9863 s i)) at 1.
  unfold R.v9863, N.v9863.
  rewrite ?node_9709.
  rewrite !state_r1012_nr_5F1012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1012_nr_5F1012 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9864 (s : N.State) (i : N.Inputs) :
  R.v9864 (state s) (inputs i) = Zmod.unsigned (N.v9864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9864 s i)) at 1.
  unfold R.v9864, N.v9864.
  rewrite ?node_9862.
  rewrite ?node_9863.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9865 (s : N.State) (i : N.Inputs) :
  R.v9865 (state s) (inputs i) = Zmod.unsigned (N.v9865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9865 s i)) at 1.
  unfold R.v9865, N.v9865.
  rewrite ?node_9861.
  rewrite ?node_9864.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9866 (s : N.State) (i : N.Inputs) :
  R.v9866 (state s) (inputs i) = Zmod.unsigned (N.v9866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9866 s i)) at 1.
  unfold R.v9866, N.v9866.
  rewrite ?node_9858.
  rewrite ?node_9865.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9867 (s : N.State) (i : N.Inputs) :
  R.v9867 (state s) (inputs i) = Zmod.unsigned (N.v9867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9867 s i)) at 1.
  unfold R.v9867, N.v9867.
  rewrite !state_r1046_nr_5F1046.
  rewrite !state_r1047_nr_5F1047.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1046_nr_5F1046 s)).
  rewrite ?(bits.mod_to_Z (N.r1047_nr_5F1047 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9868 (s : N.State) (i : N.Inputs) :
  R.v9868 (state s) (inputs i) = Zmod.unsigned (N.v9868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9868 s i)) at 1.
  unfold R.v9868, N.v9868.
  rewrite ?node_9867.
  rewrite !state_r1048_nr_5F1048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1048_nr_5F1048 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9869 (s : N.State) (i : N.Inputs) :
  R.v9869 (state s) (inputs i) = Zmod.unsigned (N.v9869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9869 s i)) at 1.
  unfold R.v9869, N.v9869.
  rewrite ?node_9868.
  rewrite !state_r1049_nr_5F1049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1049_nr_5F1049 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9870 (s : N.State) (i : N.Inputs) :
  R.v9870 (state s) (inputs i) = Zmod.unsigned (N.v9870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9870 s i)) at 1.
  unfold R.v9870, N.v9870.
  rewrite !state_r1014_nr_5F1014.
  rewrite !state_r1015_nr_5F1015.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1014_nr_5F1014 s)).
  rewrite ?(bits.mod_to_Z (N.r1015_nr_5F1015 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9871 (s : N.State) (i : N.Inputs) :
  R.v9871 (state s) (inputs i) = Zmod.unsigned (N.v9871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9871 s i)) at 1.
  unfold R.v9871, N.v9871.
  rewrite ?node_9717.
  rewrite !state_r1016_nr_5F1016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1016_nr_5F1016 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9872 (s : N.State) (i : N.Inputs) :
  R.v9872 (state s) (inputs i) = Zmod.unsigned (N.v9872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9872 s i)) at 1.
  unfold R.v9872, N.v9872.
  rewrite ?node_9870.
  rewrite ?node_9871.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9873 (s : N.State) (i : N.Inputs) :
  R.v9873 (state s) (inputs i) = Zmod.unsigned (N.v9873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9873 s i)) at 1.
  unfold R.v9873, N.v9873.
  rewrite ?node_9869.
  rewrite ?node_9872.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9874 (s : N.State) (i : N.Inputs) :
  R.v9874 (state s) (inputs i) = Zmod.unsigned (N.v9874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9874 s i)) at 1.
  unfold R.v9874, N.v9874.
  rewrite ?node_9866.
  rewrite ?node_9873.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9875 (s : N.State) (i : N.Inputs) :
  R.v9875 (state s) (inputs i) = Zmod.unsigned (N.v9875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9875 s i)) at 1.
  unfold R.v9875, N.v9875.
  rewrite !state_r1050_nr_5F1050.
  rewrite !state_r1051_nr_5F1051.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1050_nr_5F1050 s)).
  rewrite ?(bits.mod_to_Z (N.r1051_nr_5F1051 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9876 (s : N.State) (i : N.Inputs) :
  R.v9876 (state s) (inputs i) = Zmod.unsigned (N.v9876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9876 s i)) at 1.
  unfold R.v9876, N.v9876.
  rewrite ?node_9875.
  rewrite !state_r1052_nr_5F1052.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1052_nr_5F1052 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9877 (s : N.State) (i : N.Inputs) :
  R.v9877 (state s) (inputs i) = Zmod.unsigned (N.v9877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9877 s i)) at 1.
  unfold R.v9877, N.v9877.
  rewrite ?node_9876.
  rewrite !state_r1053_nr_5F1053.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1053_nr_5F1053 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9878 (s : N.State) (i : N.Inputs) :
  R.v9878 (state s) (inputs i) = Zmod.unsigned (N.v9878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9878 s i)) at 1.
  unfold R.v9878, N.v9878.
  rewrite !state_r1018_nr_5F1018.
  rewrite !state_r1019_nr_5F1019.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1018_nr_5F1018 s)).
  rewrite ?(bits.mod_to_Z (N.r1019_nr_5F1019 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9879 (s : N.State) (i : N.Inputs) :
  R.v9879 (state s) (inputs i) = Zmod.unsigned (N.v9879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9879 s i)) at 1.
  unfold R.v9879, N.v9879.
  rewrite ?node_9725.
  rewrite !state_r1020_nr_5F1020.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1020_nr_5F1020 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9880 (s : N.State) (i : N.Inputs) :
  R.v9880 (state s) (inputs i) = Zmod.unsigned (N.v9880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9880 s i)) at 1.
  unfold R.v9880, N.v9880.
  rewrite ?node_9878.
  rewrite ?node_9879.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9881 (s : N.State) (i : N.Inputs) :
  R.v9881 (state s) (inputs i) = Zmod.unsigned (N.v9881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9881 s i)) at 1.
  unfold R.v9881, N.v9881.
  rewrite ?node_9877.
  rewrite ?node_9880.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9882 (s : N.State) (i : N.Inputs) :
  R.v9882 (state s) (inputs i) = Zmod.unsigned (N.v9882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9882 s i)) at 1.
  unfold R.v9882, N.v9882.
  rewrite ?node_9874.
  rewrite ?node_9881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9883 (s : N.State) (i : N.Inputs) :
  R.v9883 (state s) (inputs i) = Zmod.unsigned (N.v9883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9883 s i)) at 1.
  unfold R.v9883, N.v9883.
  rewrite ?node_9708.
  rewrite ?node_9715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9884 (s : N.State) (i : N.Inputs) :
  R.v9884 (state s) (inputs i) = Zmod.unsigned (N.v9884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9884 s i)) at 1.
  unfold R.v9884, N.v9884.
  rewrite ?node_9716.
  rewrite ?node_9723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9885 (s : N.State) (i : N.Inputs) :
  R.v9885 (state s) (inputs i) = Zmod.unsigned (N.v9885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9885 s i)) at 1.
  unfold R.v9885, N.v9885.
  rewrite ?node_9883.
  rewrite ?node_9884.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9886 (s : N.State) (i : N.Inputs) :
  R.v9886 (state s) (inputs i) = Zmod.unsigned (N.v9886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9886 s i)) at 1.
  unfold R.v9886, N.v9886.
  rewrite ?node_9882.
  rewrite ?node_9885.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9887 (s : N.State) (i : N.Inputs) :
  R.v9887 (state s) (inputs i) = Zmod.unsigned (N.v9887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9887 s i)) at 1.
  unfold R.v9887, N.v9887.
  rewrite ?node_9851.
  rewrite ?node_9886.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9888 (s : N.State) (i : N.Inputs) :
  R.v9888 (state s) (inputs i) = Zmod.unsigned (N.v9888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9888 s i)) at 1.
  unfold R.v9888, N.v9888.
  rewrite ?node_9668.
  rewrite !state_r993_nr_5F993.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r993_nr_5F993 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9889 (s : N.State) (i : N.Inputs) :
  R.v9889 (state s) (inputs i) = Zmod.unsigned (N.v9889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9889 s i)) at 1.
  unfold R.v9889, N.v9889.
  rewrite ?node_9669.
  rewrite ?node_9672.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9890 (s : N.State) (i : N.Inputs) :
  R.v9890 (state s) (inputs i) = Zmod.unsigned (N.v9890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9890 s i)) at 1.
  unfold R.v9890, N.v9890.
  rewrite ?node_9888.
  rewrite ?node_9889.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9891 (s : N.State) (i : N.Inputs) :
  R.v9891 (state s) (inputs i) = Zmod.unsigned (N.v9891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9891 s i)) at 1.
  unfold R.v9891, N.v9891.
  rewrite ?node_9675.
  rewrite !state_r997_nr_5F997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r997_nr_5F997 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9892 (s : N.State) (i : N.Inputs) :
  R.v9892 (state s) (inputs i) = Zmod.unsigned (N.v9892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9892 s i)) at 1.
  unfold R.v9892, N.v9892.
  rewrite ?node_9676.
  rewrite ?node_9679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9893 (s : N.State) (i : N.Inputs) :
  R.v9893 (state s) (inputs i) = Zmod.unsigned (N.v9893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9893 s i)) at 1.
  unfold R.v9893, N.v9893.
  rewrite ?node_9891.
  rewrite ?node_9892.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9894 (s : N.State) (i : N.Inputs) :
  R.v9894 (state s) (inputs i) = Zmod.unsigned (N.v9894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9894 s i)) at 1.
  unfold R.v9894, N.v9894.
  rewrite ?node_9890.
  rewrite ?node_9893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9895 (s : N.State) (i : N.Inputs) :
  R.v9895 (state s) (inputs i) = Zmod.unsigned (N.v9895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9895 s i)) at 1.
  unfold R.v9895, N.v9895.
  rewrite ?node_9683.
  rewrite !state_r1001_nr_5F1001.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1001_nr_5F1001 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9896 (s : N.State) (i : N.Inputs) :
  R.v9896 (state s) (inputs i) = Zmod.unsigned (N.v9896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9896 s i)) at 1.
  unfold R.v9896, N.v9896.
  rewrite ?node_9684.
  rewrite ?node_9687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9897 (s : N.State) (i : N.Inputs) :
  R.v9897 (state s) (inputs i) = Zmod.unsigned (N.v9897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9897 s i)) at 1.
  unfold R.v9897, N.v9897.
  rewrite ?node_9895.
  rewrite ?node_9896.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9898 (s : N.State) (i : N.Inputs) :
  R.v9898 (state s) (inputs i) = Zmod.unsigned (N.v9898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9898 s i)) at 1.
  unfold R.v9898, N.v9898.
  rewrite ?node_9894.
  rewrite ?node_9897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9899 (s : N.State) (i : N.Inputs) :
  R.v9899 (state s) (inputs i) = Zmod.unsigned (N.v9899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9899 s i)) at 1.
  unfold R.v9899, N.v9899.
  rewrite ?node_9691.
  rewrite !state_r1005_nr_5F1005.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1005_nr_5F1005 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9900 (s : N.State) (i : N.Inputs) :
  R.v9900 (state s) (inputs i) = Zmod.unsigned (N.v9900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9900 s i)) at 1.
  unfold R.v9900, N.v9900.
  rewrite ?node_9692.
  rewrite ?node_9695.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9901 (s : N.State) (i : N.Inputs) :
  R.v9901 (state s) (inputs i) = Zmod.unsigned (N.v9901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9901 s i)) at 1.
  unfold R.v9901, N.v9901.
  rewrite ?node_9899.
  rewrite ?node_9900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9902 (s : N.State) (i : N.Inputs) :
  R.v9902 (state s) (inputs i) = Zmod.unsigned (N.v9902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9902 s i)) at 1.
  unfold R.v9902, N.v9902.
  rewrite ?node_9898.
  rewrite ?node_9901.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9903 (s : N.State) (i : N.Inputs) :
  R.v9903 (state s) (inputs i) = Zmod.unsigned (N.v9903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9903 s i)) at 1.
  unfold R.v9903, N.v9903.
  rewrite ?node_9736.
  rewrite ?node_9739.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9904 (s : N.State) (i : N.Inputs) :
  R.v9904 (state s) (inputs i) = Zmod.unsigned (N.v9904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9904 s i)) at 1.
  unfold R.v9904, N.v9904.
  rewrite ?node_9740.
  rewrite ?node_9743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9905 (s : N.State) (i : N.Inputs) :
  R.v9905 (state s) (inputs i) = Zmod.unsigned (N.v9905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9905 s i)) at 1.
  unfold R.v9905, N.v9905.
  rewrite ?node_9903.
  rewrite ?node_9904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9906 (s : N.State) (i : N.Inputs) :
  R.v9906 (state s) (inputs i) = Zmod.unsigned (N.v9906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9906 s i)) at 1.
  unfold R.v9906, N.v9906.
  rewrite ?node_9902.
  rewrite ?node_9905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9907 (s : N.State) (i : N.Inputs) :
  R.v9907 (state s) (inputs i) = Zmod.unsigned (N.v9907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9907 s i)) at 1.
  unfold R.v9907, N.v9907.
  rewrite ?node_9887.
  rewrite ?node_9906.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9908 (s : N.State) (i : N.Inputs) :
  R.v9908 (state s) (inputs i) = Zmod.unsigned (N.v9908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9908 s i)) at 1.
  unfold R.v9908, N.v9908.
  rewrite ?node_9703.
  rewrite !state_r1009_nr_5F1009.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1009_nr_5F1009 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9909 (s : N.State) (i : N.Inputs) :
  R.v9909 (state s) (inputs i) = Zmod.unsigned (N.v9909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9909 s i)) at 1.
  unfold R.v9909, N.v9909.
  rewrite ?node_9704.
  rewrite ?node_9707.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9910 (s : N.State) (i : N.Inputs) :
  R.v9910 (state s) (inputs i) = Zmod.unsigned (N.v9910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9910 s i)) at 1.
  unfold R.v9910, N.v9910.
  rewrite ?node_9908.
  rewrite ?node_9909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9911 (s : N.State) (i : N.Inputs) :
  R.v9911 (state s) (inputs i) = Zmod.unsigned (N.v9911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9911 s i)) at 1.
  unfold R.v9911, N.v9911.
  rewrite ?node_9710.
  rewrite !state_r1013_nr_5F1013.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1013_nr_5F1013 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9912 (s : N.State) (i : N.Inputs) :
  R.v9912 (state s) (inputs i) = Zmod.unsigned (N.v9912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9912 s i)) at 1.
  unfold R.v9912, N.v9912.
  rewrite ?node_9711.
  rewrite ?node_9714.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9913 (s : N.State) (i : N.Inputs) :
  R.v9913 (state s) (inputs i) = Zmod.unsigned (N.v9913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9913 s i)) at 1.
  unfold R.v9913, N.v9913.
  rewrite ?node_9911.
  rewrite ?node_9912.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9914 (s : N.State) (i : N.Inputs) :
  R.v9914 (state s) (inputs i) = Zmod.unsigned (N.v9914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9914 s i)) at 1.
  unfold R.v9914, N.v9914.
  rewrite ?node_9910.
  rewrite ?node_9913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9915 (s : N.State) (i : N.Inputs) :
  R.v9915 (state s) (inputs i) = Zmod.unsigned (N.v9915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9915 s i)) at 1.
  unfold R.v9915, N.v9915.
  rewrite ?node_9718.
  rewrite !state_r1017_nr_5F1017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1017_nr_5F1017 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9916 (s : N.State) (i : N.Inputs) :
  R.v9916 (state s) (inputs i) = Zmod.unsigned (N.v9916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9916 s i)) at 1.
  unfold R.v9916, N.v9916.
  rewrite ?node_9719.
  rewrite ?node_9722.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9917 (s : N.State) (i : N.Inputs) :
  R.v9917 (state s) (inputs i) = Zmod.unsigned (N.v9917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9917 s i)) at 1.
  unfold R.v9917, N.v9917.
  rewrite ?node_9915.
  rewrite ?node_9916.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9918 (s : N.State) (i : N.Inputs) :
  R.v9918 (state s) (inputs i) = Zmod.unsigned (N.v9918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9918 s i)) at 1.
  unfold R.v9918, N.v9918.
  rewrite ?node_9914.
  rewrite ?node_9917.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9919 (s : N.State) (i : N.Inputs) :
  R.v9919 (state s) (inputs i) = Zmod.unsigned (N.v9919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9919 s i)) at 1.
  unfold R.v9919, N.v9919.
  rewrite ?node_9726.
  rewrite !state_r1021_nr_5F1021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1021_nr_5F1021 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9920 (s : N.State) (i : N.Inputs) :
  R.v9920 (state s) (inputs i) = Zmod.unsigned (N.v9920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9920 s i)) at 1.
  unfold R.v9920, N.v9920.
  rewrite ?node_9918.
  rewrite ?node_9919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9921 (s : N.State) (i : N.Inputs) :
  R.v9921 (state s) (inputs i) = Zmod.unsigned (N.v9921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9921 s i)) at 1.
  unfold R.v9921, N.v9921.
  rewrite ?node_9756.
  rewrite ?node_9759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9922 (s : N.State) (i : N.Inputs) :
  R.v9922 (state s) (inputs i) = Zmod.unsigned (N.v9922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9922 s i)) at 1.
  unfold R.v9922, N.v9922.
  rewrite ?node_9760.
  rewrite ?node_9763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9923 (s : N.State) (i : N.Inputs) :
  R.v9923 (state s) (inputs i) = Zmod.unsigned (N.v9923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9923 s i)) at 1.
  unfold R.v9923, N.v9923.
  rewrite ?node_9921.
  rewrite ?node_9922.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9924 (s : N.State) (i : N.Inputs) :
  R.v9924 (state s) (inputs i) = Zmod.unsigned (N.v9924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9924 s i)) at 1.
  unfold R.v9924, N.v9924.
  rewrite ?node_9920.
  rewrite ?node_9923.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9925 (s : N.State) (i : N.Inputs) :
  R.v9925 (state s) (inputs i) = Zmod.unsigned (N.v9925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9925 s i)) at 1.
  unfold R.v9925, N.v9925.
  rewrite ?node_9907.
  rewrite ?node_9924.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9926 (s : N.State) (i : N.Inputs) :
  R.v9926 (state s) (inputs i) = Zmod.unsigned (N.v9926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9926 s i)) at 1.
  unfold R.v9926, N.v9926.
  rewrite ?node_9701.
  rewrite ?node_9732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9927 (s : N.State) (i : N.Inputs) :
  R.v9927 (state s) (inputs i) = Zmod.unsigned (N.v9927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9927 s i)) at 1.
  unfold R.v9927, N.v9927.
  rewrite ?node_9733.
  rewrite ?node_9752.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9928 (s : N.State) (i : N.Inputs) :
  R.v9928 (state s) (inputs i) = Zmod.unsigned (N.v9928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9928 s i)) at 1.
  unfold R.v9928, N.v9928.
  rewrite ?node_9926.
  rewrite ?node_9927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9929 (s : N.State) (i : N.Inputs) :
  R.v9929 (state s) (inputs i) = Zmod.unsigned (N.v9929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9929 s i)) at 1.
  unfold R.v9929, N.v9929.
  rewrite ?node_9925.
  rewrite ?node_9928.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9930 (s : N.State) (i : N.Inputs) :
  R.v9930 (state s) (inputs i) = Zmod.unsigned (N.v9930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9930 s i)) at 1.
  unfold R.v9930, N.v9930.
  rewrite ?node_9689.
  rewrite ?node_9696.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9931 (s : N.State) (i : N.Inputs) :
  R.v9931 (state s) (inputs i) = Zmod.unsigned (N.v9931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9931 s i)) at 1.
  unfold R.v9931, N.v9931.
  rewrite ?node_9697.
  rewrite ?node_9700.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9932 (s : N.State) (i : N.Inputs) :
  R.v9932 (state s) (inputs i) = Zmod.unsigned (N.v9932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9932 s i)) at 1.
  unfold R.v9932, N.v9932.
  rewrite ?node_9930.
  rewrite ?node_9931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9933 (s : N.State) (i : N.Inputs) :
  R.v9933 (state s) (inputs i) = Zmod.unsigned (N.v9933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9933 s i)) at 1.
  unfold R.v9933, N.v9933.
  rewrite ?node_9724.
  rewrite ?node_9727.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9934 (s : N.State) (i : N.Inputs) :
  R.v9934 (state s) (inputs i) = Zmod.unsigned (N.v9934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9934 s i)) at 1.
  unfold R.v9934, N.v9934.
  rewrite ?node_9728.
  rewrite ?node_9731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9935 (s : N.State) (i : N.Inputs) :
  R.v9935 (state s) (inputs i) = Zmod.unsigned (N.v9935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9935 s i)) at 1.
  unfold R.v9935, N.v9935.
  rewrite ?node_9933.
  rewrite ?node_9934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9936 (s : N.State) (i : N.Inputs) :
  R.v9936 (state s) (inputs i) = Zmod.unsigned (N.v9936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9936 s i)) at 1.
  unfold R.v9936, N.v9936.
  rewrite ?node_9932.
  rewrite ?node_9935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9937 (s : N.State) (i : N.Inputs) :
  R.v9937 (state s) (inputs i) = Zmod.unsigned (N.v9937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9937 s i)) at 1.
  unfold R.v9937, N.v9937.
  rewrite ?node_9744.
  rewrite ?node_9747.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9938 (s : N.State) (i : N.Inputs) :
  R.v9938 (state s) (inputs i) = Zmod.unsigned (N.v9938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9938 s i)) at 1.
  unfold R.v9938, N.v9938.
  rewrite ?node_9748.
  rewrite ?node_9751.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9939 (s : N.State) (i : N.Inputs) :
  R.v9939 (state s) (inputs i) = Zmod.unsigned (N.v9939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9939 s i)) at 1.
  unfold R.v9939, N.v9939.
  rewrite ?node_9937.
  rewrite ?node_9938.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9940 (s : N.State) (i : N.Inputs) :
  R.v9940 (state s) (inputs i) = Zmod.unsigned (N.v9940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9940 s i)) at 1.
  unfold R.v9940, N.v9940.
  rewrite ?node_9936.
  rewrite ?node_9939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9941 (s : N.State) (i : N.Inputs) :
  R.v9941 (state s) (inputs i) = Zmod.unsigned (N.v9941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9941 s i)) at 1.
  unfold R.v9941, N.v9941.
  rewrite ?node_9764.
  rewrite ?node_9767.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9942 (s : N.State) (i : N.Inputs) :
  R.v9942 (state s) (inputs i) = Zmod.unsigned (N.v9942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9942 s i)) at 1.
  unfold R.v9942, N.v9942.
  rewrite ?node_9768.
  rewrite ?node_9771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9943 (s : N.State) (i : N.Inputs) :
  R.v9943 (state s) (inputs i) = Zmod.unsigned (N.v9943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9943 s i)) at 1.
  unfold R.v9943, N.v9943.
  rewrite ?node_9941.
  rewrite ?node_9942.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9944 (s : N.State) (i : N.Inputs) :
  R.v9944 (state s) (inputs i) = Zmod.unsigned (N.v9944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9944 s i)) at 1.
  unfold R.v9944, N.v9944.
  rewrite ?node_9940.
  rewrite ?node_9943.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9945 (s : N.State) (i : N.Inputs) :
  R.v9945 (state s) (inputs i) = Zmod.unsigned (N.v9945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9945 s i)) at 1.
  unfold R.v9945, N.v9945.
  rewrite ?node_9780.
  rewrite ?node_9783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9946 (s : N.State) (i : N.Inputs) :
  R.v9946 (state s) (inputs i) = Zmod.unsigned (N.v9946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9946 s i)) at 1.
  unfold R.v9946, N.v9946.
  rewrite ?node_9784.
  rewrite ?node_9787.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9947 (s : N.State) (i : N.Inputs) :
  R.v9947 (state s) (inputs i) = Zmod.unsigned (N.v9947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9947 s i)) at 1.
  unfold R.v9947, N.v9947.
  rewrite ?node_9945.
  rewrite ?node_9946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9948 (s : N.State) (i : N.Inputs) :
  R.v9948 (state s) (inputs i) = Zmod.unsigned (N.v9948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9948 s i)) at 1.
  unfold R.v9948, N.v9948.
  rewrite ?node_9944.
  rewrite ?node_9947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9949 (s : N.State) (i : N.Inputs) :
  R.v9949 (state s) (inputs i) = Zmod.unsigned (N.v9949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9949 s i)) at 1.
  unfold R.v9949, N.v9949.
  rewrite ?node_9929.
  rewrite ?node_9948.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9950 (s : N.State) (i : N.Inputs) :
  R.v9950 (state s) (inputs i) = Zmod.unsigned (N.v9950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9950 s i)) at 1.
  unfold R.v9950, N.v9950.
  rewrite ?node_9753.
  rewrite ?node_9772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9951 (s : N.State) (i : N.Inputs) :
  R.v9951 (state s) (inputs i) = Zmod.unsigned (N.v9951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9951 s i)) at 1.
  unfold R.v9951, N.v9951.
  rewrite ?node_9773.
  rewrite ?node_9776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9952 (s : N.State) (i : N.Inputs) :
  R.v9952 (state s) (inputs i) = Zmod.unsigned (N.v9952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9952 s i)) at 1.
  unfold R.v9952, N.v9952.
  rewrite ?node_9950.
  rewrite ?node_9951.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9953 (s : N.State) (i : N.Inputs) :
  R.v9953 (state s) (inputs i) = Zmod.unsigned (N.v9953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9953 s i)) at 1.
  unfold R.v9953, N.v9953.
  rewrite ?node_9949.
  rewrite ?node_9952.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9954 (s : N.State) (i : N.Inputs) :
  R.v9954 (state s) (inputs i) = Zmod.unsigned (N.v9954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9954 s i)) at 1.
  unfold R.v9954, N.v9954.
  rewrite ?node_9788.
  rewrite ?node_9791.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9955 (s : N.State) (i : N.Inputs) :
  R.v9955 (state s) (inputs i) = Zmod.unsigned (N.v9955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9955 s i)) at 1.
  unfold R.v9955, N.v9955.
  rewrite ?node_9792.
  rewrite ?node_9795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9956 (s : N.State) (i : N.Inputs) :
  R.v9956 (state s) (inputs i) = Zmod.unsigned (N.v9956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9956 s i)) at 1.
  unfold R.v9956, N.v9956.
  rewrite ?node_9954.
  rewrite ?node_9955.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9957 (s : N.State) (i : N.Inputs) :
  R.v9957 (state s) (inputs i) = Zmod.unsigned (N.v9957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9957 s i)) at 1.
  unfold R.v9957, N.v9957.
  rewrite ?node_9953.
  rewrite ?node_9956.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9958 (s : N.State) (i : N.Inputs) :
  R.v9958 (state s) (inputs i) = Zmod.unsigned (N.v9958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9958 s i)) at 1.
  unfold R.v9958, N.v9958.
  rewrite ?node_9777.
  rewrite ?node_9796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9959 (s : N.State) (i : N.Inputs) :
  R.v9959 (state s) (inputs i) = Zmod.unsigned (N.v9959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9959 s i)) at 1.
  unfold R.v9959, N.v9959.
  rewrite ?node_9797.
  rewrite ?node_9800.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9960 (s : N.State) (i : N.Inputs) :
  R.v9960 (state s) (inputs i) = Zmod.unsigned (N.v9960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9960 s i)) at 1.
  unfold R.v9960, N.v9960.
  rewrite ?node_9958.
  rewrite ?node_9959.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9961 (s : N.State) (i : N.Inputs) :
  R.v9961 (state s) (inputs i) = Zmod.unsigned (N.v9961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9961 s i)) at 1.
  unfold R.v9961, N.v9961.
  rewrite ?node_9957.
  rewrite ?node_9960.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9962 (s : N.State) (i : N.Inputs) :
  R.v9962 (state s) (inputs i) = Zmod.unsigned (N.v9962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9962 s i)) at 1.
  unfold R.v9962, N.v9962.
  rewrite ?node_9801.
  rewrite ?node_9804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9963 (s : N.State) (i : N.Inputs) :
  R.v9963 (state s) (inputs i) = Zmod.unsigned (N.v9963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9963 s i)) at 1.
  unfold R.v9963, N.v9963.
  rewrite ?node_9805.
  rewrite ?node_9808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9964 (s : N.State) (i : N.Inputs) :
  R.v9964 (state s) (inputs i) = Zmod.unsigned (N.v9964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9964 s i)) at 1.
  unfold R.v9964, N.v9964.
  rewrite ?node_9962.
  rewrite ?node_9963.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9965 (s : N.State) (i : N.Inputs) :
  R.v9965 (state s) (inputs i) = Zmod.unsigned (N.v9965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9965 s i)) at 1.
  unfold R.v9965, N.v9965.
  rewrite ?node_9961.
  rewrite ?node_9964.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9966 (s : N.State) (i : N.Inputs) :
  R.v9966 (state s) (inputs i) = Zmod.unsigned (N.v9966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9966 s i)) at 1.
  unfold R.v9966, N.v9966.
  rewrite ?node_9965.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2395_nr_5F2426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2395_nr_5F2426 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9967 (s : N.State) (i : N.Inputs) :
  R.v9967 (state s) (inputs i) = Zmod.unsigned (N.v9967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9967 s i)) at 1.
  unfold R.v9967, N.v9967.
  rewrite ?node_9809.
  rewrite ?node_9812.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9968 (s : N.State) (i : N.Inputs) :
  R.v9968 (state s) (inputs i) = Zmod.unsigned (N.v9968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9968 s i)) at 1.
  unfold R.v9968, N.v9968.
  rewrite ?node_9967.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2396_nr_5F2427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2396_nr_5F2427 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9969 (s : N.State) (i : N.Inputs) :
  R.v9969 (state s) (inputs i) = Zmod.unsigned (N.v9969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9969 s i)) at 1.
  unfold R.v9969, N.v9969.
  rewrite !state_r1054_nr_5F1054.
  rewrite !state_r1055_nr_5F1055.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1054_nr_5F1054 s)).
  rewrite ?(bits.mod_to_Z (N.r1055_nr_5F1055 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9970 (s : N.State) (i : N.Inputs) :
  R.v9970 (state s) (inputs i) = Zmod.unsigned (N.v9970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9970 s i)) at 1.
  unfold R.v9970, N.v9970.
  rewrite ?node_9969.
  rewrite !state_r1056_nr_5F1056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1056_nr_5F1056 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9971 (s : N.State) (i : N.Inputs) :
  R.v9971 (state s) (inputs i) = Zmod.unsigned (N.v9971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9971 s i)) at 1.
  unfold R.v9971, N.v9971.
  rewrite ?node_9970.
  rewrite !state_r1057_nr_5F1057.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1057_nr_5F1057 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9972 (s : N.State) (i : N.Inputs) :
  R.v9972 (state s) (inputs i) = Zmod.unsigned (N.v9972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9972 s i)) at 1.
  unfold R.v9972, N.v9972.
  rewrite !state_r1022_nr_5F1022.
  rewrite !state_r1023_nr_5F1023.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1022_nr_5F1022 s)).
  rewrite ?(bits.mod_to_Z (N.r1023_nr_5F1023 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9973 (s : N.State) (i : N.Inputs) :
  R.v9973 (state s) (inputs i) = Zmod.unsigned (N.v9973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9973 s i)) at 1.
  unfold R.v9973, N.v9973.
  rewrite ?node_9817.
  rewrite !state_r1024_nr_5F1024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1024_nr_5F1024 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9974 (s : N.State) (i : N.Inputs) :
  R.v9974 (state s) (inputs i) = Zmod.unsigned (N.v9974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9974 s i)) at 1.
  unfold R.v9974, N.v9974.
  rewrite ?node_9972.
  rewrite ?node_9973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9975 (s : N.State) (i : N.Inputs) :
  R.v9975 (state s) (inputs i) = Zmod.unsigned (N.v9975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9975 s i)) at 1.
  unfold R.v9975, N.v9975.
  rewrite ?node_9971.
  rewrite ?node_9974.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9976 (s : N.State) (i : N.Inputs) :
  R.v9976 (state s) (inputs i) = Zmod.unsigned (N.v9976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9976 s i)) at 1.
  unfold R.v9976, N.v9976.
  rewrite !state_r1058_nr_5F1058.
  rewrite !state_r1059_nr_5F1059.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1058_nr_5F1058 s)).
  rewrite ?(bits.mod_to_Z (N.r1059_nr_5F1059 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9977 (s : N.State) (i : N.Inputs) :
  R.v9977 (state s) (inputs i) = Zmod.unsigned (N.v9977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9977 s i)) at 1.
  unfold R.v9977, N.v9977.
  rewrite ?node_9976.
  rewrite !state_r1060_nr_5F1060.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1060_nr_5F1060 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9978 (s : N.State) (i : N.Inputs) :
  R.v9978 (state s) (inputs i) = Zmod.unsigned (N.v9978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9978 s i)) at 1.
  unfold R.v9978, N.v9978.
  rewrite ?node_9977.
  rewrite !state_r1061_nr_5F1061.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1061_nr_5F1061 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9979 (s : N.State) (i : N.Inputs) :
  R.v9979 (state s) (inputs i) = Zmod.unsigned (N.v9979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9979 s i)) at 1.
  unfold R.v9979, N.v9979.
  rewrite !state_r1026_nr_5F1026.
  rewrite !state_r1027_nr_5F1027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1026_nr_5F1026 s)).
  rewrite ?(bits.mod_to_Z (N.r1027_nr_5F1027 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9980 (s : N.State) (i : N.Inputs) :
  R.v9980 (state s) (inputs i) = Zmod.unsigned (N.v9980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9980 s i)) at 1.
  unfold R.v9980, N.v9980.
  rewrite ?node_9824.
  rewrite !state_r1028_nr_5F1028.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1028_nr_5F1028 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9981 (s : N.State) (i : N.Inputs) :
  R.v9981 (state s) (inputs i) = Zmod.unsigned (N.v9981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9981 s i)) at 1.
  unfold R.v9981, N.v9981.
  rewrite ?node_9979.
  rewrite ?node_9980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9982 (s : N.State) (i : N.Inputs) :
  R.v9982 (state s) (inputs i) = Zmod.unsigned (N.v9982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9982 s i)) at 1.
  unfold R.v9982, N.v9982.
  rewrite ?node_9978.
  rewrite ?node_9981.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9983 (s : N.State) (i : N.Inputs) :
  R.v9983 (state s) (inputs i) = Zmod.unsigned (N.v9983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9983 s i)) at 1.
  unfold R.v9983, N.v9983.
  rewrite ?node_9975.
  rewrite ?node_9982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9984 (s : N.State) (i : N.Inputs) :
  R.v9984 (state s) (inputs i) = Zmod.unsigned (N.v9984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9984 s i)) at 1.
  unfold R.v9984, N.v9984.
  rewrite !state_r1062_nr_5F1062.
  rewrite !state_r1063_nr_5F1063.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1062_nr_5F1062 s)).
  rewrite ?(bits.mod_to_Z (N.r1063_nr_5F1063 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9985 (s : N.State) (i : N.Inputs) :
  R.v9985 (state s) (inputs i) = Zmod.unsigned (N.v9985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9985 s i)) at 1.
  unfold R.v9985, N.v9985.
  rewrite ?node_9984.
  rewrite !state_r1064_nr_5F1064.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1064_nr_5F1064 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9986 (s : N.State) (i : N.Inputs) :
  R.v9986 (state s) (inputs i) = Zmod.unsigned (N.v9986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9986 s i)) at 1.
  unfold R.v9986, N.v9986.
  rewrite ?node_9985.
  rewrite !state_r1065_nr_5F1065.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1065_nr_5F1065 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9987 (s : N.State) (i : N.Inputs) :
  R.v9987 (state s) (inputs i) = Zmod.unsigned (N.v9987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9987 s i)) at 1.
  unfold R.v9987, N.v9987.
  rewrite !state_r1030_nr_5F1030.
  rewrite !state_r1031_nr_5F1031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1030_nr_5F1030 s)).
  rewrite ?(bits.mod_to_Z (N.r1031_nr_5F1031 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9988 (s : N.State) (i : N.Inputs) :
  R.v9988 (state s) (inputs i) = Zmod.unsigned (N.v9988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9988 s i)) at 1.
  unfold R.v9988, N.v9988.
  rewrite ?node_9832.
  rewrite !state_r1032_nr_5F1032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1032_nr_5F1032 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9989 (s : N.State) (i : N.Inputs) :
  R.v9989 (state s) (inputs i) = Zmod.unsigned (N.v9989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9989 s i)) at 1.
  unfold R.v9989, N.v9989.
  rewrite ?node_9987.
  rewrite ?node_9988.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9990 (s : N.State) (i : N.Inputs) :
  R.v9990 (state s) (inputs i) = Zmod.unsigned (N.v9990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9990 s i)) at 1.
  unfold R.v9990, N.v9990.
  rewrite ?node_9986.
  rewrite ?node_9989.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9991 (s : N.State) (i : N.Inputs) :
  R.v9991 (state s) (inputs i) = Zmod.unsigned (N.v9991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9991 s i)) at 1.
  unfold R.v9991, N.v9991.
  rewrite ?node_9983.
  rewrite ?node_9990.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9992 (s : N.State) (i : N.Inputs) :
  R.v9992 (state s) (inputs i) = Zmod.unsigned (N.v9992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9992 s i)) at 1.
  unfold R.v9992, N.v9992.
  rewrite !state_r1066_nr_5F1066.
  rewrite !state_r1067_nr_5F1067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1066_nr_5F1066 s)).
  rewrite ?(bits.mod_to_Z (N.r1067_nr_5F1067 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9993 (s : N.State) (i : N.Inputs) :
  R.v9993 (state s) (inputs i) = Zmod.unsigned (N.v9993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9993 s i)) at 1.
  unfold R.v9993, N.v9993.
  rewrite ?node_9992.
  rewrite !state_r1068_nr_5F1068.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1068_nr_5F1068 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9994 (s : N.State) (i : N.Inputs) :
  R.v9994 (state s) (inputs i) = Zmod.unsigned (N.v9994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9994 s i)) at 1.
  unfold R.v9994, N.v9994.
  rewrite ?node_9993.
  rewrite !state_r1069_nr_5F1069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1069_nr_5F1069 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9995 (s : N.State) (i : N.Inputs) :
  R.v9995 (state s) (inputs i) = Zmod.unsigned (N.v9995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9995 s i)) at 1.
  unfold R.v9995, N.v9995.
  rewrite !state_r1034_nr_5F1034.
  rewrite !state_r1035_nr_5F1035.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1034_nr_5F1034 s)).
  rewrite ?(bits.mod_to_Z (N.r1035_nr_5F1035 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9996 (s : N.State) (i : N.Inputs) :
  R.v9996 (state s) (inputs i) = Zmod.unsigned (N.v9996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9996 s i)) at 1.
  unfold R.v9996, N.v9996.
  rewrite ?node_9840.
  rewrite !state_r1036_nr_5F1036.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1036_nr_5F1036 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9997 (s : N.State) (i : N.Inputs) :
  R.v9997 (state s) (inputs i) = Zmod.unsigned (N.v9997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9997 s i)) at 1.
  unfold R.v9997, N.v9997.
  rewrite ?node_9995.
  rewrite ?node_9996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9998 (s : N.State) (i : N.Inputs) :
  R.v9998 (state s) (inputs i) = Zmod.unsigned (N.v9998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9998 s i)) at 1.
  unfold R.v9998, N.v9998.
  rewrite ?node_9994.
  rewrite ?node_9997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9999 (s : N.State) (i : N.Inputs) :
  R.v9999 (state s) (inputs i) = Zmod.unsigned (N.v9999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9999 s i)) at 1.
  unfold R.v9999, N.v9999.
  rewrite ?node_9991.
  rewrite ?node_9998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
