(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes000.
Lemma node_1000 (s : N.State) (i : N.Inputs) :
  R.v1000 (state s) (inputs i) = Zmod.unsigned (N.v1000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1000 s i)) at 1.
  unfold R.v1000, N.v1000.
  rewrite ?node_999.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r357_nr_5F357.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r357_nr_5F357 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1001 (s : N.State) (i : N.Inputs) :
  R.v1001 (state s) (inputs i) = Zmod.unsigned (N.v1001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1001 s i)) at 1.
  unfold R.v1001, N.v1001.
  unfold R.v6, N.v6.
  rewrite ?node_990.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1002 (s : N.State) (i : N.Inputs) :
  R.v1002 (state s) (inputs i) = Zmod.unsigned (N.v1002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1002 s i)) at 1.
  unfold R.v1002, N.v1002.
  unfold R.v19, N.v19.
  rewrite ?node_989.
  rewrite ?node_1001.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1003 (s : N.State) (i : N.Inputs) :
  R.v1003 (state s) (inputs i) = Zmod.unsigned (N.v1003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1003 s i)) at 1.
  unfold R.v1003, N.v1003.
  rewrite ?node_1002.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1004 (s : N.State) (i : N.Inputs) :
  R.v1004 (state s) (inputs i) = Zmod.unsigned (N.v1004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1004 s i)) at 1.
  unfold R.v1004, N.v1004.
  rewrite ?node_1003.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r358_nr_5F358.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r358_nr_5F358 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1005 (s : N.State) (i : N.Inputs) :
  R.v1005 (state s) (inputs i) = Zmod.unsigned (N.v1005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1005 s i)) at 1.
  unfold R.v1005, N.v1005.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1006 (s : N.State) (i : N.Inputs) :
  R.v1006 (state s) (inputs i) = Zmod.unsigned (N.v1006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1006 s i)) at 1.
  unfold R.v1006, N.v1006.
  rewrite ?node_1005.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r359_nr_5F359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r359_nr_5F359 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1007 (s : N.State) (i : N.Inputs) :
  R.v1007 (state s) (inputs i) = Zmod.unsigned (N.v1007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1007 s i)) at 1.
  unfold R.v1007, N.v1007.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1008 (s : N.State) (i : N.Inputs) :
  R.v1008 (state s) (inputs i) = Zmod.unsigned (N.v1008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1008 s i)) at 1.
  unfold R.v1008, N.v1008.
  rewrite ?node_1007.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r360_nr_5F360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r360_nr_5F360 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1009 (s : N.State) (i : N.Inputs) :
  R.v1009 (state s) (inputs i) = Zmod.unsigned (N.v1009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1009 s i)) at 1.
  unfold R.v1009, N.v1009.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1010 (s : N.State) (i : N.Inputs) :
  R.v1010 (state s) (inputs i) = Zmod.unsigned (N.v1010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1010 s i)) at 1.
  unfold R.v1010, N.v1010.
  rewrite ?node_1009.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r361_nr_5F361.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r361_nr_5F361 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1011 (s : N.State) (i : N.Inputs) :
  R.v1011 (state s) (inputs i) = Zmod.unsigned (N.v1011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1011 s i)) at 1.
  unfold R.v1011, N.v1011.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1012 (s : N.State) (i : N.Inputs) :
  R.v1012 (state s) (inputs i) = Zmod.unsigned (N.v1012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1012 s i)) at 1.
  unfold R.v1012, N.v1012.
  rewrite ?node_1011.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r362_nr_5F362.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r362_nr_5F362 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1013 (s : N.State) (i : N.Inputs) :
  R.v1013 (state s) (inputs i) = Zmod.unsigned (N.v1013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1013 s i)) at 1.
  unfold R.v1013, N.v1013.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1014 (s : N.State) (i : N.Inputs) :
  R.v1014 (state s) (inputs i) = Zmod.unsigned (N.v1014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1014 s i)) at 1.
  unfold R.v1014, N.v1014.
  rewrite ?node_1013.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r363_nr_5F363.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r363_nr_5F363 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1015 (s : N.State) (i : N.Inputs) :
  R.v1015 (state s) (inputs i) = Zmod.unsigned (N.v1015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1015 s i)) at 1.
  unfold R.v1015, N.v1015.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1016 (s : N.State) (i : N.Inputs) :
  R.v1016 (state s) (inputs i) = Zmod.unsigned (N.v1016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1016 s i)) at 1.
  unfold R.v1016, N.v1016.
  rewrite ?node_1015.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r364_nr_5F364.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r364_nr_5F364 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1017 (s : N.State) (i : N.Inputs) :
  R.v1017 (state s) (inputs i) = Zmod.unsigned (N.v1017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1017 s i)) at 1.
  unfold R.v1017, N.v1017.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1018 (s : N.State) (i : N.Inputs) :
  R.v1018 (state s) (inputs i) = Zmod.unsigned (N.v1018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1018 s i)) at 1.
  unfold R.v1018, N.v1018.
  rewrite ?node_1017.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r365_nr_5F365.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r365_nr_5F365 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1019 (s : N.State) (i : N.Inputs) :
  R.v1019 (state s) (inputs i) = Zmod.unsigned (N.v1019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1019 s i)) at 1.
  unfold R.v1019, N.v1019.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1020 (s : N.State) (i : N.Inputs) :
  R.v1020 (state s) (inputs i) = Zmod.unsigned (N.v1020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1020 s i)) at 1.
  unfold R.v1020, N.v1020.
  rewrite ?node_1019.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r366_nr_5F366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r366_nr_5F366 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1021 (s : N.State) (i : N.Inputs) :
  R.v1021 (state s) (inputs i) = Zmod.unsigned (N.v1021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1021 s i)) at 1.
  unfold R.v1021, N.v1021.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1022 (s : N.State) (i : N.Inputs) :
  R.v1022 (state s) (inputs i) = Zmod.unsigned (N.v1022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1022 s i)) at 1.
  unfold R.v1022, N.v1022.
  rewrite ?node_1021.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r367_nr_5F367.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r367_nr_5F367 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1023 (s : N.State) (i : N.Inputs) :
  R.v1023 (state s) (inputs i) = Zmod.unsigned (N.v1023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1023 s i)) at 1.
  unfold R.v1023, N.v1023.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1024 (s : N.State) (i : N.Inputs) :
  R.v1024 (state s) (inputs i) = Zmod.unsigned (N.v1024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1024 s i)) at 1.
  unfold R.v1024, N.v1024.
  rewrite ?node_1023.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r368_nr_5F368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r368_nr_5F368 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1025 (s : N.State) (i : N.Inputs) :
  R.v1025 (state s) (inputs i) = Zmod.unsigned (N.v1025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1025 s i)) at 1.
  unfold R.v1025, N.v1025.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1026 (s : N.State) (i : N.Inputs) :
  R.v1026 (state s) (inputs i) = Zmod.unsigned (N.v1026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1026 s i)) at 1.
  unfold R.v1026, N.v1026.
  rewrite ?node_1025.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r369_nr_5F369.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r369_nr_5F369 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1027 (s : N.State) (i : N.Inputs) :
  R.v1027 (state s) (inputs i) = Zmod.unsigned (N.v1027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1027 s i)) at 1.
  unfold R.v1027, N.v1027.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1028 (s : N.State) (i : N.Inputs) :
  R.v1028 (state s) (inputs i) = Zmod.unsigned (N.v1028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1028 s i)) at 1.
  unfold R.v1028, N.v1028.
  rewrite ?node_1027.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r370_nr_5F370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r370_nr_5F370 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1029 (s : N.State) (i : N.Inputs) :
  R.v1029 (state s) (inputs i) = Zmod.unsigned (N.v1029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1029 s i)) at 1.
  unfold R.v1029, N.v1029.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1030 (s : N.State) (i : N.Inputs) :
  R.v1030 (state s) (inputs i) = Zmod.unsigned (N.v1030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1030 s i)) at 1.
  unfold R.v1030, N.v1030.
  rewrite ?node_1029.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r371_nr_5F371.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r371_nr_5F371 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1031 (s : N.State) (i : N.Inputs) :
  R.v1031 (state s) (inputs i) = Zmod.unsigned (N.v1031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1031 s i)) at 1.
  unfold R.v1031, N.v1031.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1032 (s : N.State) (i : N.Inputs) :
  R.v1032 (state s) (inputs i) = Zmod.unsigned (N.v1032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1032 s i)) at 1.
  unfold R.v1032, N.v1032.
  rewrite ?node_1031.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r372_nr_5F372.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r372_nr_5F372 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1033 (s : N.State) (i : N.Inputs) :
  R.v1033 (state s) (inputs i) = Zmod.unsigned (N.v1033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1033 s i)) at 1.
  unfold R.v1033, N.v1033.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1034 (s : N.State) (i : N.Inputs) :
  R.v1034 (state s) (inputs i) = Zmod.unsigned (N.v1034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1034 s i)) at 1.
  unfold R.v1034, N.v1034.
  rewrite ?node_1033.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r373_nr_5F373.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r373_nr_5F373 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1035 (s : N.State) (i : N.Inputs) :
  R.v1035 (state s) (inputs i) = Zmod.unsigned (N.v1035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1035 s i)) at 1.
  unfold R.v1035, N.v1035.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1036 (s : N.State) (i : N.Inputs) :
  R.v1036 (state s) (inputs i) = Zmod.unsigned (N.v1036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1036 s i)) at 1.
  unfold R.v1036, N.v1036.
  rewrite ?node_1035.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r374_nr_5F374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r374_nr_5F374 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1037 (s : N.State) (i : N.Inputs) :
  R.v1037 (state s) (inputs i) = Zmod.unsigned (N.v1037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1037 s i)) at 1.
  unfold R.v1037, N.v1037.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1038 (s : N.State) (i : N.Inputs) :
  R.v1038 (state s) (inputs i) = Zmod.unsigned (N.v1038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1038 s i)) at 1.
  unfold R.v1038, N.v1038.
  rewrite ?node_1037.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r375_nr_5F375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r375_nr_5F375 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1039 (s : N.State) (i : N.Inputs) :
  R.v1039 (state s) (inputs i) = Zmod.unsigned (N.v1039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1039 s i)) at 1.
  unfold R.v1039, N.v1039.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1040 (s : N.State) (i : N.Inputs) :
  R.v1040 (state s) (inputs i) = Zmod.unsigned (N.v1040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1040 s i)) at 1.
  unfold R.v1040, N.v1040.
  rewrite ?node_1039.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r376_nr_5F376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r376_nr_5F376 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1041 (s : N.State) (i : N.Inputs) :
  R.v1041 (state s) (inputs i) = Zmod.unsigned (N.v1041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1041 s i)) at 1.
  unfold R.v1041, N.v1041.
  rewrite ?node_1002.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1042 (s : N.State) (i : N.Inputs) :
  R.v1042 (state s) (inputs i) = Zmod.unsigned (N.v1042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1042 s i)) at 1.
  unfold R.v1042, N.v1042.
  rewrite ?node_1041.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r377_nr_5F377.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r377_nr_5F377 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1043 (s : N.State) (i : N.Inputs) :
  R.v1043 (state s) (inputs i) = Zmod.unsigned (N.v1043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1043 s i)) at 1.
  unfold R.v1043, N.v1043.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1044 (s : N.State) (i : N.Inputs) :
  R.v1044 (state s) (inputs i) = Zmod.unsigned (N.v1044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1044 s i)) at 1.
  unfold R.v1044, N.v1044.
  rewrite ?node_1043.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r378_nr_5F378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r378_nr_5F378 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1045 (s : N.State) (i : N.Inputs) :
  R.v1045 (state s) (inputs i) = Zmod.unsigned (N.v1045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1045 s i)) at 1.
  unfold R.v1045, N.v1045.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1046 (s : N.State) (i : N.Inputs) :
  R.v1046 (state s) (inputs i) = Zmod.unsigned (N.v1046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1046 s i)) at 1.
  unfold R.v1046, N.v1046.
  rewrite ?node_1045.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r379_nr_5F379.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r379_nr_5F379 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1047 (s : N.State) (i : N.Inputs) :
  R.v1047 (state s) (inputs i) = Zmod.unsigned (N.v1047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1047 s i)) at 1.
  unfold R.v1047, N.v1047.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1048 (s : N.State) (i : N.Inputs) :
  R.v1048 (state s) (inputs i) = Zmod.unsigned (N.v1048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1048 s i)) at 1.
  unfold R.v1048, N.v1048.
  rewrite ?node_1047.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r380_nr_5F380.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r380_nr_5F380 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1049 (s : N.State) (i : N.Inputs) :
  R.v1049 (state s) (inputs i) = Zmod.unsigned (N.v1049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1049 s i)) at 1.
  unfold R.v1049, N.v1049.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1050 (s : N.State) (i : N.Inputs) :
  R.v1050 (state s) (inputs i) = Zmod.unsigned (N.v1050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1050 s i)) at 1.
  unfold R.v1050, N.v1050.
  rewrite ?node_1049.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r381_nr_5F381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r381_nr_5F381 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1051 (s : N.State) (i : N.Inputs) :
  R.v1051 (state s) (inputs i) = Zmod.unsigned (N.v1051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1051 s i)) at 1.
  unfold R.v1051, N.v1051.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1052 (s : N.State) (i : N.Inputs) :
  R.v1052 (state s) (inputs i) = Zmod.unsigned (N.v1052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1052 s i)) at 1.
  unfold R.v1052, N.v1052.
  rewrite ?node_1051.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r382_nr_5F382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r382_nr_5F382 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1053 (s : N.State) (i : N.Inputs) :
  R.v1053 (state s) (inputs i) = Zmod.unsigned (N.v1053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1053 s i)) at 1.
  unfold R.v1053, N.v1053.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1054 (s : N.State) (i : N.Inputs) :
  R.v1054 (state s) (inputs i) = Zmod.unsigned (N.v1054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1054 s i)) at 1.
  unfold R.v1054, N.v1054.
  rewrite ?node_1053.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r383_nr_5F383.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r383_nr_5F383 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1055 (s : N.State) (i : N.Inputs) :
  R.v1055 (state s) (inputs i) = Zmod.unsigned (N.v1055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1055 s i)) at 1.
  unfold R.v1055, N.v1055.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1056 (s : N.State) (i : N.Inputs) :
  R.v1056 (state s) (inputs i) = Zmod.unsigned (N.v1056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1056 s i)) at 1.
  unfold R.v1056, N.v1056.
  rewrite ?node_1055.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r384_nr_5F384.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r384_nr_5F384 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1057 (s : N.State) (i : N.Inputs) :
  R.v1057 (state s) (inputs i) = Zmod.unsigned (N.v1057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1057 s i)) at 1.
  unfold R.v1057, N.v1057.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1058 (s : N.State) (i : N.Inputs) :
  R.v1058 (state s) (inputs i) = Zmod.unsigned (N.v1058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1058 s i)) at 1.
  unfold R.v1058, N.v1058.
  rewrite ?node_1057.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r385_nr_5F385.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r385_nr_5F385 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1059 (s : N.State) (i : N.Inputs) :
  R.v1059 (state s) (inputs i) = Zmod.unsigned (N.v1059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1059 s i)) at 1.
  unfold R.v1059, N.v1059.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1060 (s : N.State) (i : N.Inputs) :
  R.v1060 (state s) (inputs i) = Zmod.unsigned (N.v1060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1060 s i)) at 1.
  unfold R.v1060, N.v1060.
  rewrite ?node_1059.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r386_nr_5F386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r386_nr_5F386 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1061 (s : N.State) (i : N.Inputs) :
  R.v1061 (state s) (inputs i) = Zmod.unsigned (N.v1061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1061 s i)) at 1.
  unfold R.v1061, N.v1061.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1062 (s : N.State) (i : N.Inputs) :
  R.v1062 (state s) (inputs i) = Zmod.unsigned (N.v1062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1062 s i)) at 1.
  unfold R.v1062, N.v1062.
  rewrite ?node_1061.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r387_nr_5F387.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r387_nr_5F387 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1063 (s : N.State) (i : N.Inputs) :
  R.v1063 (state s) (inputs i) = Zmod.unsigned (N.v1063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1063 s i)) at 1.
  unfold R.v1063, N.v1063.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1064 (s : N.State) (i : N.Inputs) :
  R.v1064 (state s) (inputs i) = Zmod.unsigned (N.v1064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1064 s i)) at 1.
  unfold R.v1064, N.v1064.
  rewrite ?node_1063.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r388_nr_5F388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r388_nr_5F388 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1065 (s : N.State) (i : N.Inputs) :
  R.v1065 (state s) (inputs i) = Zmod.unsigned (N.v1065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1065 s i)) at 1.
  unfold R.v1065, N.v1065.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1066 (s : N.State) (i : N.Inputs) :
  R.v1066 (state s) (inputs i) = Zmod.unsigned (N.v1066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1066 s i)) at 1.
  unfold R.v1066, N.v1066.
  rewrite ?node_1065.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r389_nr_5F389.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r389_nr_5F389 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1067 (s : N.State) (i : N.Inputs) :
  R.v1067 (state s) (inputs i) = Zmod.unsigned (N.v1067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1067 s i)) at 1.
  unfold R.v1067, N.v1067.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1068 (s : N.State) (i : N.Inputs) :
  R.v1068 (state s) (inputs i) = Zmod.unsigned (N.v1068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1068 s i)) at 1.
  unfold R.v1068, N.v1068.
  rewrite ?node_1067.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r390_nr_5F390.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r390_nr_5F390 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1069 (s : N.State) (i : N.Inputs) :
  R.v1069 (state s) (inputs i) = Zmod.unsigned (N.v1069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1069 s i)) at 1.
  unfold R.v1069, N.v1069.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1070 (s : N.State) (i : N.Inputs) :
  R.v1070 (state s) (inputs i) = Zmod.unsigned (N.v1070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1070 s i)) at 1.
  unfold R.v1070, N.v1070.
  rewrite ?node_1069.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r391_nr_5F391.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r391_nr_5F391 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1071 (s : N.State) (i : N.Inputs) :
  R.v1071 (state s) (inputs i) = Zmod.unsigned (N.v1071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1071 s i)) at 1.
  unfold R.v1071, N.v1071.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1072 (s : N.State) (i : N.Inputs) :
  R.v1072 (state s) (inputs i) = Zmod.unsigned (N.v1072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1072 s i)) at 1.
  unfold R.v1072, N.v1072.
  rewrite ?node_1071.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r392_nr_5F392.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r392_nr_5F392 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1073 (s : N.State) (i : N.Inputs) :
  R.v1073 (state s) (inputs i) = Zmod.unsigned (N.v1073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1073 s i)) at 1.
  unfold R.v1073, N.v1073.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1074 (s : N.State) (i : N.Inputs) :
  R.v1074 (state s) (inputs i) = Zmod.unsigned (N.v1074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1074 s i)) at 1.
  unfold R.v1074, N.v1074.
  rewrite ?node_1073.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r393_nr_5F393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r393_nr_5F393 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1075 (s : N.State) (i : N.Inputs) :
  R.v1075 (state s) (inputs i) = Zmod.unsigned (N.v1075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1075 s i)) at 1.
  unfold R.v1075, N.v1075.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1076 (s : N.State) (i : N.Inputs) :
  R.v1076 (state s) (inputs i) = Zmod.unsigned (N.v1076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1076 s i)) at 1.
  unfold R.v1076, N.v1076.
  rewrite ?node_1075.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r394_nr_5F394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r394_nr_5F394 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1077 (s : N.State) (i : N.Inputs) :
  R.v1077 (state s) (inputs i) = Zmod.unsigned (N.v1077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1077 s i)) at 1.
  unfold R.v1077, N.v1077.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1078 (s : N.State) (i : N.Inputs) :
  R.v1078 (state s) (inputs i) = Zmod.unsigned (N.v1078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1078 s i)) at 1.
  unfold R.v1078, N.v1078.
  rewrite ?node_1077.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r395_nr_5F395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r395_nr_5F395 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1079 (s : N.State) (i : N.Inputs) :
  R.v1079 (state s) (inputs i) = Zmod.unsigned (N.v1079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1079 s i)) at 1.
  unfold R.v1079, N.v1079.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1080 (s : N.State) (i : N.Inputs) :
  R.v1080 (state s) (inputs i) = Zmod.unsigned (N.v1080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1080 s i)) at 1.
  unfold R.v1080, N.v1080.
  unfold R.v33, N.v33.
  rewrite ?node_1079.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1081 (s : N.State) (i : N.Inputs) :
  R.v1081 (state s) (inputs i) = Zmod.unsigned (N.v1081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1081 s i)) at 1.
  unfold R.v1081, N.v1081.
  unfold R.v35, N.v35.
  rewrite ?node_1079.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1082 (s : N.State) (i : N.Inputs) :
  R.v1082 (state s) (inputs i) = Zmod.unsigned (N.v1082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1082 s i)) at 1.
  unfold R.v1082, N.v1082.
  rewrite ?node_1080.
  rewrite ?node_1081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1083 (s : N.State) (i : N.Inputs) :
  R.v1083 (state s) (inputs i) = Zmod.unsigned (N.v1083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1083 s i)) at 1.
  unfold R.v1083, N.v1083.
  unfold R.v39, N.v39.
  rewrite ?node_1079.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1084 (s : N.State) (i : N.Inputs) :
  R.v1084 (state s) (inputs i) = Zmod.unsigned (N.v1084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1084 s i)) at 1.
  unfold R.v1084, N.v1084.
  unfold R.v42, N.v42.
  rewrite ?node_1079.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1085 (s : N.State) (i : N.Inputs) :
  R.v1085 (state s) (inputs i) = Zmod.unsigned (N.v1085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1085 s i)) at 1.
  unfold R.v1085, N.v1085.
  unfold R.v45, N.v45.
  rewrite ?node_1079.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1086 (s : N.State) (i : N.Inputs) :
  R.v1086 (state s) (inputs i) = Zmod.unsigned (N.v1086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1086 s i)) at 1.
  unfold R.v1086, N.v1086.
  unfold R.v47, N.v47.
  rewrite ?node_1079.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1087 (s : N.State) (i : N.Inputs) :
  R.v1087 (state s) (inputs i) = Zmod.unsigned (N.v1087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1087 s i)) at 1.
  unfold R.v1087, N.v1087.
  rewrite ?node_1085.
  rewrite ?node_1086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1088 (s : N.State) (i : N.Inputs) :
  R.v1088 (state s) (inputs i) = Zmod.unsigned (N.v1088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1088 s i)) at 1.
  unfold R.v1088, N.v1088.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_1087.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1089 (s : N.State) (i : N.Inputs) :
  R.v1089 (state s) (inputs i) = Zmod.unsigned (N.v1089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1089 s i)) at 1.
  unfold R.v1089, N.v1089.
  rewrite ?node_44.
  rewrite ?node_1084.
  rewrite ?node_1088.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1090 (s : N.State) (i : N.Inputs) :
  R.v1090 (state s) (inputs i) = Zmod.unsigned (N.v1090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1090 s i)) at 1.
  unfold R.v1090, N.v1090.
  rewrite ?node_41.
  rewrite ?node_1083.
  rewrite ?node_1089.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1091 (s : N.State) (i : N.Inputs) :
  R.v1091 (state s) (inputs i) = Zmod.unsigned (N.v1091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1091 s i)) at 1.
  unfold R.v1091, N.v1091.
  rewrite ?node_38.
  rewrite ?node_1082.
  rewrite ?node_1090.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1092 (s : N.State) (i : N.Inputs) :
  R.v1092 (state s) (inputs i) = Zmod.unsigned (N.v1092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1092 s i)) at 1.
  unfold R.v1092, N.v1092.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1093 (s : N.State) (i : N.Inputs) :
  R.v1093 (state s) (inputs i) = Zmod.unsigned (N.v1093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1093 s i)) at 1.
  unfold R.v1093, N.v1093.
  rewrite ?node_1092.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r396_nr_5F396.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r396_nr_5F396 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1094 (s : N.State) (i : N.Inputs) :
  R.v1094 (state s) (inputs i) = Zmod.unsigned (N.v1094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1094 s i)) at 1.
  unfold R.v1094, N.v1094.
  unfold R.v6, N.v6.
  rewrite ?node_1083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1095 (s : N.State) (i : N.Inputs) :
  R.v1095 (state s) (inputs i) = Zmod.unsigned (N.v1095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1095 s i)) at 1.
  unfold R.v1095, N.v1095.
  unfold R.v19, N.v19.
  rewrite ?node_1082.
  rewrite ?node_1094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1096 (s : N.State) (i : N.Inputs) :
  R.v1096 (state s) (inputs i) = Zmod.unsigned (N.v1096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1096 s i)) at 1.
  unfold R.v1096, N.v1096.
  rewrite ?node_1095.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1097 (s : N.State) (i : N.Inputs) :
  R.v1097 (state s) (inputs i) = Zmod.unsigned (N.v1097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1097 s i)) at 1.
  unfold R.v1097, N.v1097.
  rewrite ?node_1096.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r397_nr_5F397.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r397_nr_5F397 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1098 (s : N.State) (i : N.Inputs) :
  R.v1098 (state s) (inputs i) = Zmod.unsigned (N.v1098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1098 s i)) at 1.
  unfold R.v1098, N.v1098.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1099 (s : N.State) (i : N.Inputs) :
  R.v1099 (state s) (inputs i) = Zmod.unsigned (N.v1099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1099 s i)) at 1.
  unfold R.v1099, N.v1099.
  rewrite ?node_1098.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r398_nr_5F398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r398_nr_5F398 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1100 (s : N.State) (i : N.Inputs) :
  R.v1100 (state s) (inputs i) = Zmod.unsigned (N.v1100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1100 s i)) at 1.
  unfold R.v1100, N.v1100.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1101 (s : N.State) (i : N.Inputs) :
  R.v1101 (state s) (inputs i) = Zmod.unsigned (N.v1101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1101 s i)) at 1.
  unfold R.v1101, N.v1101.
  rewrite ?node_1100.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r399_nr_5F399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r399_nr_5F399 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1102 (s : N.State) (i : N.Inputs) :
  R.v1102 (state s) (inputs i) = Zmod.unsigned (N.v1102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1102 s i)) at 1.
  unfold R.v1102, N.v1102.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1103 (s : N.State) (i : N.Inputs) :
  R.v1103 (state s) (inputs i) = Zmod.unsigned (N.v1103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1103 s i)) at 1.
  unfold R.v1103, N.v1103.
  rewrite ?node_1102.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r400_nr_5F400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r400_nr_5F400 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1104 (s : N.State) (i : N.Inputs) :
  R.v1104 (state s) (inputs i) = Zmod.unsigned (N.v1104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1104 s i)) at 1.
  unfold R.v1104, N.v1104.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1105 (s : N.State) (i : N.Inputs) :
  R.v1105 (state s) (inputs i) = Zmod.unsigned (N.v1105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1105 s i)) at 1.
  unfold R.v1105, N.v1105.
  rewrite ?node_1104.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r401_nr_5F401.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r401_nr_5F401 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1106 (s : N.State) (i : N.Inputs) :
  R.v1106 (state s) (inputs i) = Zmod.unsigned (N.v1106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1106 s i)) at 1.
  unfold R.v1106, N.v1106.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1107 (s : N.State) (i : N.Inputs) :
  R.v1107 (state s) (inputs i) = Zmod.unsigned (N.v1107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1107 s i)) at 1.
  unfold R.v1107, N.v1107.
  rewrite ?node_1106.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r402_nr_5F402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r402_nr_5F402 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1108 (s : N.State) (i : N.Inputs) :
  R.v1108 (state s) (inputs i) = Zmod.unsigned (N.v1108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1108 s i)) at 1.
  unfold R.v1108, N.v1108.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1109 (s : N.State) (i : N.Inputs) :
  R.v1109 (state s) (inputs i) = Zmod.unsigned (N.v1109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1109 s i)) at 1.
  unfold R.v1109, N.v1109.
  rewrite ?node_1108.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r403_nr_5F403.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r403_nr_5F403 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1110 (s : N.State) (i : N.Inputs) :
  R.v1110 (state s) (inputs i) = Zmod.unsigned (N.v1110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1110 s i)) at 1.
  unfold R.v1110, N.v1110.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1111 (s : N.State) (i : N.Inputs) :
  R.v1111 (state s) (inputs i) = Zmod.unsigned (N.v1111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1111 s i)) at 1.
  unfold R.v1111, N.v1111.
  rewrite ?node_1110.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r404_nr_5F404.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r404_nr_5F404 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1112 (s : N.State) (i : N.Inputs) :
  R.v1112 (state s) (inputs i) = Zmod.unsigned (N.v1112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1112 s i)) at 1.
  unfold R.v1112, N.v1112.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1113 (s : N.State) (i : N.Inputs) :
  R.v1113 (state s) (inputs i) = Zmod.unsigned (N.v1113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1113 s i)) at 1.
  unfold R.v1113, N.v1113.
  rewrite ?node_1112.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r405_nr_5F405.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r405_nr_5F405 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1114 (s : N.State) (i : N.Inputs) :
  R.v1114 (state s) (inputs i) = Zmod.unsigned (N.v1114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1114 s i)) at 1.
  unfold R.v1114, N.v1114.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1115 (s : N.State) (i : N.Inputs) :
  R.v1115 (state s) (inputs i) = Zmod.unsigned (N.v1115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1115 s i)) at 1.
  unfold R.v1115, N.v1115.
  rewrite ?node_1114.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r406_nr_5F406.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r406_nr_5F406 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1116 (s : N.State) (i : N.Inputs) :
  R.v1116 (state s) (inputs i) = Zmod.unsigned (N.v1116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1116 s i)) at 1.
  unfold R.v1116, N.v1116.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1117 (s : N.State) (i : N.Inputs) :
  R.v1117 (state s) (inputs i) = Zmod.unsigned (N.v1117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1117 s i)) at 1.
  unfold R.v1117, N.v1117.
  rewrite ?node_1116.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r407_nr_5F407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r407_nr_5F407 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1118 (s : N.State) (i : N.Inputs) :
  R.v1118 (state s) (inputs i) = Zmod.unsigned (N.v1118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1118 s i)) at 1.
  unfold R.v1118, N.v1118.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1119 (s : N.State) (i : N.Inputs) :
  R.v1119 (state s) (inputs i) = Zmod.unsigned (N.v1119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1119 s i)) at 1.
  unfold R.v1119, N.v1119.
  rewrite ?node_1118.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r408_nr_5F408.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r408_nr_5F408 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1120 (s : N.State) (i : N.Inputs) :
  R.v1120 (state s) (inputs i) = Zmod.unsigned (N.v1120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1120 s i)) at 1.
  unfold R.v1120, N.v1120.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1121 (s : N.State) (i : N.Inputs) :
  R.v1121 (state s) (inputs i) = Zmod.unsigned (N.v1121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1121 s i)) at 1.
  unfold R.v1121, N.v1121.
  rewrite ?node_1120.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r409_nr_5F409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r409_nr_5F409 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1122 (s : N.State) (i : N.Inputs) :
  R.v1122 (state s) (inputs i) = Zmod.unsigned (N.v1122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1122 s i)) at 1.
  unfold R.v1122, N.v1122.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1123 (s : N.State) (i : N.Inputs) :
  R.v1123 (state s) (inputs i) = Zmod.unsigned (N.v1123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1123 s i)) at 1.
  unfold R.v1123, N.v1123.
  rewrite ?node_1122.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r410_nr_5F410.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r410_nr_5F410 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1124 (s : N.State) (i : N.Inputs) :
  R.v1124 (state s) (inputs i) = Zmod.unsigned (N.v1124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1124 s i)) at 1.
  unfold R.v1124, N.v1124.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1125 (s : N.State) (i : N.Inputs) :
  R.v1125 (state s) (inputs i) = Zmod.unsigned (N.v1125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1125 s i)) at 1.
  unfold R.v1125, N.v1125.
  rewrite ?node_1124.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r411_nr_5F411.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r411_nr_5F411 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1126 (s : N.State) (i : N.Inputs) :
  R.v1126 (state s) (inputs i) = Zmod.unsigned (N.v1126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1126 s i)) at 1.
  unfold R.v1126, N.v1126.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1127 (s : N.State) (i : N.Inputs) :
  R.v1127 (state s) (inputs i) = Zmod.unsigned (N.v1127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1127 s i)) at 1.
  unfold R.v1127, N.v1127.
  rewrite ?node_1126.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r412_nr_5F412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r412_nr_5F412 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1128 (s : N.State) (i : N.Inputs) :
  R.v1128 (state s) (inputs i) = Zmod.unsigned (N.v1128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1128 s i)) at 1.
  unfold R.v1128, N.v1128.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1129 (s : N.State) (i : N.Inputs) :
  R.v1129 (state s) (inputs i) = Zmod.unsigned (N.v1129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1129 s i)) at 1.
  unfold R.v1129, N.v1129.
  rewrite ?node_1128.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r413_nr_5F413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r413_nr_5F413 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1130 (s : N.State) (i : N.Inputs) :
  R.v1130 (state s) (inputs i) = Zmod.unsigned (N.v1130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1130 s i)) at 1.
  unfold R.v1130, N.v1130.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1131 (s : N.State) (i : N.Inputs) :
  R.v1131 (state s) (inputs i) = Zmod.unsigned (N.v1131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1131 s i)) at 1.
  unfold R.v1131, N.v1131.
  rewrite ?node_1130.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r414_nr_5F414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r414_nr_5F414 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1132 (s : N.State) (i : N.Inputs) :
  R.v1132 (state s) (inputs i) = Zmod.unsigned (N.v1132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1132 s i)) at 1.
  unfold R.v1132, N.v1132.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1133 (s : N.State) (i : N.Inputs) :
  R.v1133 (state s) (inputs i) = Zmod.unsigned (N.v1133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1133 s i)) at 1.
  unfold R.v1133, N.v1133.
  rewrite ?node_1132.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r415_nr_5F415.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r415_nr_5F415 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1134 (s : N.State) (i : N.Inputs) :
  R.v1134 (state s) (inputs i) = Zmod.unsigned (N.v1134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1134 s i)) at 1.
  unfold R.v1134, N.v1134.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1135 (s : N.State) (i : N.Inputs) :
  R.v1135 (state s) (inputs i) = Zmod.unsigned (N.v1135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1135 s i)) at 1.
  unfold R.v1135, N.v1135.
  rewrite ?node_1134.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r416_nr_5F416.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r416_nr_5F416 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1136 (s : N.State) (i : N.Inputs) :
  R.v1136 (state s) (inputs i) = Zmod.unsigned (N.v1136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1136 s i)) at 1.
  unfold R.v1136, N.v1136.
  rewrite ?node_1095.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1137 (s : N.State) (i : N.Inputs) :
  R.v1137 (state s) (inputs i) = Zmod.unsigned (N.v1137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1137 s i)) at 1.
  unfold R.v1137, N.v1137.
  rewrite ?node_1136.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r417_nr_5F417.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r417_nr_5F417 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1138 (s : N.State) (i : N.Inputs) :
  R.v1138 (state s) (inputs i) = Zmod.unsigned (N.v1138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1138 s i)) at 1.
  unfold R.v1138, N.v1138.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1139 (s : N.State) (i : N.Inputs) :
  R.v1139 (state s) (inputs i) = Zmod.unsigned (N.v1139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1139 s i)) at 1.
  unfold R.v1139, N.v1139.
  rewrite ?node_1138.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r418_nr_5F418.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r418_nr_5F418 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1140 (s : N.State) (i : N.Inputs) :
  R.v1140 (state s) (inputs i) = Zmod.unsigned (N.v1140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1140 s i)) at 1.
  unfold R.v1140, N.v1140.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1141 (s : N.State) (i : N.Inputs) :
  R.v1141 (state s) (inputs i) = Zmod.unsigned (N.v1141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1141 s i)) at 1.
  unfold R.v1141, N.v1141.
  rewrite ?node_1140.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r419_nr_5F419.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r419_nr_5F419 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1142 (s : N.State) (i : N.Inputs) :
  R.v1142 (state s) (inputs i) = Zmod.unsigned (N.v1142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1142 s i)) at 1.
  unfold R.v1142, N.v1142.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1143 (s : N.State) (i : N.Inputs) :
  R.v1143 (state s) (inputs i) = Zmod.unsigned (N.v1143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1143 s i)) at 1.
  unfold R.v1143, N.v1143.
  rewrite ?node_1142.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r420_nr_5F420.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r420_nr_5F420 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1144 (s : N.State) (i : N.Inputs) :
  R.v1144 (state s) (inputs i) = Zmod.unsigned (N.v1144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1144 s i)) at 1.
  unfold R.v1144, N.v1144.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1145 (s : N.State) (i : N.Inputs) :
  R.v1145 (state s) (inputs i) = Zmod.unsigned (N.v1145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1145 s i)) at 1.
  unfold R.v1145, N.v1145.
  rewrite ?node_1144.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r421_nr_5F421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r421_nr_5F421 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1146 (s : N.State) (i : N.Inputs) :
  R.v1146 (state s) (inputs i) = Zmod.unsigned (N.v1146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1146 s i)) at 1.
  unfold R.v1146, N.v1146.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1147 (s : N.State) (i : N.Inputs) :
  R.v1147 (state s) (inputs i) = Zmod.unsigned (N.v1147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1147 s i)) at 1.
  unfold R.v1147, N.v1147.
  rewrite ?node_1146.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r422_nr_5F422.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r422_nr_5F422 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1148 (s : N.State) (i : N.Inputs) :
  R.v1148 (state s) (inputs i) = Zmod.unsigned (N.v1148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1148 s i)) at 1.
  unfold R.v1148, N.v1148.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1149 (s : N.State) (i : N.Inputs) :
  R.v1149 (state s) (inputs i) = Zmod.unsigned (N.v1149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1149 s i)) at 1.
  unfold R.v1149, N.v1149.
  rewrite ?node_1148.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r423_nr_5F423.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r423_nr_5F423 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1150 (s : N.State) (i : N.Inputs) :
  R.v1150 (state s) (inputs i) = Zmod.unsigned (N.v1150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1150 s i)) at 1.
  unfold R.v1150, N.v1150.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1151 (s : N.State) (i : N.Inputs) :
  R.v1151 (state s) (inputs i) = Zmod.unsigned (N.v1151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1151 s i)) at 1.
  unfold R.v1151, N.v1151.
  rewrite ?node_1150.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r424_nr_5F424.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r424_nr_5F424 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1152 (s : N.State) (i : N.Inputs) :
  R.v1152 (state s) (inputs i) = Zmod.unsigned (N.v1152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1152 s i)) at 1.
  unfold R.v1152, N.v1152.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1153 (s : N.State) (i : N.Inputs) :
  R.v1153 (state s) (inputs i) = Zmod.unsigned (N.v1153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1153 s i)) at 1.
  unfold R.v1153, N.v1153.
  rewrite ?node_1152.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r425_nr_5F425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r425_nr_5F425 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1154 (s : N.State) (i : N.Inputs) :
  R.v1154 (state s) (inputs i) = Zmod.unsigned (N.v1154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1154 s i)) at 1.
  unfold R.v1154, N.v1154.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1155 (s : N.State) (i : N.Inputs) :
  R.v1155 (state s) (inputs i) = Zmod.unsigned (N.v1155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1155 s i)) at 1.
  unfold R.v1155, N.v1155.
  rewrite ?node_1154.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r426_nr_5F426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r426_nr_5F426 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1156 (s : N.State) (i : N.Inputs) :
  R.v1156 (state s) (inputs i) = Zmod.unsigned (N.v1156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1156 s i)) at 1.
  unfold R.v1156, N.v1156.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1157 (s : N.State) (i : N.Inputs) :
  R.v1157 (state s) (inputs i) = Zmod.unsigned (N.v1157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1157 s i)) at 1.
  unfold R.v1157, N.v1157.
  rewrite ?node_1156.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r427_nr_5F427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r427_nr_5F427 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1158 (s : N.State) (i : N.Inputs) :
  R.v1158 (state s) (inputs i) = Zmod.unsigned (N.v1158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1158 s i)) at 1.
  unfold R.v1158, N.v1158.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1159 (s : N.State) (i : N.Inputs) :
  R.v1159 (state s) (inputs i) = Zmod.unsigned (N.v1159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1159 s i)) at 1.
  unfold R.v1159, N.v1159.
  rewrite ?node_1158.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r428_nr_5F428.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r428_nr_5F428 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1160 (s : N.State) (i : N.Inputs) :
  R.v1160 (state s) (inputs i) = Zmod.unsigned (N.v1160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1160 s i)) at 1.
  unfold R.v1160, N.v1160.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1161 (s : N.State) (i : N.Inputs) :
  R.v1161 (state s) (inputs i) = Zmod.unsigned (N.v1161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1161 s i)) at 1.
  unfold R.v1161, N.v1161.
  rewrite ?node_1160.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r429_nr_5F429.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r429_nr_5F429 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1162 (s : N.State) (i : N.Inputs) :
  R.v1162 (state s) (inputs i) = Zmod.unsigned (N.v1162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1162 s i)) at 1.
  unfold R.v1162, N.v1162.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1163 (s : N.State) (i : N.Inputs) :
  R.v1163 (state s) (inputs i) = Zmod.unsigned (N.v1163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1163 s i)) at 1.
  unfold R.v1163, N.v1163.
  rewrite ?node_1162.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r430_nr_5F430.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r430_nr_5F430 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1164 (s : N.State) (i : N.Inputs) :
  R.v1164 (state s) (inputs i) = Zmod.unsigned (N.v1164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1164 s i)) at 1.
  unfold R.v1164, N.v1164.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1165 (s : N.State) (i : N.Inputs) :
  R.v1165 (state s) (inputs i) = Zmod.unsigned (N.v1165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1165 s i)) at 1.
  unfold R.v1165, N.v1165.
  rewrite ?node_1164.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r431_nr_5F431.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r431_nr_5F431 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1166 (s : N.State) (i : N.Inputs) :
  R.v1166 (state s) (inputs i) = Zmod.unsigned (N.v1166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1166 s i)) at 1.
  unfold R.v1166, N.v1166.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1167 (s : N.State) (i : N.Inputs) :
  R.v1167 (state s) (inputs i) = Zmod.unsigned (N.v1167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1167 s i)) at 1.
  unfold R.v1167, N.v1167.
  rewrite ?node_1166.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r432_nr_5F432.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r432_nr_5F432 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1168 (s : N.State) (i : N.Inputs) :
  R.v1168 (state s) (inputs i) = Zmod.unsigned (N.v1168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1168 s i)) at 1.
  unfold R.v1168, N.v1168.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1169 (s : N.State) (i : N.Inputs) :
  R.v1169 (state s) (inputs i) = Zmod.unsigned (N.v1169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1169 s i)) at 1.
  unfold R.v1169, N.v1169.
  rewrite ?node_1168.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r433_nr_5F433.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r433_nr_5F433 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1170 (s : N.State) (i : N.Inputs) :
  R.v1170 (state s) (inputs i) = Zmod.unsigned (N.v1170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1170 s i)) at 1.
  unfold R.v1170, N.v1170.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1171 (s : N.State) (i : N.Inputs) :
  R.v1171 (state s) (inputs i) = Zmod.unsigned (N.v1171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1171 s i)) at 1.
  unfold R.v1171, N.v1171.
  rewrite ?node_1170.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r434_nr_5F434.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r434_nr_5F434 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1172 (s : N.State) (i : N.Inputs) :
  R.v1172 (state s) (inputs i) = Zmod.unsigned (N.v1172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1172 s i)) at 1.
  unfold R.v1172, N.v1172.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1173 (s : N.State) (i : N.Inputs) :
  R.v1173 (state s) (inputs i) = Zmod.unsigned (N.v1173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1173 s i)) at 1.
  unfold R.v1173, N.v1173.
  rewrite ?node_1172.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r435_nr_5F435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r435_nr_5F435 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1174 (s : N.State) (i : N.Inputs) :
  R.v1174 (state s) (inputs i) = Zmod.unsigned (N.v1174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1174 s i)) at 1.
  unfold R.v1174, N.v1174.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1175 (s : N.State) (i : N.Inputs) :
  R.v1175 (state s) (inputs i) = Zmod.unsigned (N.v1175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1175 s i)) at 1.
  unfold R.v1175, N.v1175.
  rewrite ?node_1174.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r436_nr_5F436.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r436_nr_5F436 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1176 (s : N.State) (i : N.Inputs) :
  R.v1176 (state s) (inputs i) = Zmod.unsigned (N.v1176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1176 s i)) at 1.
  unfold R.v1176, N.v1176.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1177 (s : N.State) (i : N.Inputs) :
  R.v1177 (state s) (inputs i) = Zmod.unsigned (N.v1177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1177 s i)) at 1.
  unfold R.v1177, N.v1177.
  unfold R.v33, N.v33.
  rewrite ?node_1176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1178 (s : N.State) (i : N.Inputs) :
  R.v1178 (state s) (inputs i) = Zmod.unsigned (N.v1178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1178 s i)) at 1.
  unfold R.v1178, N.v1178.
  unfold R.v35, N.v35.
  rewrite ?node_1176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1179 (s : N.State) (i : N.Inputs) :
  R.v1179 (state s) (inputs i) = Zmod.unsigned (N.v1179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1179 s i)) at 1.
  unfold R.v1179, N.v1179.
  rewrite ?node_1177.
  rewrite ?node_1178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1180 (s : N.State) (i : N.Inputs) :
  R.v1180 (state s) (inputs i) = Zmod.unsigned (N.v1180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1180 s i)) at 1.
  unfold R.v1180, N.v1180.
  unfold R.v39, N.v39.
  rewrite ?node_1176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1181 (s : N.State) (i : N.Inputs) :
  R.v1181 (state s) (inputs i) = Zmod.unsigned (N.v1181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1181 s i)) at 1.
  unfold R.v1181, N.v1181.
  unfold R.v42, N.v42.
  rewrite ?node_1176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1182 (s : N.State) (i : N.Inputs) :
  R.v1182 (state s) (inputs i) = Zmod.unsigned (N.v1182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1182 s i)) at 1.
  unfold R.v1182, N.v1182.
  unfold R.v45, N.v45.
  rewrite ?node_1176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1183 (s : N.State) (i : N.Inputs) :
  R.v1183 (state s) (inputs i) = Zmod.unsigned (N.v1183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1183 s i)) at 1.
  unfold R.v1183, N.v1183.
  unfold R.v47, N.v47.
  rewrite ?node_1176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1184 (s : N.State) (i : N.Inputs) :
  R.v1184 (state s) (inputs i) = Zmod.unsigned (N.v1184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1184 s i)) at 1.
  unfold R.v1184, N.v1184.
  rewrite ?node_1182.
  rewrite ?node_1183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1185 (s : N.State) (i : N.Inputs) :
  R.v1185 (state s) (inputs i) = Zmod.unsigned (N.v1185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1185 s i)) at 1.
  unfold R.v1185, N.v1185.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_1184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1186 (s : N.State) (i : N.Inputs) :
  R.v1186 (state s) (inputs i) = Zmod.unsigned (N.v1186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1186 s i)) at 1.
  unfold R.v1186, N.v1186.
  rewrite ?node_44.
  rewrite ?node_1181.
  rewrite ?node_1185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1187 (s : N.State) (i : N.Inputs) :
  R.v1187 (state s) (inputs i) = Zmod.unsigned (N.v1187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1187 s i)) at 1.
  unfold R.v1187, N.v1187.
  rewrite ?node_41.
  rewrite ?node_1180.
  rewrite ?node_1186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1188 (s : N.State) (i : N.Inputs) :
  R.v1188 (state s) (inputs i) = Zmod.unsigned (N.v1188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1188 s i)) at 1.
  unfold R.v1188, N.v1188.
  rewrite ?node_38.
  rewrite ?node_1179.
  rewrite ?node_1187.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1189 (s : N.State) (i : N.Inputs) :
  R.v1189 (state s) (inputs i) = Zmod.unsigned (N.v1189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1189 s i)) at 1.
  unfold R.v1189, N.v1189.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1190 (s : N.State) (i : N.Inputs) :
  R.v1190 (state s) (inputs i) = Zmod.unsigned (N.v1190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1190 s i)) at 1.
  unfold R.v1190, N.v1190.
  rewrite ?node_1189.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r437_nr_5F437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r437_nr_5F437 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1191 (s : N.State) (i : N.Inputs) :
  R.v1191 (state s) (inputs i) = Zmod.unsigned (N.v1191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1191 s i)) at 1.
  unfold R.v1191, N.v1191.
  unfold R.v6, N.v6.
  rewrite ?node_1180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1192 (s : N.State) (i : N.Inputs) :
  R.v1192 (state s) (inputs i) = Zmod.unsigned (N.v1192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1192 s i)) at 1.
  unfold R.v1192, N.v1192.
  unfold R.v19, N.v19.
  rewrite ?node_1179.
  rewrite ?node_1191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1193 (s : N.State) (i : N.Inputs) :
  R.v1193 (state s) (inputs i) = Zmod.unsigned (N.v1193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1193 s i)) at 1.
  unfold R.v1193, N.v1193.
  rewrite ?node_1192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1194 (s : N.State) (i : N.Inputs) :
  R.v1194 (state s) (inputs i) = Zmod.unsigned (N.v1194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1194 s i)) at 1.
  unfold R.v1194, N.v1194.
  rewrite ?node_1193.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r438_nr_5F438.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r438_nr_5F438 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1195 (s : N.State) (i : N.Inputs) :
  R.v1195 (state s) (inputs i) = Zmod.unsigned (N.v1195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1195 s i)) at 1.
  unfold R.v1195, N.v1195.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1196 (s : N.State) (i : N.Inputs) :
  R.v1196 (state s) (inputs i) = Zmod.unsigned (N.v1196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1196 s i)) at 1.
  unfold R.v1196, N.v1196.
  rewrite ?node_1195.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r439_nr_5F439.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r439_nr_5F439 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1197 (s : N.State) (i : N.Inputs) :
  R.v1197 (state s) (inputs i) = Zmod.unsigned (N.v1197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1197 s i)) at 1.
  unfold R.v1197, N.v1197.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1198 (s : N.State) (i : N.Inputs) :
  R.v1198 (state s) (inputs i) = Zmod.unsigned (N.v1198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1198 s i)) at 1.
  unfold R.v1198, N.v1198.
  rewrite ?node_1197.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r440_nr_5F440.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r440_nr_5F440 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1199 (s : N.State) (i : N.Inputs) :
  R.v1199 (state s) (inputs i) = Zmod.unsigned (N.v1199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1199 s i)) at 1.
  unfold R.v1199, N.v1199.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1200 (s : N.State) (i : N.Inputs) :
  R.v1200 (state s) (inputs i) = Zmod.unsigned (N.v1200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1200 s i)) at 1.
  unfold R.v1200, N.v1200.
  rewrite ?node_1199.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r441_nr_5F441.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r441_nr_5F441 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1201 (s : N.State) (i : N.Inputs) :
  R.v1201 (state s) (inputs i) = Zmod.unsigned (N.v1201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1201 s i)) at 1.
  unfold R.v1201, N.v1201.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1202 (s : N.State) (i : N.Inputs) :
  R.v1202 (state s) (inputs i) = Zmod.unsigned (N.v1202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1202 s i)) at 1.
  unfold R.v1202, N.v1202.
  rewrite ?node_1201.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r442_nr_5F442.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r442_nr_5F442 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1203 (s : N.State) (i : N.Inputs) :
  R.v1203 (state s) (inputs i) = Zmod.unsigned (N.v1203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1203 s i)) at 1.
  unfold R.v1203, N.v1203.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1204 (s : N.State) (i : N.Inputs) :
  R.v1204 (state s) (inputs i) = Zmod.unsigned (N.v1204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1204 s i)) at 1.
  unfold R.v1204, N.v1204.
  rewrite ?node_1203.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r443_nr_5F443.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r443_nr_5F443 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1205 (s : N.State) (i : N.Inputs) :
  R.v1205 (state s) (inputs i) = Zmod.unsigned (N.v1205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1205 s i)) at 1.
  unfold R.v1205, N.v1205.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1206 (s : N.State) (i : N.Inputs) :
  R.v1206 (state s) (inputs i) = Zmod.unsigned (N.v1206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1206 s i)) at 1.
  unfold R.v1206, N.v1206.
  rewrite ?node_1205.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r444_nr_5F444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r444_nr_5F444 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1207 (s : N.State) (i : N.Inputs) :
  R.v1207 (state s) (inputs i) = Zmod.unsigned (N.v1207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1207 s i)) at 1.
  unfold R.v1207, N.v1207.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1208 (s : N.State) (i : N.Inputs) :
  R.v1208 (state s) (inputs i) = Zmod.unsigned (N.v1208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1208 s i)) at 1.
  unfold R.v1208, N.v1208.
  rewrite ?node_1207.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r445_nr_5F445.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r445_nr_5F445 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1209 (s : N.State) (i : N.Inputs) :
  R.v1209 (state s) (inputs i) = Zmod.unsigned (N.v1209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1209 s i)) at 1.
  unfold R.v1209, N.v1209.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1210 (s : N.State) (i : N.Inputs) :
  R.v1210 (state s) (inputs i) = Zmod.unsigned (N.v1210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1210 s i)) at 1.
  unfold R.v1210, N.v1210.
  rewrite ?node_1209.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r446_nr_5F446.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r446_nr_5F446 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1211 (s : N.State) (i : N.Inputs) :
  R.v1211 (state s) (inputs i) = Zmod.unsigned (N.v1211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1211 s i)) at 1.
  unfold R.v1211, N.v1211.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1212 (s : N.State) (i : N.Inputs) :
  R.v1212 (state s) (inputs i) = Zmod.unsigned (N.v1212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1212 s i)) at 1.
  unfold R.v1212, N.v1212.
  rewrite ?node_1211.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r447_nr_5F447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r447_nr_5F447 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1213 (s : N.State) (i : N.Inputs) :
  R.v1213 (state s) (inputs i) = Zmod.unsigned (N.v1213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1213 s i)) at 1.
  unfold R.v1213, N.v1213.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1214 (s : N.State) (i : N.Inputs) :
  R.v1214 (state s) (inputs i) = Zmod.unsigned (N.v1214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1214 s i)) at 1.
  unfold R.v1214, N.v1214.
  rewrite ?node_1213.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r448_nr_5F448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r448_nr_5F448 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1215 (s : N.State) (i : N.Inputs) :
  R.v1215 (state s) (inputs i) = Zmod.unsigned (N.v1215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1215 s i)) at 1.
  unfold R.v1215, N.v1215.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1216 (s : N.State) (i : N.Inputs) :
  R.v1216 (state s) (inputs i) = Zmod.unsigned (N.v1216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1216 s i)) at 1.
  unfold R.v1216, N.v1216.
  rewrite ?node_1215.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r449_nr_5F449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r449_nr_5F449 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1217 (s : N.State) (i : N.Inputs) :
  R.v1217 (state s) (inputs i) = Zmod.unsigned (N.v1217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1217 s i)) at 1.
  unfold R.v1217, N.v1217.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1218 (s : N.State) (i : N.Inputs) :
  R.v1218 (state s) (inputs i) = Zmod.unsigned (N.v1218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1218 s i)) at 1.
  unfold R.v1218, N.v1218.
  rewrite ?node_1217.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r450_nr_5F450.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r450_nr_5F450 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1219 (s : N.State) (i : N.Inputs) :
  R.v1219 (state s) (inputs i) = Zmod.unsigned (N.v1219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1219 s i)) at 1.
  unfold R.v1219, N.v1219.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1220 (s : N.State) (i : N.Inputs) :
  R.v1220 (state s) (inputs i) = Zmod.unsigned (N.v1220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1220 s i)) at 1.
  unfold R.v1220, N.v1220.
  rewrite ?node_1219.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r451_nr_5F451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r451_nr_5F451 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1221 (s : N.State) (i : N.Inputs) :
  R.v1221 (state s) (inputs i) = Zmod.unsigned (N.v1221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1221 s i)) at 1.
  unfold R.v1221, N.v1221.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1222 (s : N.State) (i : N.Inputs) :
  R.v1222 (state s) (inputs i) = Zmod.unsigned (N.v1222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1222 s i)) at 1.
  unfold R.v1222, N.v1222.
  rewrite ?node_1221.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r452_nr_5F452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r452_nr_5F452 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1223 (s : N.State) (i : N.Inputs) :
  R.v1223 (state s) (inputs i) = Zmod.unsigned (N.v1223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1223 s i)) at 1.
  unfold R.v1223, N.v1223.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1224 (s : N.State) (i : N.Inputs) :
  R.v1224 (state s) (inputs i) = Zmod.unsigned (N.v1224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1224 s i)) at 1.
  unfold R.v1224, N.v1224.
  rewrite ?node_1223.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r453_nr_5F453.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r453_nr_5F453 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1225 (s : N.State) (i : N.Inputs) :
  R.v1225 (state s) (inputs i) = Zmod.unsigned (N.v1225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1225 s i)) at 1.
  unfold R.v1225, N.v1225.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1226 (s : N.State) (i : N.Inputs) :
  R.v1226 (state s) (inputs i) = Zmod.unsigned (N.v1226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1226 s i)) at 1.
  unfold R.v1226, N.v1226.
  rewrite ?node_1225.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r454_nr_5F454.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r454_nr_5F454 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1227 (s : N.State) (i : N.Inputs) :
  R.v1227 (state s) (inputs i) = Zmod.unsigned (N.v1227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1227 s i)) at 1.
  unfold R.v1227, N.v1227.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1228 (s : N.State) (i : N.Inputs) :
  R.v1228 (state s) (inputs i) = Zmod.unsigned (N.v1228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1228 s i)) at 1.
  unfold R.v1228, N.v1228.
  rewrite ?node_1227.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r455_nr_5F455.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r455_nr_5F455 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1229 (s : N.State) (i : N.Inputs) :
  R.v1229 (state s) (inputs i) = Zmod.unsigned (N.v1229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1229 s i)) at 1.
  unfold R.v1229, N.v1229.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1230 (s : N.State) (i : N.Inputs) :
  R.v1230 (state s) (inputs i) = Zmod.unsigned (N.v1230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1230 s i)) at 1.
  unfold R.v1230, N.v1230.
  rewrite ?node_1229.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r456_nr_5F456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r456_nr_5F456 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1231 (s : N.State) (i : N.Inputs) :
  R.v1231 (state s) (inputs i) = Zmod.unsigned (N.v1231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1231 s i)) at 1.
  unfold R.v1231, N.v1231.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1232 (s : N.State) (i : N.Inputs) :
  R.v1232 (state s) (inputs i) = Zmod.unsigned (N.v1232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1232 s i)) at 1.
  unfold R.v1232, N.v1232.
  rewrite ?node_1231.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r457_nr_5F457.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r457_nr_5F457 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1233 (s : N.State) (i : N.Inputs) :
  R.v1233 (state s) (inputs i) = Zmod.unsigned (N.v1233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1233 s i)) at 1.
  unfold R.v1233, N.v1233.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1234 (s : N.State) (i : N.Inputs) :
  R.v1234 (state s) (inputs i) = Zmod.unsigned (N.v1234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1234 s i)) at 1.
  unfold R.v1234, N.v1234.
  rewrite ?node_1233.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r458_nr_5F458.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r458_nr_5F458 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1235 (s : N.State) (i : N.Inputs) :
  R.v1235 (state s) (inputs i) = Zmod.unsigned (N.v1235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1235 s i)) at 1.
  unfold R.v1235, N.v1235.
  rewrite ?node_1192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1236 (s : N.State) (i : N.Inputs) :
  R.v1236 (state s) (inputs i) = Zmod.unsigned (N.v1236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1236 s i)) at 1.
  unfold R.v1236, N.v1236.
  rewrite ?node_1235.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r459_nr_5F459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r459_nr_5F459 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1237 (s : N.State) (i : N.Inputs) :
  R.v1237 (state s) (inputs i) = Zmod.unsigned (N.v1237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1237 s i)) at 1.
  unfold R.v1237, N.v1237.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1238 (s : N.State) (i : N.Inputs) :
  R.v1238 (state s) (inputs i) = Zmod.unsigned (N.v1238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1238 s i)) at 1.
  unfold R.v1238, N.v1238.
  rewrite ?node_1237.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r460_nr_5F460.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r460_nr_5F460 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1239 (s : N.State) (i : N.Inputs) :
  R.v1239 (state s) (inputs i) = Zmod.unsigned (N.v1239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1239 s i)) at 1.
  unfold R.v1239, N.v1239.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1240 (s : N.State) (i : N.Inputs) :
  R.v1240 (state s) (inputs i) = Zmod.unsigned (N.v1240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1240 s i)) at 1.
  unfold R.v1240, N.v1240.
  rewrite ?node_1239.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r461_nr_5F461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r461_nr_5F461 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1241 (s : N.State) (i : N.Inputs) :
  R.v1241 (state s) (inputs i) = Zmod.unsigned (N.v1241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1241 s i)) at 1.
  unfold R.v1241, N.v1241.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1242 (s : N.State) (i : N.Inputs) :
  R.v1242 (state s) (inputs i) = Zmod.unsigned (N.v1242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1242 s i)) at 1.
  unfold R.v1242, N.v1242.
  rewrite ?node_1241.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r462_nr_5F462.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r462_nr_5F462 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1243 (s : N.State) (i : N.Inputs) :
  R.v1243 (state s) (inputs i) = Zmod.unsigned (N.v1243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1243 s i)) at 1.
  unfold R.v1243, N.v1243.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1244 (s : N.State) (i : N.Inputs) :
  R.v1244 (state s) (inputs i) = Zmod.unsigned (N.v1244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1244 s i)) at 1.
  unfold R.v1244, N.v1244.
  rewrite ?node_1243.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r463_nr_5F463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r463_nr_5F463 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1245 (s : N.State) (i : N.Inputs) :
  R.v1245 (state s) (inputs i) = Zmod.unsigned (N.v1245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1245 s i)) at 1.
  unfold R.v1245, N.v1245.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1246 (s : N.State) (i : N.Inputs) :
  R.v1246 (state s) (inputs i) = Zmod.unsigned (N.v1246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1246 s i)) at 1.
  unfold R.v1246, N.v1246.
  rewrite ?node_1245.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r464_nr_5F464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r464_nr_5F464 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1247 (s : N.State) (i : N.Inputs) :
  R.v1247 (state s) (inputs i) = Zmod.unsigned (N.v1247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1247 s i)) at 1.
  unfold R.v1247, N.v1247.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1248 (s : N.State) (i : N.Inputs) :
  R.v1248 (state s) (inputs i) = Zmod.unsigned (N.v1248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1248 s i)) at 1.
  unfold R.v1248, N.v1248.
  rewrite ?node_1247.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r465_nr_5F465.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r465_nr_5F465 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1249 (s : N.State) (i : N.Inputs) :
  R.v1249 (state s) (inputs i) = Zmod.unsigned (N.v1249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1249 s i)) at 1.
  unfold R.v1249, N.v1249.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1250 (s : N.State) (i : N.Inputs) :
  R.v1250 (state s) (inputs i) = Zmod.unsigned (N.v1250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1250 s i)) at 1.
  unfold R.v1250, N.v1250.
  rewrite ?node_1249.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r466_nr_5F466.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r466_nr_5F466 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1251 (s : N.State) (i : N.Inputs) :
  R.v1251 (state s) (inputs i) = Zmod.unsigned (N.v1251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1251 s i)) at 1.
  unfold R.v1251, N.v1251.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1252 (s : N.State) (i : N.Inputs) :
  R.v1252 (state s) (inputs i) = Zmod.unsigned (N.v1252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1252 s i)) at 1.
  unfold R.v1252, N.v1252.
  rewrite ?node_1251.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r467_nr_5F467.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r467_nr_5F467 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1253 (s : N.State) (i : N.Inputs) :
  R.v1253 (state s) (inputs i) = Zmod.unsigned (N.v1253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1253 s i)) at 1.
  unfold R.v1253, N.v1253.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1254 (s : N.State) (i : N.Inputs) :
  R.v1254 (state s) (inputs i) = Zmod.unsigned (N.v1254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1254 s i)) at 1.
  unfold R.v1254, N.v1254.
  rewrite ?node_1253.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r468_nr_5F468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r468_nr_5F468 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1255 (s : N.State) (i : N.Inputs) :
  R.v1255 (state s) (inputs i) = Zmod.unsigned (N.v1255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1255 s i)) at 1.
  unfold R.v1255, N.v1255.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1256 (s : N.State) (i : N.Inputs) :
  R.v1256 (state s) (inputs i) = Zmod.unsigned (N.v1256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1256 s i)) at 1.
  unfold R.v1256, N.v1256.
  rewrite ?node_1255.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r469_nr_5F469.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r469_nr_5F469 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1257 (s : N.State) (i : N.Inputs) :
  R.v1257 (state s) (inputs i) = Zmod.unsigned (N.v1257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1257 s i)) at 1.
  unfold R.v1257, N.v1257.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1258 (s : N.State) (i : N.Inputs) :
  R.v1258 (state s) (inputs i) = Zmod.unsigned (N.v1258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1258 s i)) at 1.
  unfold R.v1258, N.v1258.
  rewrite ?node_1257.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r470_nr_5F470.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r470_nr_5F470 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1259 (s : N.State) (i : N.Inputs) :
  R.v1259 (state s) (inputs i) = Zmod.unsigned (N.v1259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1259 s i)) at 1.
  unfold R.v1259, N.v1259.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1260 (s : N.State) (i : N.Inputs) :
  R.v1260 (state s) (inputs i) = Zmod.unsigned (N.v1260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1260 s i)) at 1.
  unfold R.v1260, N.v1260.
  rewrite ?node_1259.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r471_nr_5F471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r471_nr_5F471 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1261 (s : N.State) (i : N.Inputs) :
  R.v1261 (state s) (inputs i) = Zmod.unsigned (N.v1261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1261 s i)) at 1.
  unfold R.v1261, N.v1261.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1262 (s : N.State) (i : N.Inputs) :
  R.v1262 (state s) (inputs i) = Zmod.unsigned (N.v1262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1262 s i)) at 1.
  unfold R.v1262, N.v1262.
  rewrite ?node_1261.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r472_nr_5F472.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r472_nr_5F472 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1263 (s : N.State) (i : N.Inputs) :
  R.v1263 (state s) (inputs i) = Zmod.unsigned (N.v1263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1263 s i)) at 1.
  unfold R.v1263, N.v1263.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1264 (s : N.State) (i : N.Inputs) :
  R.v1264 (state s) (inputs i) = Zmod.unsigned (N.v1264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1264 s i)) at 1.
  unfold R.v1264, N.v1264.
  rewrite ?node_1263.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r473_nr_5F473.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r473_nr_5F473 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1265 (s : N.State) (i : N.Inputs) :
  R.v1265 (state s) (inputs i) = Zmod.unsigned (N.v1265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1265 s i)) at 1.
  unfold R.v1265, N.v1265.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1266 (s : N.State) (i : N.Inputs) :
  R.v1266 (state s) (inputs i) = Zmod.unsigned (N.v1266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1266 s i)) at 1.
  unfold R.v1266, N.v1266.
  rewrite ?node_1265.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r474_nr_5F474.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r474_nr_5F474 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1267 (s : N.State) (i : N.Inputs) :
  R.v1267 (state s) (inputs i) = Zmod.unsigned (N.v1267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1267 s i)) at 1.
  unfold R.v1267, N.v1267.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1268 (s : N.State) (i : N.Inputs) :
  R.v1268 (state s) (inputs i) = Zmod.unsigned (N.v1268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1268 s i)) at 1.
  unfold R.v1268, N.v1268.
  rewrite ?node_1267.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r475_nr_5F475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r475_nr_5F475 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1269 (s : N.State) (i : N.Inputs) :
  R.v1269 (state s) (inputs i) = Zmod.unsigned (N.v1269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1269 s i)) at 1.
  unfold R.v1269, N.v1269.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1270 (s : N.State) (i : N.Inputs) :
  R.v1270 (state s) (inputs i) = Zmod.unsigned (N.v1270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1270 s i)) at 1.
  unfold R.v1270, N.v1270.
  rewrite ?node_1269.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r476_nr_5F476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r476_nr_5F476 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1271 (s : N.State) (i : N.Inputs) :
  R.v1271 (state s) (inputs i) = Zmod.unsigned (N.v1271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1271 s i)) at 1.
  unfold R.v1271, N.v1271.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1272 (s : N.State) (i : N.Inputs) :
  R.v1272 (state s) (inputs i) = Zmod.unsigned (N.v1272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1272 s i)) at 1.
  unfold R.v1272, N.v1272.
  rewrite ?node_1271.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r477_nr_5F477.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r477_nr_5F477 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1273 (s : N.State) (i : N.Inputs) :
  R.v1273 (state s) (inputs i) = Zmod.unsigned (N.v1273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1273 s i)) at 1.
  unfold R.v1273, N.v1273.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1274 (s : N.State) (i : N.Inputs) :
  R.v1274 (state s) (inputs i) = Zmod.unsigned (N.v1274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1274 s i)) at 1.
  unfold R.v1274, N.v1274.
  rewrite ?node_1273.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r478_nr_5F478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r478_nr_5F478 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1275 (s : N.State) (i : N.Inputs) :
  R.v1275 (state s) (inputs i) = Zmod.unsigned (N.v1275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1275 s i)) at 1.
  unfold R.v1275, N.v1275.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1276 (s : N.State) (i : N.Inputs) :
  R.v1276 (state s) (inputs i) = Zmod.unsigned (N.v1276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1276 s i)) at 1.
  unfold R.v1276, N.v1276.
  rewrite ?node_1275.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r479_nr_5F479.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r479_nr_5F479 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1277 (s : N.State) (i : N.Inputs) :
  R.v1277 (state s) (inputs i) = Zmod.unsigned (N.v1277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1277 s i)) at 1.
  unfold R.v1277, N.v1277.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1278 (s : N.State) (i : N.Inputs) :
  R.v1278 (state s) (inputs i) = Zmod.unsigned (N.v1278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1278 s i)) at 1.
  unfold R.v1278, N.v1278.
  unfold R.v33, N.v33.
  rewrite ?node_1277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1279 (s : N.State) (i : N.Inputs) :
  R.v1279 (state s) (inputs i) = Zmod.unsigned (N.v1279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1279 s i)) at 1.
  unfold R.v1279, N.v1279.
  unfold R.v35, N.v35.
  rewrite ?node_1277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1280 (s : N.State) (i : N.Inputs) :
  R.v1280 (state s) (inputs i) = Zmod.unsigned (N.v1280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1280 s i)) at 1.
  unfold R.v1280, N.v1280.
  rewrite ?node_1278.
  rewrite ?node_1279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1281 (s : N.State) (i : N.Inputs) :
  R.v1281 (state s) (inputs i) = Zmod.unsigned (N.v1281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1281 s i)) at 1.
  unfold R.v1281, N.v1281.
  unfold R.v39, N.v39.
  rewrite ?node_1277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1282 (s : N.State) (i : N.Inputs) :
  R.v1282 (state s) (inputs i) = Zmod.unsigned (N.v1282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1282 s i)) at 1.
  unfold R.v1282, N.v1282.
  unfold R.v42, N.v42.
  rewrite ?node_1277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1283 (s : N.State) (i : N.Inputs) :
  R.v1283 (state s) (inputs i) = Zmod.unsigned (N.v1283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1283 s i)) at 1.
  unfold R.v1283, N.v1283.
  unfold R.v45, N.v45.
  rewrite ?node_1277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1284 (s : N.State) (i : N.Inputs) :
  R.v1284 (state s) (inputs i) = Zmod.unsigned (N.v1284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1284 s i)) at 1.
  unfold R.v1284, N.v1284.
  unfold R.v47, N.v47.
  rewrite ?node_1277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1285 (s : N.State) (i : N.Inputs) :
  R.v1285 (state s) (inputs i) = Zmod.unsigned (N.v1285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1285 s i)) at 1.
  unfold R.v1285, N.v1285.
  rewrite ?node_1283.
  rewrite ?node_1284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1286 (s : N.State) (i : N.Inputs) :
  R.v1286 (state s) (inputs i) = Zmod.unsigned (N.v1286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1286 s i)) at 1.
  unfold R.v1286, N.v1286.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_1285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1287 (s : N.State) (i : N.Inputs) :
  R.v1287 (state s) (inputs i) = Zmod.unsigned (N.v1287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1287 s i)) at 1.
  unfold R.v1287, N.v1287.
  rewrite ?node_44.
  rewrite ?node_1282.
  rewrite ?node_1286.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1288 (s : N.State) (i : N.Inputs) :
  R.v1288 (state s) (inputs i) = Zmod.unsigned (N.v1288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1288 s i)) at 1.
  unfold R.v1288, N.v1288.
  rewrite ?node_41.
  rewrite ?node_1281.
  rewrite ?node_1287.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1289 (s : N.State) (i : N.Inputs) :
  R.v1289 (state s) (inputs i) = Zmod.unsigned (N.v1289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1289 s i)) at 1.
  unfold R.v1289, N.v1289.
  rewrite ?node_38.
  rewrite ?node_1280.
  rewrite ?node_1288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1290 (s : N.State) (i : N.Inputs) :
  R.v1290 (state s) (inputs i) = Zmod.unsigned (N.v1290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1290 s i)) at 1.
  unfold R.v1290, N.v1290.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1291 (s : N.State) (i : N.Inputs) :
  R.v1291 (state s) (inputs i) = Zmod.unsigned (N.v1291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1291 s i)) at 1.
  unfold R.v1291, N.v1291.
  rewrite ?node_1290.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r480_nr_5F480.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r480_nr_5F480 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1292 (s : N.State) (i : N.Inputs) :
  R.v1292 (state s) (inputs i) = Zmod.unsigned (N.v1292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1292 s i)) at 1.
  unfold R.v1292, N.v1292.
  unfold R.v6, N.v6.
  rewrite ?node_1281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1293 (s : N.State) (i : N.Inputs) :
  R.v1293 (state s) (inputs i) = Zmod.unsigned (N.v1293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1293 s i)) at 1.
  unfold R.v1293, N.v1293.
  unfold R.v19, N.v19.
  rewrite ?node_1280.
  rewrite ?node_1292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1294 (s : N.State) (i : N.Inputs) :
  R.v1294 (state s) (inputs i) = Zmod.unsigned (N.v1294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1294 s i)) at 1.
  unfold R.v1294, N.v1294.
  rewrite ?node_1293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1295 (s : N.State) (i : N.Inputs) :
  R.v1295 (state s) (inputs i) = Zmod.unsigned (N.v1295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1295 s i)) at 1.
  unfold R.v1295, N.v1295.
  rewrite ?node_1294.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r481_nr_5F481.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r481_nr_5F481 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1296 (s : N.State) (i : N.Inputs) :
  R.v1296 (state s) (inputs i) = Zmod.unsigned (N.v1296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1296 s i)) at 1.
  unfold R.v1296, N.v1296.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1297 (s : N.State) (i : N.Inputs) :
  R.v1297 (state s) (inputs i) = Zmod.unsigned (N.v1297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1297 s i)) at 1.
  unfold R.v1297, N.v1297.
  rewrite ?node_1296.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r482_nr_5F482.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r482_nr_5F482 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1298 (s : N.State) (i : N.Inputs) :
  R.v1298 (state s) (inputs i) = Zmod.unsigned (N.v1298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1298 s i)) at 1.
  unfold R.v1298, N.v1298.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1299 (s : N.State) (i : N.Inputs) :
  R.v1299 (state s) (inputs i) = Zmod.unsigned (N.v1299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1299 s i)) at 1.
  unfold R.v1299, N.v1299.
  rewrite ?node_1298.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r483_nr_5F483.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r483_nr_5F483 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1300 (s : N.State) (i : N.Inputs) :
  R.v1300 (state s) (inputs i) = Zmod.unsigned (N.v1300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1300 s i)) at 1.
  unfold R.v1300, N.v1300.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1301 (s : N.State) (i : N.Inputs) :
  R.v1301 (state s) (inputs i) = Zmod.unsigned (N.v1301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1301 s i)) at 1.
  unfold R.v1301, N.v1301.
  rewrite ?node_1300.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r484_nr_5F484.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r484_nr_5F484 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1302 (s : N.State) (i : N.Inputs) :
  R.v1302 (state s) (inputs i) = Zmod.unsigned (N.v1302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1302 s i)) at 1.
  unfold R.v1302, N.v1302.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1303 (s : N.State) (i : N.Inputs) :
  R.v1303 (state s) (inputs i) = Zmod.unsigned (N.v1303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1303 s i)) at 1.
  unfold R.v1303, N.v1303.
  rewrite ?node_1302.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r485_nr_5F485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r485_nr_5F485 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1304 (s : N.State) (i : N.Inputs) :
  R.v1304 (state s) (inputs i) = Zmod.unsigned (N.v1304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1304 s i)) at 1.
  unfold R.v1304, N.v1304.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1305 (s : N.State) (i : N.Inputs) :
  R.v1305 (state s) (inputs i) = Zmod.unsigned (N.v1305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1305 s i)) at 1.
  unfold R.v1305, N.v1305.
  rewrite ?node_1304.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r486_nr_5F486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r486_nr_5F486 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1306 (s : N.State) (i : N.Inputs) :
  R.v1306 (state s) (inputs i) = Zmod.unsigned (N.v1306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1306 s i)) at 1.
  unfold R.v1306, N.v1306.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1307 (s : N.State) (i : N.Inputs) :
  R.v1307 (state s) (inputs i) = Zmod.unsigned (N.v1307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1307 s i)) at 1.
  unfold R.v1307, N.v1307.
  rewrite ?node_1306.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r487_nr_5F487.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r487_nr_5F487 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1308 (s : N.State) (i : N.Inputs) :
  R.v1308 (state s) (inputs i) = Zmod.unsigned (N.v1308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1308 s i)) at 1.
  unfold R.v1308, N.v1308.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1309 (s : N.State) (i : N.Inputs) :
  R.v1309 (state s) (inputs i) = Zmod.unsigned (N.v1309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1309 s i)) at 1.
  unfold R.v1309, N.v1309.
  rewrite ?node_1308.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r488_nr_5F488.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r488_nr_5F488 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1310 (s : N.State) (i : N.Inputs) :
  R.v1310 (state s) (inputs i) = Zmod.unsigned (N.v1310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1310 s i)) at 1.
  unfold R.v1310, N.v1310.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1311 (s : N.State) (i : N.Inputs) :
  R.v1311 (state s) (inputs i) = Zmod.unsigned (N.v1311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1311 s i)) at 1.
  unfold R.v1311, N.v1311.
  rewrite ?node_1310.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r489_nr_5F489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r489_nr_5F489 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1312 (s : N.State) (i : N.Inputs) :
  R.v1312 (state s) (inputs i) = Zmod.unsigned (N.v1312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1312 s i)) at 1.
  unfold R.v1312, N.v1312.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1313 (s : N.State) (i : N.Inputs) :
  R.v1313 (state s) (inputs i) = Zmod.unsigned (N.v1313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1313 s i)) at 1.
  unfold R.v1313, N.v1313.
  rewrite ?node_1312.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r490_nr_5F490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r490_nr_5F490 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1314 (s : N.State) (i : N.Inputs) :
  R.v1314 (state s) (inputs i) = Zmod.unsigned (N.v1314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1314 s i)) at 1.
  unfold R.v1314, N.v1314.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1315 (s : N.State) (i : N.Inputs) :
  R.v1315 (state s) (inputs i) = Zmod.unsigned (N.v1315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1315 s i)) at 1.
  unfold R.v1315, N.v1315.
  rewrite ?node_1314.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r491_nr_5F491.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r491_nr_5F491 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1316 (s : N.State) (i : N.Inputs) :
  R.v1316 (state s) (inputs i) = Zmod.unsigned (N.v1316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1316 s i)) at 1.
  unfold R.v1316, N.v1316.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1317 (s : N.State) (i : N.Inputs) :
  R.v1317 (state s) (inputs i) = Zmod.unsigned (N.v1317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1317 s i)) at 1.
  unfold R.v1317, N.v1317.
  rewrite ?node_1316.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r492_nr_5F492.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r492_nr_5F492 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1318 (s : N.State) (i : N.Inputs) :
  R.v1318 (state s) (inputs i) = Zmod.unsigned (N.v1318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1318 s i)) at 1.
  unfold R.v1318, N.v1318.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1319 (s : N.State) (i : N.Inputs) :
  R.v1319 (state s) (inputs i) = Zmod.unsigned (N.v1319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1319 s i)) at 1.
  unfold R.v1319, N.v1319.
  rewrite ?node_1318.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r493_nr_5F493.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r493_nr_5F493 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1320 (s : N.State) (i : N.Inputs) :
  R.v1320 (state s) (inputs i) = Zmod.unsigned (N.v1320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1320 s i)) at 1.
  unfold R.v1320, N.v1320.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1321 (s : N.State) (i : N.Inputs) :
  R.v1321 (state s) (inputs i) = Zmod.unsigned (N.v1321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1321 s i)) at 1.
  unfold R.v1321, N.v1321.
  rewrite ?node_1320.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r494_nr_5F494.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r494_nr_5F494 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1322 (s : N.State) (i : N.Inputs) :
  R.v1322 (state s) (inputs i) = Zmod.unsigned (N.v1322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1322 s i)) at 1.
  unfold R.v1322, N.v1322.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1323 (s : N.State) (i : N.Inputs) :
  R.v1323 (state s) (inputs i) = Zmod.unsigned (N.v1323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1323 s i)) at 1.
  unfold R.v1323, N.v1323.
  rewrite ?node_1322.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r495_nr_5F495.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r495_nr_5F495 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1324 (s : N.State) (i : N.Inputs) :
  R.v1324 (state s) (inputs i) = Zmod.unsigned (N.v1324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1324 s i)) at 1.
  unfold R.v1324, N.v1324.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1325 (s : N.State) (i : N.Inputs) :
  R.v1325 (state s) (inputs i) = Zmod.unsigned (N.v1325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1325 s i)) at 1.
  unfold R.v1325, N.v1325.
  rewrite ?node_1324.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r496_nr_5F496.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r496_nr_5F496 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1326 (s : N.State) (i : N.Inputs) :
  R.v1326 (state s) (inputs i) = Zmod.unsigned (N.v1326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1326 s i)) at 1.
  unfold R.v1326, N.v1326.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1327 (s : N.State) (i : N.Inputs) :
  R.v1327 (state s) (inputs i) = Zmod.unsigned (N.v1327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1327 s i)) at 1.
  unfold R.v1327, N.v1327.
  rewrite ?node_1326.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r497_nr_5F497.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r497_nr_5F497 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1328 (s : N.State) (i : N.Inputs) :
  R.v1328 (state s) (inputs i) = Zmod.unsigned (N.v1328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1328 s i)) at 1.
  unfold R.v1328, N.v1328.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1329 (s : N.State) (i : N.Inputs) :
  R.v1329 (state s) (inputs i) = Zmod.unsigned (N.v1329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1329 s i)) at 1.
  unfold R.v1329, N.v1329.
  rewrite ?node_1328.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r498_nr_5F498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r498_nr_5F498 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1330 (s : N.State) (i : N.Inputs) :
  R.v1330 (state s) (inputs i) = Zmod.unsigned (N.v1330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1330 s i)) at 1.
  unfold R.v1330, N.v1330.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1331 (s : N.State) (i : N.Inputs) :
  R.v1331 (state s) (inputs i) = Zmod.unsigned (N.v1331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1331 s i)) at 1.
  unfold R.v1331, N.v1331.
  rewrite ?node_1330.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r499_nr_5F499.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r499_nr_5F499 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1332 (s : N.State) (i : N.Inputs) :
  R.v1332 (state s) (inputs i) = Zmod.unsigned (N.v1332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1332 s i)) at 1.
  unfold R.v1332, N.v1332.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1333 (s : N.State) (i : N.Inputs) :
  R.v1333 (state s) (inputs i) = Zmod.unsigned (N.v1333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1333 s i)) at 1.
  unfold R.v1333, N.v1333.
  rewrite ?node_1332.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r500_nr_5F500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r500_nr_5F500 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1334 (s : N.State) (i : N.Inputs) :
  R.v1334 (state s) (inputs i) = Zmod.unsigned (N.v1334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1334 s i)) at 1.
  unfold R.v1334, N.v1334.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1335 (s : N.State) (i : N.Inputs) :
  R.v1335 (state s) (inputs i) = Zmod.unsigned (N.v1335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1335 s i)) at 1.
  unfold R.v1335, N.v1335.
  rewrite ?node_1334.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r501_nr_5F501.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r501_nr_5F501 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1336 (s : N.State) (i : N.Inputs) :
  R.v1336 (state s) (inputs i) = Zmod.unsigned (N.v1336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1336 s i)) at 1.
  unfold R.v1336, N.v1336.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1337 (s : N.State) (i : N.Inputs) :
  R.v1337 (state s) (inputs i) = Zmod.unsigned (N.v1337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1337 s i)) at 1.
  unfold R.v1337, N.v1337.
  rewrite ?node_1336.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r502_nr_5F502.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r502_nr_5F502 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1338 (s : N.State) (i : N.Inputs) :
  R.v1338 (state s) (inputs i) = Zmod.unsigned (N.v1338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1338 s i)) at 1.
  unfold R.v1338, N.v1338.
  rewrite ?node_1293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1339 (s : N.State) (i : N.Inputs) :
  R.v1339 (state s) (inputs i) = Zmod.unsigned (N.v1339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1339 s i)) at 1.
  unfold R.v1339, N.v1339.
  rewrite ?node_1338.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r503_nr_5F503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r503_nr_5F503 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1340 (s : N.State) (i : N.Inputs) :
  R.v1340 (state s) (inputs i) = Zmod.unsigned (N.v1340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1340 s i)) at 1.
  unfold R.v1340, N.v1340.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1341 (s : N.State) (i : N.Inputs) :
  R.v1341 (state s) (inputs i) = Zmod.unsigned (N.v1341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1341 s i)) at 1.
  unfold R.v1341, N.v1341.
  rewrite ?node_1340.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r504_nr_5F504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r504_nr_5F504 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1342 (s : N.State) (i : N.Inputs) :
  R.v1342 (state s) (inputs i) = Zmod.unsigned (N.v1342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1342 s i)) at 1.
  unfold R.v1342, N.v1342.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1343 (s : N.State) (i : N.Inputs) :
  R.v1343 (state s) (inputs i) = Zmod.unsigned (N.v1343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1343 s i)) at 1.
  unfold R.v1343, N.v1343.
  rewrite ?node_1342.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r505_nr_5F505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r505_nr_5F505 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1344 (s : N.State) (i : N.Inputs) :
  R.v1344 (state s) (inputs i) = Zmod.unsigned (N.v1344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1344 s i)) at 1.
  unfold R.v1344, N.v1344.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1345 (s : N.State) (i : N.Inputs) :
  R.v1345 (state s) (inputs i) = Zmod.unsigned (N.v1345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1345 s i)) at 1.
  unfold R.v1345, N.v1345.
  rewrite ?node_1344.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r506_nr_5F506.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r506_nr_5F506 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1346 (s : N.State) (i : N.Inputs) :
  R.v1346 (state s) (inputs i) = Zmod.unsigned (N.v1346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1346 s i)) at 1.
  unfold R.v1346, N.v1346.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1347 (s : N.State) (i : N.Inputs) :
  R.v1347 (state s) (inputs i) = Zmod.unsigned (N.v1347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1347 s i)) at 1.
  unfold R.v1347, N.v1347.
  rewrite ?node_1346.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r507_nr_5F507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r507_nr_5F507 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1348 (s : N.State) (i : N.Inputs) :
  R.v1348 (state s) (inputs i) = Zmod.unsigned (N.v1348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1348 s i)) at 1.
  unfold R.v1348, N.v1348.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1349 (s : N.State) (i : N.Inputs) :
  R.v1349 (state s) (inputs i) = Zmod.unsigned (N.v1349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1349 s i)) at 1.
  unfold R.v1349, N.v1349.
  rewrite ?node_1348.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r508_nr_5F508.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r508_nr_5F508 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1350 (s : N.State) (i : N.Inputs) :
  R.v1350 (state s) (inputs i) = Zmod.unsigned (N.v1350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1350 s i)) at 1.
  unfold R.v1350, N.v1350.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1351 (s : N.State) (i : N.Inputs) :
  R.v1351 (state s) (inputs i) = Zmod.unsigned (N.v1351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1351 s i)) at 1.
  unfold R.v1351, N.v1351.
  rewrite ?node_1350.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r509_nr_5F509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r509_nr_5F509 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1352 (s : N.State) (i : N.Inputs) :
  R.v1352 (state s) (inputs i) = Zmod.unsigned (N.v1352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1352 s i)) at 1.
  unfold R.v1352, N.v1352.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1353 (s : N.State) (i : N.Inputs) :
  R.v1353 (state s) (inputs i) = Zmod.unsigned (N.v1353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1353 s i)) at 1.
  unfold R.v1353, N.v1353.
  rewrite ?node_1352.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r510_nr_5F510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r510_nr_5F510 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1354 (s : N.State) (i : N.Inputs) :
  R.v1354 (state s) (inputs i) = Zmod.unsigned (N.v1354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1354 s i)) at 1.
  unfold R.v1354, N.v1354.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1355 (s : N.State) (i : N.Inputs) :
  R.v1355 (state s) (inputs i) = Zmod.unsigned (N.v1355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1355 s i)) at 1.
  unfold R.v1355, N.v1355.
  rewrite ?node_1354.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r511_nr_5F511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r511_nr_5F511 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1356 (s : N.State) (i : N.Inputs) :
  R.v1356 (state s) (inputs i) = Zmod.unsigned (N.v1356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1356 s i)) at 1.
  unfold R.v1356, N.v1356.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1357 (s : N.State) (i : N.Inputs) :
  R.v1357 (state s) (inputs i) = Zmod.unsigned (N.v1357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1357 s i)) at 1.
  unfold R.v1357, N.v1357.
  rewrite ?node_1356.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r512_nr_5F512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r512_nr_5F512 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1358 (s : N.State) (i : N.Inputs) :
  R.v1358 (state s) (inputs i) = Zmod.unsigned (N.v1358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1358 s i)) at 1.
  unfold R.v1358, N.v1358.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1359 (s : N.State) (i : N.Inputs) :
  R.v1359 (state s) (inputs i) = Zmod.unsigned (N.v1359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1359 s i)) at 1.
  unfold R.v1359, N.v1359.
  rewrite ?node_1358.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r513_nr_5F513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r513_nr_5F513 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1360 (s : N.State) (i : N.Inputs) :
  R.v1360 (state s) (inputs i) = Zmod.unsigned (N.v1360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1360 s i)) at 1.
  unfold R.v1360, N.v1360.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1361 (s : N.State) (i : N.Inputs) :
  R.v1361 (state s) (inputs i) = Zmod.unsigned (N.v1361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1361 s i)) at 1.
  unfold R.v1361, N.v1361.
  rewrite ?node_1360.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r514_nr_5F514.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r514_nr_5F514 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1362 (s : N.State) (i : N.Inputs) :
  R.v1362 (state s) (inputs i) = Zmod.unsigned (N.v1362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1362 s i)) at 1.
  unfold R.v1362, N.v1362.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1363 (s : N.State) (i : N.Inputs) :
  R.v1363 (state s) (inputs i) = Zmod.unsigned (N.v1363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1363 s i)) at 1.
  unfold R.v1363, N.v1363.
  rewrite ?node_1362.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r515_nr_5F515.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r515_nr_5F515 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1364 (s : N.State) (i : N.Inputs) :
  R.v1364 (state s) (inputs i) = Zmod.unsigned (N.v1364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1364 s i)) at 1.
  unfold R.v1364, N.v1364.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1365 (s : N.State) (i : N.Inputs) :
  R.v1365 (state s) (inputs i) = Zmod.unsigned (N.v1365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1365 s i)) at 1.
  unfold R.v1365, N.v1365.
  rewrite ?node_1364.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r516_nr_5F516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r516_nr_5F516 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1366 (s : N.State) (i : N.Inputs) :
  R.v1366 (state s) (inputs i) = Zmod.unsigned (N.v1366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1366 s i)) at 1.
  unfold R.v1366, N.v1366.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1367 (s : N.State) (i : N.Inputs) :
  R.v1367 (state s) (inputs i) = Zmod.unsigned (N.v1367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1367 s i)) at 1.
  unfold R.v1367, N.v1367.
  rewrite ?node_1366.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r517_nr_5F517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r517_nr_5F517 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1368 (s : N.State) (i : N.Inputs) :
  R.v1368 (state s) (inputs i) = Zmod.unsigned (N.v1368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1368 s i)) at 1.
  unfold R.v1368, N.v1368.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1369 (s : N.State) (i : N.Inputs) :
  R.v1369 (state s) (inputs i) = Zmod.unsigned (N.v1369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1369 s i)) at 1.
  unfold R.v1369, N.v1369.
  rewrite ?node_1368.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r518_nr_5F518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r518_nr_5F518 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1370 (s : N.State) (i : N.Inputs) :
  R.v1370 (state s) (inputs i) = Zmod.unsigned (N.v1370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1370 s i)) at 1.
  unfold R.v1370, N.v1370.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1371 (s : N.State) (i : N.Inputs) :
  R.v1371 (state s) (inputs i) = Zmod.unsigned (N.v1371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1371 s i)) at 1.
  unfold R.v1371, N.v1371.
  rewrite ?node_1370.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r519_nr_5F519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r519_nr_5F519 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1372 (s : N.State) (i : N.Inputs) :
  R.v1372 (state s) (inputs i) = Zmod.unsigned (N.v1372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1372 s i)) at 1.
  unfold R.v1372, N.v1372.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1373 (s : N.State) (i : N.Inputs) :
  R.v1373 (state s) (inputs i) = Zmod.unsigned (N.v1373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1373 s i)) at 1.
  unfold R.v1373, N.v1373.
  rewrite ?node_1372.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r520_nr_5F520.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r520_nr_5F520 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1374 (s : N.State) (i : N.Inputs) :
  R.v1374 (state s) (inputs i) = Zmod.unsigned (N.v1374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1374 s i)) at 1.
  unfold R.v1374, N.v1374.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1375 (s : N.State) (i : N.Inputs) :
  R.v1375 (state s) (inputs i) = Zmod.unsigned (N.v1375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1375 s i)) at 1.
  unfold R.v1375, N.v1375.
  rewrite ?node_1374.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r521_nr_5F521.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r521_nr_5F521 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1376 (s : N.State) (i : N.Inputs) :
  R.v1376 (state s) (inputs i) = Zmod.unsigned (N.v1376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1376 s i)) at 1.
  unfold R.v1376, N.v1376.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1377 (s : N.State) (i : N.Inputs) :
  R.v1377 (state s) (inputs i) = Zmod.unsigned (N.v1377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1377 s i)) at 1.
  unfold R.v1377, N.v1377.
  rewrite ?node_1376.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r522_nr_5F522.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r522_nr_5F522 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1378 (s : N.State) (i : N.Inputs) :
  R.v1378 (state s) (inputs i) = Zmod.unsigned (N.v1378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1378 s i)) at 1.
  unfold R.v1378, N.v1378.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1379 (s : N.State) (i : N.Inputs) :
  R.v1379 (state s) (inputs i) = Zmod.unsigned (N.v1379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1379 s i)) at 1.
  unfold R.v1379, N.v1379.
  rewrite ?node_1378.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r523_nr_5F523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r523_nr_5F523 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1380 (s : N.State) (i : N.Inputs) :
  R.v1380 (state s) (inputs i) = Zmod.unsigned (N.v1380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1380 s i)) at 1.
  unfold R.v1380, N.v1380.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1381 (s : N.State) (i : N.Inputs) :
  R.v1381 (state s) (inputs i) = Zmod.unsigned (N.v1381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1381 s i)) at 1.
  unfold R.v1381, N.v1381.
  rewrite ?node_1380.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r524_nr_5F524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r524_nr_5F524 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1382 (s : N.State) (i : N.Inputs) :
  R.v1382 (state s) (inputs i) = Zmod.unsigned (N.v1382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1382 s i)) at 1.
  unfold R.v1382, N.v1382.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1383 (s : N.State) (i : N.Inputs) :
  R.v1383 (state s) (inputs i) = Zmod.unsigned (N.v1383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1383 s i)) at 1.
  unfold R.v1383, N.v1383.
  unfold R.v33, N.v33.
  rewrite ?node_1382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1384 (s : N.State) (i : N.Inputs) :
  R.v1384 (state s) (inputs i) = Zmod.unsigned (N.v1384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1384 s i)) at 1.
  unfold R.v1384, N.v1384.
  unfold R.v35, N.v35.
  rewrite ?node_1382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1385 (s : N.State) (i : N.Inputs) :
  R.v1385 (state s) (inputs i) = Zmod.unsigned (N.v1385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1385 s i)) at 1.
  unfold R.v1385, N.v1385.
  rewrite ?node_1383.
  rewrite ?node_1384.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1386 (s : N.State) (i : N.Inputs) :
  R.v1386 (state s) (inputs i) = Zmod.unsigned (N.v1386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1386 s i)) at 1.
  unfold R.v1386, N.v1386.
  unfold R.v39, N.v39.
  rewrite ?node_1382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1387 (s : N.State) (i : N.Inputs) :
  R.v1387 (state s) (inputs i) = Zmod.unsigned (N.v1387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1387 s i)) at 1.
  unfold R.v1387, N.v1387.
  unfold R.v42, N.v42.
  rewrite ?node_1382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1388 (s : N.State) (i : N.Inputs) :
  R.v1388 (state s) (inputs i) = Zmod.unsigned (N.v1388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1388 s i)) at 1.
  unfold R.v1388, N.v1388.
  unfold R.v45, N.v45.
  rewrite ?node_1382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1389 (s : N.State) (i : N.Inputs) :
  R.v1389 (state s) (inputs i) = Zmod.unsigned (N.v1389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1389 s i)) at 1.
  unfold R.v1389, N.v1389.
  unfold R.v47, N.v47.
  rewrite ?node_1382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1390 (s : N.State) (i : N.Inputs) :
  R.v1390 (state s) (inputs i) = Zmod.unsigned (N.v1390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1390 s i)) at 1.
  unfold R.v1390, N.v1390.
  rewrite ?node_1388.
  rewrite ?node_1389.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1391 (s : N.State) (i : N.Inputs) :
  R.v1391 (state s) (inputs i) = Zmod.unsigned (N.v1391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1391 s i)) at 1.
  unfold R.v1391, N.v1391.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_1390.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1392 (s : N.State) (i : N.Inputs) :
  R.v1392 (state s) (inputs i) = Zmod.unsigned (N.v1392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1392 s i)) at 1.
  unfold R.v1392, N.v1392.
  rewrite ?node_44.
  rewrite ?node_1387.
  rewrite ?node_1391.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1393 (s : N.State) (i : N.Inputs) :
  R.v1393 (state s) (inputs i) = Zmod.unsigned (N.v1393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1393 s i)) at 1.
  unfold R.v1393, N.v1393.
  rewrite ?node_41.
  rewrite ?node_1386.
  rewrite ?node_1392.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1394 (s : N.State) (i : N.Inputs) :
  R.v1394 (state s) (inputs i) = Zmod.unsigned (N.v1394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1394 s i)) at 1.
  unfold R.v1394, N.v1394.
  rewrite ?node_38.
  rewrite ?node_1385.
  rewrite ?node_1393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1395 (s : N.State) (i : N.Inputs) :
  R.v1395 (state s) (inputs i) = Zmod.unsigned (N.v1395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1395 s i)) at 1.
  unfold R.v1395, N.v1395.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1396 (s : N.State) (i : N.Inputs) :
  R.v1396 (state s) (inputs i) = Zmod.unsigned (N.v1396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1396 s i)) at 1.
  unfold R.v1396, N.v1396.
  rewrite ?node_1395.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r525_nr_5F525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r525_nr_5F525 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1397 (s : N.State) (i : N.Inputs) :
  R.v1397 (state s) (inputs i) = Zmod.unsigned (N.v1397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1397 s i)) at 1.
  unfold R.v1397, N.v1397.
  unfold R.v6, N.v6.
  rewrite ?node_1386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1398 (s : N.State) (i : N.Inputs) :
  R.v1398 (state s) (inputs i) = Zmod.unsigned (N.v1398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1398 s i)) at 1.
  unfold R.v1398, N.v1398.
  unfold R.v19, N.v19.
  rewrite ?node_1385.
  rewrite ?node_1397.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1399 (s : N.State) (i : N.Inputs) :
  R.v1399 (state s) (inputs i) = Zmod.unsigned (N.v1399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1399 s i)) at 1.
  unfold R.v1399, N.v1399.
  rewrite ?node_1398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1400 (s : N.State) (i : N.Inputs) :
  R.v1400 (state s) (inputs i) = Zmod.unsigned (N.v1400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1400 s i)) at 1.
  unfold R.v1400, N.v1400.
  rewrite ?node_1399.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r526_nr_5F526.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r526_nr_5F526 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1401 (s : N.State) (i : N.Inputs) :
  R.v1401 (state s) (inputs i) = Zmod.unsigned (N.v1401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1401 s i)) at 1.
  unfold R.v1401, N.v1401.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1402 (s : N.State) (i : N.Inputs) :
  R.v1402 (state s) (inputs i) = Zmod.unsigned (N.v1402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1402 s i)) at 1.
  unfold R.v1402, N.v1402.
  rewrite ?node_1401.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r527_nr_5F527.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r527_nr_5F527 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1403 (s : N.State) (i : N.Inputs) :
  R.v1403 (state s) (inputs i) = Zmod.unsigned (N.v1403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1403 s i)) at 1.
  unfold R.v1403, N.v1403.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1404 (s : N.State) (i : N.Inputs) :
  R.v1404 (state s) (inputs i) = Zmod.unsigned (N.v1404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1404 s i)) at 1.
  unfold R.v1404, N.v1404.
  rewrite ?node_1403.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r528_nr_5F528.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r528_nr_5F528 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1405 (s : N.State) (i : N.Inputs) :
  R.v1405 (state s) (inputs i) = Zmod.unsigned (N.v1405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1405 s i)) at 1.
  unfold R.v1405, N.v1405.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1406 (s : N.State) (i : N.Inputs) :
  R.v1406 (state s) (inputs i) = Zmod.unsigned (N.v1406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1406 s i)) at 1.
  unfold R.v1406, N.v1406.
  rewrite ?node_1405.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r529_nr_5F529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r529_nr_5F529 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1407 (s : N.State) (i : N.Inputs) :
  R.v1407 (state s) (inputs i) = Zmod.unsigned (N.v1407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1407 s i)) at 1.
  unfold R.v1407, N.v1407.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1408 (s : N.State) (i : N.Inputs) :
  R.v1408 (state s) (inputs i) = Zmod.unsigned (N.v1408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1408 s i)) at 1.
  unfold R.v1408, N.v1408.
  rewrite ?node_1407.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r530_nr_5F530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r530_nr_5F530 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1409 (s : N.State) (i : N.Inputs) :
  R.v1409 (state s) (inputs i) = Zmod.unsigned (N.v1409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1409 s i)) at 1.
  unfold R.v1409, N.v1409.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1410 (s : N.State) (i : N.Inputs) :
  R.v1410 (state s) (inputs i) = Zmod.unsigned (N.v1410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1410 s i)) at 1.
  unfold R.v1410, N.v1410.
  rewrite ?node_1409.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r531_nr_5F531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r531_nr_5F531 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1411 (s : N.State) (i : N.Inputs) :
  R.v1411 (state s) (inputs i) = Zmod.unsigned (N.v1411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1411 s i)) at 1.
  unfold R.v1411, N.v1411.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1412 (s : N.State) (i : N.Inputs) :
  R.v1412 (state s) (inputs i) = Zmod.unsigned (N.v1412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1412 s i)) at 1.
  unfold R.v1412, N.v1412.
  rewrite ?node_1411.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r532_nr_5F532.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r532_nr_5F532 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1413 (s : N.State) (i : N.Inputs) :
  R.v1413 (state s) (inputs i) = Zmod.unsigned (N.v1413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1413 s i)) at 1.
  unfold R.v1413, N.v1413.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1414 (s : N.State) (i : N.Inputs) :
  R.v1414 (state s) (inputs i) = Zmod.unsigned (N.v1414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1414 s i)) at 1.
  unfold R.v1414, N.v1414.
  rewrite ?node_1413.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r533_nr_5F533.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r533_nr_5F533 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1415 (s : N.State) (i : N.Inputs) :
  R.v1415 (state s) (inputs i) = Zmod.unsigned (N.v1415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1415 s i)) at 1.
  unfold R.v1415, N.v1415.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1416 (s : N.State) (i : N.Inputs) :
  R.v1416 (state s) (inputs i) = Zmod.unsigned (N.v1416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1416 s i)) at 1.
  unfold R.v1416, N.v1416.
  rewrite ?node_1415.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r534_nr_5F534.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r534_nr_5F534 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1417 (s : N.State) (i : N.Inputs) :
  R.v1417 (state s) (inputs i) = Zmod.unsigned (N.v1417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1417 s i)) at 1.
  unfold R.v1417, N.v1417.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1418 (s : N.State) (i : N.Inputs) :
  R.v1418 (state s) (inputs i) = Zmod.unsigned (N.v1418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1418 s i)) at 1.
  unfold R.v1418, N.v1418.
  rewrite ?node_1417.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r535_nr_5F535.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r535_nr_5F535 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1419 (s : N.State) (i : N.Inputs) :
  R.v1419 (state s) (inputs i) = Zmod.unsigned (N.v1419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1419 s i)) at 1.
  unfold R.v1419, N.v1419.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1420 (s : N.State) (i : N.Inputs) :
  R.v1420 (state s) (inputs i) = Zmod.unsigned (N.v1420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1420 s i)) at 1.
  unfold R.v1420, N.v1420.
  rewrite ?node_1419.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r536_nr_5F536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r536_nr_5F536 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1421 (s : N.State) (i : N.Inputs) :
  R.v1421 (state s) (inputs i) = Zmod.unsigned (N.v1421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1421 s i)) at 1.
  unfold R.v1421, N.v1421.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1422 (s : N.State) (i : N.Inputs) :
  R.v1422 (state s) (inputs i) = Zmod.unsigned (N.v1422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1422 s i)) at 1.
  unfold R.v1422, N.v1422.
  rewrite ?node_1421.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r537_nr_5F537.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r537_nr_5F537 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1423 (s : N.State) (i : N.Inputs) :
  R.v1423 (state s) (inputs i) = Zmod.unsigned (N.v1423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1423 s i)) at 1.
  unfold R.v1423, N.v1423.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1424 (s : N.State) (i : N.Inputs) :
  R.v1424 (state s) (inputs i) = Zmod.unsigned (N.v1424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1424 s i)) at 1.
  unfold R.v1424, N.v1424.
  rewrite ?node_1423.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r538_nr_5F538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r538_nr_5F538 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1425 (s : N.State) (i : N.Inputs) :
  R.v1425 (state s) (inputs i) = Zmod.unsigned (N.v1425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1425 s i)) at 1.
  unfold R.v1425, N.v1425.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1426 (s : N.State) (i : N.Inputs) :
  R.v1426 (state s) (inputs i) = Zmod.unsigned (N.v1426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1426 s i)) at 1.
  unfold R.v1426, N.v1426.
  rewrite ?node_1425.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r539_nr_5F539.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r539_nr_5F539 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1427 (s : N.State) (i : N.Inputs) :
  R.v1427 (state s) (inputs i) = Zmod.unsigned (N.v1427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1427 s i)) at 1.
  unfold R.v1427, N.v1427.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1428 (s : N.State) (i : N.Inputs) :
  R.v1428 (state s) (inputs i) = Zmod.unsigned (N.v1428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1428 s i)) at 1.
  unfold R.v1428, N.v1428.
  rewrite ?node_1427.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r540_nr_5F540.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r540_nr_5F540 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1429 (s : N.State) (i : N.Inputs) :
  R.v1429 (state s) (inputs i) = Zmod.unsigned (N.v1429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1429 s i)) at 1.
  unfold R.v1429, N.v1429.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1430 (s : N.State) (i : N.Inputs) :
  R.v1430 (state s) (inputs i) = Zmod.unsigned (N.v1430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1430 s i)) at 1.
  unfold R.v1430, N.v1430.
  rewrite ?node_1429.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r541_nr_5F541.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r541_nr_5F541 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1431 (s : N.State) (i : N.Inputs) :
  R.v1431 (state s) (inputs i) = Zmod.unsigned (N.v1431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1431 s i)) at 1.
  unfold R.v1431, N.v1431.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1432 (s : N.State) (i : N.Inputs) :
  R.v1432 (state s) (inputs i) = Zmod.unsigned (N.v1432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1432 s i)) at 1.
  unfold R.v1432, N.v1432.
  rewrite ?node_1431.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r542_nr_5F542.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r542_nr_5F542 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1433 (s : N.State) (i : N.Inputs) :
  R.v1433 (state s) (inputs i) = Zmod.unsigned (N.v1433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1433 s i)) at 1.
  unfold R.v1433, N.v1433.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1434 (s : N.State) (i : N.Inputs) :
  R.v1434 (state s) (inputs i) = Zmod.unsigned (N.v1434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1434 s i)) at 1.
  unfold R.v1434, N.v1434.
  rewrite ?node_1433.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r543_nr_5F543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r543_nr_5F543 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1435 (s : N.State) (i : N.Inputs) :
  R.v1435 (state s) (inputs i) = Zmod.unsigned (N.v1435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1435 s i)) at 1.
  unfold R.v1435, N.v1435.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1436 (s : N.State) (i : N.Inputs) :
  R.v1436 (state s) (inputs i) = Zmod.unsigned (N.v1436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1436 s i)) at 1.
  unfold R.v1436, N.v1436.
  rewrite ?node_1435.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r544_nr_5F544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r544_nr_5F544 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1437 (s : N.State) (i : N.Inputs) :
  R.v1437 (state s) (inputs i) = Zmod.unsigned (N.v1437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1437 s i)) at 1.
  unfold R.v1437, N.v1437.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1438 (s : N.State) (i : N.Inputs) :
  R.v1438 (state s) (inputs i) = Zmod.unsigned (N.v1438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1438 s i)) at 1.
  unfold R.v1438, N.v1438.
  rewrite ?node_1437.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r545_nr_5F545.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r545_nr_5F545 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1439 (s : N.State) (i : N.Inputs) :
  R.v1439 (state s) (inputs i) = Zmod.unsigned (N.v1439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1439 s i)) at 1.
  unfold R.v1439, N.v1439.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1440 (s : N.State) (i : N.Inputs) :
  R.v1440 (state s) (inputs i) = Zmod.unsigned (N.v1440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1440 s i)) at 1.
  unfold R.v1440, N.v1440.
  rewrite ?node_1439.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r546_nr_5F546.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r546_nr_5F546 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1441 (s : N.State) (i : N.Inputs) :
  R.v1441 (state s) (inputs i) = Zmod.unsigned (N.v1441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1441 s i)) at 1.
  unfold R.v1441, N.v1441.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1442 (s : N.State) (i : N.Inputs) :
  R.v1442 (state s) (inputs i) = Zmod.unsigned (N.v1442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1442 s i)) at 1.
  unfold R.v1442, N.v1442.
  rewrite ?node_1441.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r547_nr_5F547.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r547_nr_5F547 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1443 (s : N.State) (i : N.Inputs) :
  R.v1443 (state s) (inputs i) = Zmod.unsigned (N.v1443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1443 s i)) at 1.
  unfold R.v1443, N.v1443.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1444 (s : N.State) (i : N.Inputs) :
  R.v1444 (state s) (inputs i) = Zmod.unsigned (N.v1444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1444 s i)) at 1.
  unfold R.v1444, N.v1444.
  rewrite ?node_1443.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r548_nr_5F548.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r548_nr_5F548 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1445 (s : N.State) (i : N.Inputs) :
  R.v1445 (state s) (inputs i) = Zmod.unsigned (N.v1445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1445 s i)) at 1.
  unfold R.v1445, N.v1445.
  rewrite ?node_1398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1446 (s : N.State) (i : N.Inputs) :
  R.v1446 (state s) (inputs i) = Zmod.unsigned (N.v1446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1446 s i)) at 1.
  unfold R.v1446, N.v1446.
  rewrite ?node_1445.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r549_nr_5F549.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r549_nr_5F549 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1447 (s : N.State) (i : N.Inputs) :
  R.v1447 (state s) (inputs i) = Zmod.unsigned (N.v1447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1447 s i)) at 1.
  unfold R.v1447, N.v1447.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1448 (s : N.State) (i : N.Inputs) :
  R.v1448 (state s) (inputs i) = Zmod.unsigned (N.v1448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1448 s i)) at 1.
  unfold R.v1448, N.v1448.
  rewrite ?node_1447.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r550_nr_5F550.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r550_nr_5F550 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1449 (s : N.State) (i : N.Inputs) :
  R.v1449 (state s) (inputs i) = Zmod.unsigned (N.v1449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1449 s i)) at 1.
  unfold R.v1449, N.v1449.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1450 (s : N.State) (i : N.Inputs) :
  R.v1450 (state s) (inputs i) = Zmod.unsigned (N.v1450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1450 s i)) at 1.
  unfold R.v1450, N.v1450.
  rewrite ?node_1449.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r551_nr_5F551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r551_nr_5F551 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1451 (s : N.State) (i : N.Inputs) :
  R.v1451 (state s) (inputs i) = Zmod.unsigned (N.v1451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1451 s i)) at 1.
  unfold R.v1451, N.v1451.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1452 (s : N.State) (i : N.Inputs) :
  R.v1452 (state s) (inputs i) = Zmod.unsigned (N.v1452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1452 s i)) at 1.
  unfold R.v1452, N.v1452.
  rewrite ?node_1451.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r552_nr_5F552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r552_nr_5F552 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1453 (s : N.State) (i : N.Inputs) :
  R.v1453 (state s) (inputs i) = Zmod.unsigned (N.v1453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1453 s i)) at 1.
  unfold R.v1453, N.v1453.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1454 (s : N.State) (i : N.Inputs) :
  R.v1454 (state s) (inputs i) = Zmod.unsigned (N.v1454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1454 s i)) at 1.
  unfold R.v1454, N.v1454.
  rewrite ?node_1453.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r553_nr_5F553.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r553_nr_5F553 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1455 (s : N.State) (i : N.Inputs) :
  R.v1455 (state s) (inputs i) = Zmod.unsigned (N.v1455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1455 s i)) at 1.
  unfold R.v1455, N.v1455.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1456 (s : N.State) (i : N.Inputs) :
  R.v1456 (state s) (inputs i) = Zmod.unsigned (N.v1456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1456 s i)) at 1.
  unfold R.v1456, N.v1456.
  rewrite ?node_1455.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r554_nr_5F554.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r554_nr_5F554 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1457 (s : N.State) (i : N.Inputs) :
  R.v1457 (state s) (inputs i) = Zmod.unsigned (N.v1457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1457 s i)) at 1.
  unfold R.v1457, N.v1457.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1458 (s : N.State) (i : N.Inputs) :
  R.v1458 (state s) (inputs i) = Zmod.unsigned (N.v1458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1458 s i)) at 1.
  unfold R.v1458, N.v1458.
  rewrite ?node_1457.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r555_nr_5F555.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r555_nr_5F555 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1459 (s : N.State) (i : N.Inputs) :
  R.v1459 (state s) (inputs i) = Zmod.unsigned (N.v1459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1459 s i)) at 1.
  unfold R.v1459, N.v1459.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1460 (s : N.State) (i : N.Inputs) :
  R.v1460 (state s) (inputs i) = Zmod.unsigned (N.v1460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1460 s i)) at 1.
  unfold R.v1460, N.v1460.
  rewrite ?node_1459.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r556_nr_5F556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r556_nr_5F556 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1461 (s : N.State) (i : N.Inputs) :
  R.v1461 (state s) (inputs i) = Zmod.unsigned (N.v1461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1461 s i)) at 1.
  unfold R.v1461, N.v1461.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1462 (s : N.State) (i : N.Inputs) :
  R.v1462 (state s) (inputs i) = Zmod.unsigned (N.v1462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1462 s i)) at 1.
  unfold R.v1462, N.v1462.
  rewrite ?node_1461.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r557_nr_5F557.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r557_nr_5F557 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1463 (s : N.State) (i : N.Inputs) :
  R.v1463 (state s) (inputs i) = Zmod.unsigned (N.v1463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1463 s i)) at 1.
  unfold R.v1463, N.v1463.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1464 (s : N.State) (i : N.Inputs) :
  R.v1464 (state s) (inputs i) = Zmod.unsigned (N.v1464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1464 s i)) at 1.
  unfold R.v1464, N.v1464.
  rewrite ?node_1463.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r558_nr_5F558.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r558_nr_5F558 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1465 (s : N.State) (i : N.Inputs) :
  R.v1465 (state s) (inputs i) = Zmod.unsigned (N.v1465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1465 s i)) at 1.
  unfold R.v1465, N.v1465.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1466 (s : N.State) (i : N.Inputs) :
  R.v1466 (state s) (inputs i) = Zmod.unsigned (N.v1466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1466 s i)) at 1.
  unfold R.v1466, N.v1466.
  rewrite ?node_1465.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r559_nr_5F559.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r559_nr_5F559 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1467 (s : N.State) (i : N.Inputs) :
  R.v1467 (state s) (inputs i) = Zmod.unsigned (N.v1467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1467 s i)) at 1.
  unfold R.v1467, N.v1467.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1468 (s : N.State) (i : N.Inputs) :
  R.v1468 (state s) (inputs i) = Zmod.unsigned (N.v1468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1468 s i)) at 1.
  unfold R.v1468, N.v1468.
  rewrite ?node_1467.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r560_nr_5F560.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r560_nr_5F560 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1469 (s : N.State) (i : N.Inputs) :
  R.v1469 (state s) (inputs i) = Zmod.unsigned (N.v1469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1469 s i)) at 1.
  unfold R.v1469, N.v1469.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1470 (s : N.State) (i : N.Inputs) :
  R.v1470 (state s) (inputs i) = Zmod.unsigned (N.v1470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1470 s i)) at 1.
  unfold R.v1470, N.v1470.
  rewrite ?node_1469.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r561_nr_5F561.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r561_nr_5F561 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1471 (s : N.State) (i : N.Inputs) :
  R.v1471 (state s) (inputs i) = Zmod.unsigned (N.v1471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1471 s i)) at 1.
  unfold R.v1471, N.v1471.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1472 (s : N.State) (i : N.Inputs) :
  R.v1472 (state s) (inputs i) = Zmod.unsigned (N.v1472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1472 s i)) at 1.
  unfold R.v1472, N.v1472.
  rewrite ?node_1471.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r562_nr_5F562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r562_nr_5F562 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1473 (s : N.State) (i : N.Inputs) :
  R.v1473 (state s) (inputs i) = Zmod.unsigned (N.v1473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1473 s i)) at 1.
  unfold R.v1473, N.v1473.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1474 (s : N.State) (i : N.Inputs) :
  R.v1474 (state s) (inputs i) = Zmod.unsigned (N.v1474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1474 s i)) at 1.
  unfold R.v1474, N.v1474.
  rewrite ?node_1473.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r563_nr_5F563.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r563_nr_5F563 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1475 (s : N.State) (i : N.Inputs) :
  R.v1475 (state s) (inputs i) = Zmod.unsigned (N.v1475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1475 s i)) at 1.
  unfold R.v1475, N.v1475.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1476 (s : N.State) (i : N.Inputs) :
  R.v1476 (state s) (inputs i) = Zmod.unsigned (N.v1476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1476 s i)) at 1.
  unfold R.v1476, N.v1476.
  rewrite ?node_1475.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r564_nr_5F564.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r564_nr_5F564 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1477 (s : N.State) (i : N.Inputs) :
  R.v1477 (state s) (inputs i) = Zmod.unsigned (N.v1477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1477 s i)) at 1.
  unfold R.v1477, N.v1477.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1478 (s : N.State) (i : N.Inputs) :
  R.v1478 (state s) (inputs i) = Zmod.unsigned (N.v1478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1478 s i)) at 1.
  unfold R.v1478, N.v1478.
  rewrite ?node_1477.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r565_nr_5F565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r565_nr_5F565 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1479 (s : N.State) (i : N.Inputs) :
  R.v1479 (state s) (inputs i) = Zmod.unsigned (N.v1479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1479 s i)) at 1.
  unfold R.v1479, N.v1479.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1480 (s : N.State) (i : N.Inputs) :
  R.v1480 (state s) (inputs i) = Zmod.unsigned (N.v1480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1480 s i)) at 1.
  unfold R.v1480, N.v1480.
  rewrite ?node_1479.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r566_nr_5F566.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r566_nr_5F566 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1481 (s : N.State) (i : N.Inputs) :
  R.v1481 (state s) (inputs i) = Zmod.unsigned (N.v1481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1481 s i)) at 1.
  unfold R.v1481, N.v1481.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1482 (s : N.State) (i : N.Inputs) :
  R.v1482 (state s) (inputs i) = Zmod.unsigned (N.v1482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1482 s i)) at 1.
  unfold R.v1482, N.v1482.
  rewrite ?node_1481.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r567_nr_5F567.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r567_nr_5F567 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1483 (s : N.State) (i : N.Inputs) :
  R.v1483 (state s) (inputs i) = Zmod.unsigned (N.v1483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1483 s i)) at 1.
  unfold R.v1483, N.v1483.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1484 (s : N.State) (i : N.Inputs) :
  R.v1484 (state s) (inputs i) = Zmod.unsigned (N.v1484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1484 s i)) at 1.
  unfold R.v1484, N.v1484.
  rewrite ?node_1483.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r568_nr_5F568.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r568_nr_5F568 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1485 (s : N.State) (i : N.Inputs) :
  R.v1485 (state s) (inputs i) = Zmod.unsigned (N.v1485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1485 s i)) at 1.
  unfold R.v1485, N.v1485.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1486 (s : N.State) (i : N.Inputs) :
  R.v1486 (state s) (inputs i) = Zmod.unsigned (N.v1486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1486 s i)) at 1.
  unfold R.v1486, N.v1486.
  rewrite ?node_1485.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r569_nr_5F569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r569_nr_5F569 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1487 (s : N.State) (i : N.Inputs) :
  R.v1487 (state s) (inputs i) = Zmod.unsigned (N.v1487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1487 s i)) at 1.
  unfold R.v1487, N.v1487.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1488 (s : N.State) (i : N.Inputs) :
  R.v1488 (state s) (inputs i) = Zmod.unsigned (N.v1488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1488 s i)) at 1.
  unfold R.v1488, N.v1488.
  rewrite ?node_1487.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r570_nr_5F570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r570_nr_5F570 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1489 (s : N.State) (i : N.Inputs) :
  R.v1489 (state s) (inputs i) = Zmod.unsigned (N.v1489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1489 s i)) at 1.
  unfold R.v1489, N.v1489.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1490 (s : N.State) (i : N.Inputs) :
  R.v1490 (state s) (inputs i) = Zmod.unsigned (N.v1490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1490 s i)) at 1.
  unfold R.v1490, N.v1490.
  rewrite ?node_1489.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r571_nr_5F571.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r571_nr_5F571 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1491 (s : N.State) (i : N.Inputs) :
  R.v1491 (state s) (inputs i) = Zmod.unsigned (N.v1491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1491 s i)) at 1.
  unfold R.v1491, N.v1491.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1492 (s : N.State) (i : N.Inputs) :
  R.v1492 (state s) (inputs i) = Zmod.unsigned (N.v1492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1492 s i)) at 1.
  unfold R.v1492, N.v1492.
  unfold R.v33, N.v33.
  rewrite ?node_1491.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1493 (s : N.State) (i : N.Inputs) :
  R.v1493 (state s) (inputs i) = Zmod.unsigned (N.v1493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1493 s i)) at 1.
  unfold R.v1493, N.v1493.
  unfold R.v35, N.v35.
  rewrite ?node_1491.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1494 (s : N.State) (i : N.Inputs) :
  R.v1494 (state s) (inputs i) = Zmod.unsigned (N.v1494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1494 s i)) at 1.
  unfold R.v1494, N.v1494.
  rewrite ?node_1492.
  rewrite ?node_1493.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1495 (s : N.State) (i : N.Inputs) :
  R.v1495 (state s) (inputs i) = Zmod.unsigned (N.v1495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1495 s i)) at 1.
  unfold R.v1495, N.v1495.
  unfold R.v39, N.v39.
  rewrite ?node_1491.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1496 (s : N.State) (i : N.Inputs) :
  R.v1496 (state s) (inputs i) = Zmod.unsigned (N.v1496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1496 s i)) at 1.
  unfold R.v1496, N.v1496.
  unfold R.v42, N.v42.
  rewrite ?node_1491.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1497 (s : N.State) (i : N.Inputs) :
  R.v1497 (state s) (inputs i) = Zmod.unsigned (N.v1497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1497 s i)) at 1.
  unfold R.v1497, N.v1497.
  unfold R.v45, N.v45.
  rewrite ?node_1491.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1498 (s : N.State) (i : N.Inputs) :
  R.v1498 (state s) (inputs i) = Zmod.unsigned (N.v1498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1498 s i)) at 1.
  unfold R.v1498, N.v1498.
  unfold R.v47, N.v47.
  rewrite ?node_1491.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1499 (s : N.State) (i : N.Inputs) :
  R.v1499 (state s) (inputs i) = Zmod.unsigned (N.v1499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1499 s i)) at 1.
  unfold R.v1499, N.v1499.
  rewrite ?node_1497.
  rewrite ?node_1498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1500 (s : N.State) (i : N.Inputs) :
  R.v1500 (state s) (inputs i) = Zmod.unsigned (N.v1500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1500 s i)) at 1.
  unfold R.v1500, N.v1500.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_1499.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1501 (s : N.State) (i : N.Inputs) :
  R.v1501 (state s) (inputs i) = Zmod.unsigned (N.v1501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1501 s i)) at 1.
  unfold R.v1501, N.v1501.
  rewrite ?node_44.
  rewrite ?node_1496.
  rewrite ?node_1500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1502 (s : N.State) (i : N.Inputs) :
  R.v1502 (state s) (inputs i) = Zmod.unsigned (N.v1502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1502 s i)) at 1.
  unfold R.v1502, N.v1502.
  rewrite ?node_41.
  rewrite ?node_1495.
  rewrite ?node_1501.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1503 (s : N.State) (i : N.Inputs) :
  R.v1503 (state s) (inputs i) = Zmod.unsigned (N.v1503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1503 s i)) at 1.
  unfold R.v1503, N.v1503.
  rewrite ?node_38.
  rewrite ?node_1494.
  rewrite ?node_1502.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1504 (s : N.State) (i : N.Inputs) :
  R.v1504 (state s) (inputs i) = Zmod.unsigned (N.v1504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1504 s i)) at 1.
  unfold R.v1504, N.v1504.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1505 (s : N.State) (i : N.Inputs) :
  R.v1505 (state s) (inputs i) = Zmod.unsigned (N.v1505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1505 s i)) at 1.
  unfold R.v1505, N.v1505.
  rewrite ?node_1504.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r572_nr_5F572.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r572_nr_5F572 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1506 (s : N.State) (i : N.Inputs) :
  R.v1506 (state s) (inputs i) = Zmod.unsigned (N.v1506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1506 s i)) at 1.
  unfold R.v1506, N.v1506.
  unfold R.v6, N.v6.
  rewrite ?node_1495.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1507 (s : N.State) (i : N.Inputs) :
  R.v1507 (state s) (inputs i) = Zmod.unsigned (N.v1507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1507 s i)) at 1.
  unfold R.v1507, N.v1507.
  unfold R.v19, N.v19.
  rewrite ?node_1494.
  rewrite ?node_1506.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1508 (s : N.State) (i : N.Inputs) :
  R.v1508 (state s) (inputs i) = Zmod.unsigned (N.v1508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1508 s i)) at 1.
  unfold R.v1508, N.v1508.
  rewrite ?node_1507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1509 (s : N.State) (i : N.Inputs) :
  R.v1509 (state s) (inputs i) = Zmod.unsigned (N.v1509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1509 s i)) at 1.
  unfold R.v1509, N.v1509.
  rewrite ?node_1508.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r573_nr_5F573.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r573_nr_5F573 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1510 (s : N.State) (i : N.Inputs) :
  R.v1510 (state s) (inputs i) = Zmod.unsigned (N.v1510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1510 s i)) at 1.
  unfold R.v1510, N.v1510.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1511 (s : N.State) (i : N.Inputs) :
  R.v1511 (state s) (inputs i) = Zmod.unsigned (N.v1511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1511 s i)) at 1.
  unfold R.v1511, N.v1511.
  rewrite ?node_1510.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r574_nr_5F574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r574_nr_5F574 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1512 (s : N.State) (i : N.Inputs) :
  R.v1512 (state s) (inputs i) = Zmod.unsigned (N.v1512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1512 s i)) at 1.
  unfold R.v1512, N.v1512.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1513 (s : N.State) (i : N.Inputs) :
  R.v1513 (state s) (inputs i) = Zmod.unsigned (N.v1513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1513 s i)) at 1.
  unfold R.v1513, N.v1513.
  rewrite ?node_1512.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r575_nr_5F575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r575_nr_5F575 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1514 (s : N.State) (i : N.Inputs) :
  R.v1514 (state s) (inputs i) = Zmod.unsigned (N.v1514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1514 s i)) at 1.
  unfold R.v1514, N.v1514.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1515 (s : N.State) (i : N.Inputs) :
  R.v1515 (state s) (inputs i) = Zmod.unsigned (N.v1515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1515 s i)) at 1.
  unfold R.v1515, N.v1515.
  rewrite ?node_1514.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r576_nr_5F576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r576_nr_5F576 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1516 (s : N.State) (i : N.Inputs) :
  R.v1516 (state s) (inputs i) = Zmod.unsigned (N.v1516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1516 s i)) at 1.
  unfold R.v1516, N.v1516.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1517 (s : N.State) (i : N.Inputs) :
  R.v1517 (state s) (inputs i) = Zmod.unsigned (N.v1517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1517 s i)) at 1.
  unfold R.v1517, N.v1517.
  rewrite ?node_1516.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r577_nr_5F577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r577_nr_5F577 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1518 (s : N.State) (i : N.Inputs) :
  R.v1518 (state s) (inputs i) = Zmod.unsigned (N.v1518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1518 s i)) at 1.
  unfold R.v1518, N.v1518.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1519 (s : N.State) (i : N.Inputs) :
  R.v1519 (state s) (inputs i) = Zmod.unsigned (N.v1519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1519 s i)) at 1.
  unfold R.v1519, N.v1519.
  rewrite ?node_1518.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r578_nr_5F578.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r578_nr_5F578 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1520 (s : N.State) (i : N.Inputs) :
  R.v1520 (state s) (inputs i) = Zmod.unsigned (N.v1520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1520 s i)) at 1.
  unfold R.v1520, N.v1520.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1521 (s : N.State) (i : N.Inputs) :
  R.v1521 (state s) (inputs i) = Zmod.unsigned (N.v1521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1521 s i)) at 1.
  unfold R.v1521, N.v1521.
  rewrite ?node_1520.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r579_nr_5F579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r579_nr_5F579 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1522 (s : N.State) (i : N.Inputs) :
  R.v1522 (state s) (inputs i) = Zmod.unsigned (N.v1522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1522 s i)) at 1.
  unfold R.v1522, N.v1522.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1523 (s : N.State) (i : N.Inputs) :
  R.v1523 (state s) (inputs i) = Zmod.unsigned (N.v1523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1523 s i)) at 1.
  unfold R.v1523, N.v1523.
  rewrite ?node_1522.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r580_nr_5F580.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r580_nr_5F580 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1524 (s : N.State) (i : N.Inputs) :
  R.v1524 (state s) (inputs i) = Zmod.unsigned (N.v1524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1524 s i)) at 1.
  unfold R.v1524, N.v1524.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1525 (s : N.State) (i : N.Inputs) :
  R.v1525 (state s) (inputs i) = Zmod.unsigned (N.v1525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1525 s i)) at 1.
  unfold R.v1525, N.v1525.
  rewrite ?node_1524.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r581_nr_5F581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r581_nr_5F581 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1526 (s : N.State) (i : N.Inputs) :
  R.v1526 (state s) (inputs i) = Zmod.unsigned (N.v1526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1526 s i)) at 1.
  unfold R.v1526, N.v1526.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1527 (s : N.State) (i : N.Inputs) :
  R.v1527 (state s) (inputs i) = Zmod.unsigned (N.v1527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1527 s i)) at 1.
  unfold R.v1527, N.v1527.
  rewrite ?node_1526.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r582_nr_5F582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r582_nr_5F582 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1528 (s : N.State) (i : N.Inputs) :
  R.v1528 (state s) (inputs i) = Zmod.unsigned (N.v1528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1528 s i)) at 1.
  unfold R.v1528, N.v1528.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1529 (s : N.State) (i : N.Inputs) :
  R.v1529 (state s) (inputs i) = Zmod.unsigned (N.v1529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1529 s i)) at 1.
  unfold R.v1529, N.v1529.
  rewrite ?node_1528.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r583_nr_5F583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r583_nr_5F583 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1530 (s : N.State) (i : N.Inputs) :
  R.v1530 (state s) (inputs i) = Zmod.unsigned (N.v1530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1530 s i)) at 1.
  unfold R.v1530, N.v1530.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1531 (s : N.State) (i : N.Inputs) :
  R.v1531 (state s) (inputs i) = Zmod.unsigned (N.v1531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1531 s i)) at 1.
  unfold R.v1531, N.v1531.
  rewrite ?node_1530.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r584_nr_5F584.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r584_nr_5F584 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1532 (s : N.State) (i : N.Inputs) :
  R.v1532 (state s) (inputs i) = Zmod.unsigned (N.v1532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1532 s i)) at 1.
  unfold R.v1532, N.v1532.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1533 (s : N.State) (i : N.Inputs) :
  R.v1533 (state s) (inputs i) = Zmod.unsigned (N.v1533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1533 s i)) at 1.
  unfold R.v1533, N.v1533.
  rewrite ?node_1532.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r585_nr_5F585.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r585_nr_5F585 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1534 (s : N.State) (i : N.Inputs) :
  R.v1534 (state s) (inputs i) = Zmod.unsigned (N.v1534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1534 s i)) at 1.
  unfold R.v1534, N.v1534.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1535 (s : N.State) (i : N.Inputs) :
  R.v1535 (state s) (inputs i) = Zmod.unsigned (N.v1535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1535 s i)) at 1.
  unfold R.v1535, N.v1535.
  rewrite ?node_1534.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r586_nr_5F586.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r586_nr_5F586 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1536 (s : N.State) (i : N.Inputs) :
  R.v1536 (state s) (inputs i) = Zmod.unsigned (N.v1536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1536 s i)) at 1.
  unfold R.v1536, N.v1536.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1537 (s : N.State) (i : N.Inputs) :
  R.v1537 (state s) (inputs i) = Zmod.unsigned (N.v1537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1537 s i)) at 1.
  unfold R.v1537, N.v1537.
  rewrite ?node_1536.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r587_nr_5F587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r587_nr_5F587 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1538 (s : N.State) (i : N.Inputs) :
  R.v1538 (state s) (inputs i) = Zmod.unsigned (N.v1538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1538 s i)) at 1.
  unfold R.v1538, N.v1538.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1539 (s : N.State) (i : N.Inputs) :
  R.v1539 (state s) (inputs i) = Zmod.unsigned (N.v1539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1539 s i)) at 1.
  unfold R.v1539, N.v1539.
  rewrite ?node_1538.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r588_nr_5F588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r588_nr_5F588 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1540 (s : N.State) (i : N.Inputs) :
  R.v1540 (state s) (inputs i) = Zmod.unsigned (N.v1540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1540 s i)) at 1.
  unfold R.v1540, N.v1540.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1541 (s : N.State) (i : N.Inputs) :
  R.v1541 (state s) (inputs i) = Zmod.unsigned (N.v1541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1541 s i)) at 1.
  unfold R.v1541, N.v1541.
  rewrite ?node_1540.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r589_nr_5F589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r589_nr_5F589 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1542 (s : N.State) (i : N.Inputs) :
  R.v1542 (state s) (inputs i) = Zmod.unsigned (N.v1542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1542 s i)) at 1.
  unfold R.v1542, N.v1542.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1543 (s : N.State) (i : N.Inputs) :
  R.v1543 (state s) (inputs i) = Zmod.unsigned (N.v1543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1543 s i)) at 1.
  unfold R.v1543, N.v1543.
  rewrite ?node_1542.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r590_nr_5F590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r590_nr_5F590 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1544 (s : N.State) (i : N.Inputs) :
  R.v1544 (state s) (inputs i) = Zmod.unsigned (N.v1544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1544 s i)) at 1.
  unfold R.v1544, N.v1544.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1545 (s : N.State) (i : N.Inputs) :
  R.v1545 (state s) (inputs i) = Zmod.unsigned (N.v1545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1545 s i)) at 1.
  unfold R.v1545, N.v1545.
  rewrite ?node_1544.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r591_nr_5F591.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r591_nr_5F591 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1546 (s : N.State) (i : N.Inputs) :
  R.v1546 (state s) (inputs i) = Zmod.unsigned (N.v1546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1546 s i)) at 1.
  unfold R.v1546, N.v1546.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1547 (s : N.State) (i : N.Inputs) :
  R.v1547 (state s) (inputs i) = Zmod.unsigned (N.v1547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1547 s i)) at 1.
  unfold R.v1547, N.v1547.
  rewrite ?node_1546.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r592_nr_5F592.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r592_nr_5F592 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1548 (s : N.State) (i : N.Inputs) :
  R.v1548 (state s) (inputs i) = Zmod.unsigned (N.v1548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1548 s i)) at 1.
  unfold R.v1548, N.v1548.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1549 (s : N.State) (i : N.Inputs) :
  R.v1549 (state s) (inputs i) = Zmod.unsigned (N.v1549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1549 s i)) at 1.
  unfold R.v1549, N.v1549.
  rewrite ?node_1548.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r593_nr_5F593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r593_nr_5F593 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1550 (s : N.State) (i : N.Inputs) :
  R.v1550 (state s) (inputs i) = Zmod.unsigned (N.v1550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1550 s i)) at 1.
  unfold R.v1550, N.v1550.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1551 (s : N.State) (i : N.Inputs) :
  R.v1551 (state s) (inputs i) = Zmod.unsigned (N.v1551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1551 s i)) at 1.
  unfold R.v1551, N.v1551.
  rewrite ?node_1550.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r594_nr_5F594.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r594_nr_5F594 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1552 (s : N.State) (i : N.Inputs) :
  R.v1552 (state s) (inputs i) = Zmod.unsigned (N.v1552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1552 s i)) at 1.
  unfold R.v1552, N.v1552.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1553 (s : N.State) (i : N.Inputs) :
  R.v1553 (state s) (inputs i) = Zmod.unsigned (N.v1553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1553 s i)) at 1.
  unfold R.v1553, N.v1553.
  rewrite ?node_1552.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r595_nr_5F595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r595_nr_5F595 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1554 (s : N.State) (i : N.Inputs) :
  R.v1554 (state s) (inputs i) = Zmod.unsigned (N.v1554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1554 s i)) at 1.
  unfold R.v1554, N.v1554.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1555 (s : N.State) (i : N.Inputs) :
  R.v1555 (state s) (inputs i) = Zmod.unsigned (N.v1555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1555 s i)) at 1.
  unfold R.v1555, N.v1555.
  rewrite ?node_1554.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r596_nr_5F596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r596_nr_5F596 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1556 (s : N.State) (i : N.Inputs) :
  R.v1556 (state s) (inputs i) = Zmod.unsigned (N.v1556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1556 s i)) at 1.
  unfold R.v1556, N.v1556.
  rewrite ?node_1507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1557 (s : N.State) (i : N.Inputs) :
  R.v1557 (state s) (inputs i) = Zmod.unsigned (N.v1557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1557 s i)) at 1.
  unfold R.v1557, N.v1557.
  rewrite ?node_1556.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r597_nr_5F597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r597_nr_5F597 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1558 (s : N.State) (i : N.Inputs) :
  R.v1558 (state s) (inputs i) = Zmod.unsigned (N.v1558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1558 s i)) at 1.
  unfold R.v1558, N.v1558.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1559 (s : N.State) (i : N.Inputs) :
  R.v1559 (state s) (inputs i) = Zmod.unsigned (N.v1559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1559 s i)) at 1.
  unfold R.v1559, N.v1559.
  rewrite ?node_1558.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r598_nr_5F598.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r598_nr_5F598 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1560 (s : N.State) (i : N.Inputs) :
  R.v1560 (state s) (inputs i) = Zmod.unsigned (N.v1560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1560 s i)) at 1.
  unfold R.v1560, N.v1560.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1561 (s : N.State) (i : N.Inputs) :
  R.v1561 (state s) (inputs i) = Zmod.unsigned (N.v1561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1561 s i)) at 1.
  unfold R.v1561, N.v1561.
  rewrite ?node_1560.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r599_nr_5F599.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r599_nr_5F599 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1562 (s : N.State) (i : N.Inputs) :
  R.v1562 (state s) (inputs i) = Zmod.unsigned (N.v1562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1562 s i)) at 1.
  unfold R.v1562, N.v1562.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1563 (s : N.State) (i : N.Inputs) :
  R.v1563 (state s) (inputs i) = Zmod.unsigned (N.v1563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1563 s i)) at 1.
  unfold R.v1563, N.v1563.
  rewrite ?node_1562.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r600_nr_5F600.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r600_nr_5F600 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1564 (s : N.State) (i : N.Inputs) :
  R.v1564 (state s) (inputs i) = Zmod.unsigned (N.v1564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1564 s i)) at 1.
  unfold R.v1564, N.v1564.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1565 (s : N.State) (i : N.Inputs) :
  R.v1565 (state s) (inputs i) = Zmod.unsigned (N.v1565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1565 s i)) at 1.
  unfold R.v1565, N.v1565.
  rewrite ?node_1564.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r601_nr_5F601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r601_nr_5F601 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1566 (s : N.State) (i : N.Inputs) :
  R.v1566 (state s) (inputs i) = Zmod.unsigned (N.v1566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1566 s i)) at 1.
  unfold R.v1566, N.v1566.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1567 (s : N.State) (i : N.Inputs) :
  R.v1567 (state s) (inputs i) = Zmod.unsigned (N.v1567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1567 s i)) at 1.
  unfold R.v1567, N.v1567.
  rewrite ?node_1566.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r602_nr_5F602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r602_nr_5F602 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1568 (s : N.State) (i : N.Inputs) :
  R.v1568 (state s) (inputs i) = Zmod.unsigned (N.v1568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1568 s i)) at 1.
  unfold R.v1568, N.v1568.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1569 (s : N.State) (i : N.Inputs) :
  R.v1569 (state s) (inputs i) = Zmod.unsigned (N.v1569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1569 s i)) at 1.
  unfold R.v1569, N.v1569.
  rewrite ?node_1568.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r603_nr_5F603.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r603_nr_5F603 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1570 (s : N.State) (i : N.Inputs) :
  R.v1570 (state s) (inputs i) = Zmod.unsigned (N.v1570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1570 s i)) at 1.
  unfold R.v1570, N.v1570.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1571 (s : N.State) (i : N.Inputs) :
  R.v1571 (state s) (inputs i) = Zmod.unsigned (N.v1571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1571 s i)) at 1.
  unfold R.v1571, N.v1571.
  rewrite ?node_1570.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r604_nr_5F604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r604_nr_5F604 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1572 (s : N.State) (i : N.Inputs) :
  R.v1572 (state s) (inputs i) = Zmod.unsigned (N.v1572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1572 s i)) at 1.
  unfold R.v1572, N.v1572.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1573 (s : N.State) (i : N.Inputs) :
  R.v1573 (state s) (inputs i) = Zmod.unsigned (N.v1573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1573 s i)) at 1.
  unfold R.v1573, N.v1573.
  rewrite ?node_1572.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r605_nr_5F605.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r605_nr_5F605 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1574 (s : N.State) (i : N.Inputs) :
  R.v1574 (state s) (inputs i) = Zmod.unsigned (N.v1574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1574 s i)) at 1.
  unfold R.v1574, N.v1574.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1575 (s : N.State) (i : N.Inputs) :
  R.v1575 (state s) (inputs i) = Zmod.unsigned (N.v1575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1575 s i)) at 1.
  unfold R.v1575, N.v1575.
  rewrite ?node_1574.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r606_nr_5F606.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r606_nr_5F606 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1576 (s : N.State) (i : N.Inputs) :
  R.v1576 (state s) (inputs i) = Zmod.unsigned (N.v1576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1576 s i)) at 1.
  unfold R.v1576, N.v1576.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1577 (s : N.State) (i : N.Inputs) :
  R.v1577 (state s) (inputs i) = Zmod.unsigned (N.v1577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1577 s i)) at 1.
  unfold R.v1577, N.v1577.
  rewrite ?node_1576.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r607_nr_5F607.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r607_nr_5F607 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1578 (s : N.State) (i : N.Inputs) :
  R.v1578 (state s) (inputs i) = Zmod.unsigned (N.v1578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1578 s i)) at 1.
  unfold R.v1578, N.v1578.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1579 (s : N.State) (i : N.Inputs) :
  R.v1579 (state s) (inputs i) = Zmod.unsigned (N.v1579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1579 s i)) at 1.
  unfold R.v1579, N.v1579.
  rewrite ?node_1578.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r608_nr_5F608.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r608_nr_5F608 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1580 (s : N.State) (i : N.Inputs) :
  R.v1580 (state s) (inputs i) = Zmod.unsigned (N.v1580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1580 s i)) at 1.
  unfold R.v1580, N.v1580.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1581 (s : N.State) (i : N.Inputs) :
  R.v1581 (state s) (inputs i) = Zmod.unsigned (N.v1581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1581 s i)) at 1.
  unfold R.v1581, N.v1581.
  rewrite ?node_1580.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r609_nr_5F609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r609_nr_5F609 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1582 (s : N.State) (i : N.Inputs) :
  R.v1582 (state s) (inputs i) = Zmod.unsigned (N.v1582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1582 s i)) at 1.
  unfold R.v1582, N.v1582.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1583 (s : N.State) (i : N.Inputs) :
  R.v1583 (state s) (inputs i) = Zmod.unsigned (N.v1583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1583 s i)) at 1.
  unfold R.v1583, N.v1583.
  rewrite ?node_1582.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r610_nr_5F610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r610_nr_5F610 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1584 (s : N.State) (i : N.Inputs) :
  R.v1584 (state s) (inputs i) = Zmod.unsigned (N.v1584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1584 s i)) at 1.
  unfold R.v1584, N.v1584.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1585 (s : N.State) (i : N.Inputs) :
  R.v1585 (state s) (inputs i) = Zmod.unsigned (N.v1585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1585 s i)) at 1.
  unfold R.v1585, N.v1585.
  rewrite ?node_1584.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r611_nr_5F611.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r611_nr_5F611 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1586 (s : N.State) (i : N.Inputs) :
  R.v1586 (state s) (inputs i) = Zmod.unsigned (N.v1586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1586 s i)) at 1.
  unfold R.v1586, N.v1586.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1587 (s : N.State) (i : N.Inputs) :
  R.v1587 (state s) (inputs i) = Zmod.unsigned (N.v1587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1587 s i)) at 1.
  unfold R.v1587, N.v1587.
  rewrite ?node_1586.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r612_nr_5F612.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r612_nr_5F612 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1588 (s : N.State) (i : N.Inputs) :
  R.v1588 (state s) (inputs i) = Zmod.unsigned (N.v1588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1588 s i)) at 1.
  unfold R.v1588, N.v1588.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1589 (s : N.State) (i : N.Inputs) :
  R.v1589 (state s) (inputs i) = Zmod.unsigned (N.v1589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1589 s i)) at 1.
  unfold R.v1589, N.v1589.
  rewrite ?node_1588.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r613_nr_5F613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r613_nr_5F613 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1590 (s : N.State) (i : N.Inputs) :
  R.v1590 (state s) (inputs i) = Zmod.unsigned (N.v1590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1590 s i)) at 1.
  unfold R.v1590, N.v1590.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1591 (s : N.State) (i : N.Inputs) :
  R.v1591 (state s) (inputs i) = Zmod.unsigned (N.v1591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1591 s i)) at 1.
  unfold R.v1591, N.v1591.
  rewrite ?node_1590.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r614_nr_5F614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r614_nr_5F614 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1592 (s : N.State) (i : N.Inputs) :
  R.v1592 (state s) (inputs i) = Zmod.unsigned (N.v1592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1592 s i)) at 1.
  unfold R.v1592, N.v1592.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1593 (s : N.State) (i : N.Inputs) :
  R.v1593 (state s) (inputs i) = Zmod.unsigned (N.v1593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1593 s i)) at 1.
  unfold R.v1593, N.v1593.
  rewrite ?node_1592.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r615_nr_5F615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r615_nr_5F615 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1594 (s : N.State) (i : N.Inputs) :
  R.v1594 (state s) (inputs i) = Zmod.unsigned (N.v1594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1594 s i)) at 1.
  unfold R.v1594, N.v1594.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1595 (s : N.State) (i : N.Inputs) :
  R.v1595 (state s) (inputs i) = Zmod.unsigned (N.v1595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1595 s i)) at 1.
  unfold R.v1595, N.v1595.
  rewrite ?node_1594.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r616_nr_5F616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r616_nr_5F616 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1596 (s : N.State) (i : N.Inputs) :
  R.v1596 (state s) (inputs i) = Zmod.unsigned (N.v1596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1596 s i)) at 1.
  unfold R.v1596, N.v1596.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1597 (s : N.State) (i : N.Inputs) :
  R.v1597 (state s) (inputs i) = Zmod.unsigned (N.v1597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1597 s i)) at 1.
  unfold R.v1597, N.v1597.
  rewrite ?node_1596.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r617_nr_5F617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r617_nr_5F617 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1598 (s : N.State) (i : N.Inputs) :
  R.v1598 (state s) (inputs i) = Zmod.unsigned (N.v1598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1598 s i)) at 1.
  unfold R.v1598, N.v1598.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1599 (s : N.State) (i : N.Inputs) :
  R.v1599 (state s) (inputs i) = Zmod.unsigned (N.v1599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1599 s i)) at 1.
  unfold R.v1599, N.v1599.
  rewrite ?node_1598.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r618_nr_5F618.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r618_nr_5F618 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1600 (s : N.State) (i : N.Inputs) :
  R.v1600 (state s) (inputs i) = Zmod.unsigned (N.v1600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1600 s i)) at 1.
  unfold R.v1600, N.v1600.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1601 (s : N.State) (i : N.Inputs) :
  R.v1601 (state s) (inputs i) = Zmod.unsigned (N.v1601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1601 s i)) at 1.
  unfold R.v1601, N.v1601.
  rewrite ?node_1600.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r619_nr_5F619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r619_nr_5F619 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1602 (s : N.State) (i : N.Inputs) :
  R.v1602 (state s) (inputs i) = Zmod.unsigned (N.v1602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1602 s i)) at 1.
  unfold R.v1602, N.v1602.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1603 (s : N.State) (i : N.Inputs) :
  R.v1603 (state s) (inputs i) = Zmod.unsigned (N.v1603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1603 s i)) at 1.
  unfold R.v1603, N.v1603.
  rewrite ?node_1602.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r620_nr_5F620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r620_nr_5F620 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1604 (s : N.State) (i : N.Inputs) :
  R.v1604 (state s) (inputs i) = Zmod.unsigned (N.v1604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1604 s i)) at 1.
  unfold R.v1604, N.v1604.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1605 (s : N.State) (i : N.Inputs) :
  R.v1605 (state s) (inputs i) = Zmod.unsigned (N.v1605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1605 s i)) at 1.
  unfold R.v1605, N.v1605.
  unfold R.v33, N.v33.
  rewrite ?node_1604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1606 (s : N.State) (i : N.Inputs) :
  R.v1606 (state s) (inputs i) = Zmod.unsigned (N.v1606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1606 s i)) at 1.
  unfold R.v1606, N.v1606.
  unfold R.v35, N.v35.
  rewrite ?node_1604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1607 (s : N.State) (i : N.Inputs) :
  R.v1607 (state s) (inputs i) = Zmod.unsigned (N.v1607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1607 s i)) at 1.
  unfold R.v1607, N.v1607.
  rewrite ?node_1605.
  rewrite ?node_1606.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1608 (s : N.State) (i : N.Inputs) :
  R.v1608 (state s) (inputs i) = Zmod.unsigned (N.v1608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1608 s i)) at 1.
  unfold R.v1608, N.v1608.
  unfold R.v39, N.v39.
  rewrite ?node_1604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1609 (s : N.State) (i : N.Inputs) :
  R.v1609 (state s) (inputs i) = Zmod.unsigned (N.v1609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1609 s i)) at 1.
  unfold R.v1609, N.v1609.
  unfold R.v42, N.v42.
  rewrite ?node_1604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1610 (s : N.State) (i : N.Inputs) :
  R.v1610 (state s) (inputs i) = Zmod.unsigned (N.v1610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1610 s i)) at 1.
  unfold R.v1610, N.v1610.
  unfold R.v45, N.v45.
  rewrite ?node_1604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1611 (s : N.State) (i : N.Inputs) :
  R.v1611 (state s) (inputs i) = Zmod.unsigned (N.v1611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1611 s i)) at 1.
  unfold R.v1611, N.v1611.
  unfold R.v47, N.v47.
  rewrite ?node_1604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1612 (s : N.State) (i : N.Inputs) :
  R.v1612 (state s) (inputs i) = Zmod.unsigned (N.v1612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1612 s i)) at 1.
  unfold R.v1612, N.v1612.
  rewrite ?node_1610.
  rewrite ?node_1611.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1613 (s : N.State) (i : N.Inputs) :
  R.v1613 (state s) (inputs i) = Zmod.unsigned (N.v1613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1613 s i)) at 1.
  unfold R.v1613, N.v1613.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_1612.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1614 (s : N.State) (i : N.Inputs) :
  R.v1614 (state s) (inputs i) = Zmod.unsigned (N.v1614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1614 s i)) at 1.
  unfold R.v1614, N.v1614.
  rewrite ?node_44.
  rewrite ?node_1609.
  rewrite ?node_1613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1615 (s : N.State) (i : N.Inputs) :
  R.v1615 (state s) (inputs i) = Zmod.unsigned (N.v1615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1615 s i)) at 1.
  unfold R.v1615, N.v1615.
  rewrite ?node_41.
  rewrite ?node_1608.
  rewrite ?node_1614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1616 (s : N.State) (i : N.Inputs) :
  R.v1616 (state s) (inputs i) = Zmod.unsigned (N.v1616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1616 s i)) at 1.
  unfold R.v1616, N.v1616.
  rewrite ?node_38.
  rewrite ?node_1607.
  rewrite ?node_1615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1617 (s : N.State) (i : N.Inputs) :
  R.v1617 (state s) (inputs i) = Zmod.unsigned (N.v1617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1617 s i)) at 1.
  unfold R.v1617, N.v1617.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1618 (s : N.State) (i : N.Inputs) :
  R.v1618 (state s) (inputs i) = Zmod.unsigned (N.v1618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1618 s i)) at 1.
  unfold R.v1618, N.v1618.
  rewrite ?node_1617.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r621_nr_5F621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r621_nr_5F621 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1619 (s : N.State) (i : N.Inputs) :
  R.v1619 (state s) (inputs i) = Zmod.unsigned (N.v1619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1619 s i)) at 1.
  unfold R.v1619, N.v1619.
  unfold R.v6, N.v6.
  rewrite ?node_1608.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1620 (s : N.State) (i : N.Inputs) :
  R.v1620 (state s) (inputs i) = Zmod.unsigned (N.v1620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1620 s i)) at 1.
  unfold R.v1620, N.v1620.
  unfold R.v19, N.v19.
  rewrite ?node_1607.
  rewrite ?node_1619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1621 (s : N.State) (i : N.Inputs) :
  R.v1621 (state s) (inputs i) = Zmod.unsigned (N.v1621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1621 s i)) at 1.
  unfold R.v1621, N.v1621.
  rewrite ?node_1620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1622 (s : N.State) (i : N.Inputs) :
  R.v1622 (state s) (inputs i) = Zmod.unsigned (N.v1622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1622 s i)) at 1.
  unfold R.v1622, N.v1622.
  rewrite ?node_1621.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r622_nr_5F622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r622_nr_5F622 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1623 (s : N.State) (i : N.Inputs) :
  R.v1623 (state s) (inputs i) = Zmod.unsigned (N.v1623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1623 s i)) at 1.
  unfold R.v1623, N.v1623.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1624 (s : N.State) (i : N.Inputs) :
  R.v1624 (state s) (inputs i) = Zmod.unsigned (N.v1624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1624 s i)) at 1.
  unfold R.v1624, N.v1624.
  rewrite ?node_1623.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r623_nr_5F623.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r623_nr_5F623 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1625 (s : N.State) (i : N.Inputs) :
  R.v1625 (state s) (inputs i) = Zmod.unsigned (N.v1625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1625 s i)) at 1.
  unfold R.v1625, N.v1625.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1626 (s : N.State) (i : N.Inputs) :
  R.v1626 (state s) (inputs i) = Zmod.unsigned (N.v1626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1626 s i)) at 1.
  unfold R.v1626, N.v1626.
  rewrite ?node_1625.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r624_nr_5F624.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r624_nr_5F624 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1627 (s : N.State) (i : N.Inputs) :
  R.v1627 (state s) (inputs i) = Zmod.unsigned (N.v1627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1627 s i)) at 1.
  unfold R.v1627, N.v1627.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1628 (s : N.State) (i : N.Inputs) :
  R.v1628 (state s) (inputs i) = Zmod.unsigned (N.v1628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1628 s i)) at 1.
  unfold R.v1628, N.v1628.
  rewrite ?node_1627.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r625_nr_5F625.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r625_nr_5F625 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1629 (s : N.State) (i : N.Inputs) :
  R.v1629 (state s) (inputs i) = Zmod.unsigned (N.v1629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1629 s i)) at 1.
  unfold R.v1629, N.v1629.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1630 (s : N.State) (i : N.Inputs) :
  R.v1630 (state s) (inputs i) = Zmod.unsigned (N.v1630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1630 s i)) at 1.
  unfold R.v1630, N.v1630.
  rewrite ?node_1629.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r626_nr_5F626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r626_nr_5F626 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1631 (s : N.State) (i : N.Inputs) :
  R.v1631 (state s) (inputs i) = Zmod.unsigned (N.v1631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1631 s i)) at 1.
  unfold R.v1631, N.v1631.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1632 (s : N.State) (i : N.Inputs) :
  R.v1632 (state s) (inputs i) = Zmod.unsigned (N.v1632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1632 s i)) at 1.
  unfold R.v1632, N.v1632.
  rewrite ?node_1631.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r627_nr_5F627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r627_nr_5F627 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1633 (s : N.State) (i : N.Inputs) :
  R.v1633 (state s) (inputs i) = Zmod.unsigned (N.v1633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1633 s i)) at 1.
  unfold R.v1633, N.v1633.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1634 (s : N.State) (i : N.Inputs) :
  R.v1634 (state s) (inputs i) = Zmod.unsigned (N.v1634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1634 s i)) at 1.
  unfold R.v1634, N.v1634.
  rewrite ?node_1633.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r628_nr_5F628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r628_nr_5F628 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1635 (s : N.State) (i : N.Inputs) :
  R.v1635 (state s) (inputs i) = Zmod.unsigned (N.v1635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1635 s i)) at 1.
  unfold R.v1635, N.v1635.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1636 (s : N.State) (i : N.Inputs) :
  R.v1636 (state s) (inputs i) = Zmod.unsigned (N.v1636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1636 s i)) at 1.
  unfold R.v1636, N.v1636.
  rewrite ?node_1635.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r629_nr_5F629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r629_nr_5F629 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1637 (s : N.State) (i : N.Inputs) :
  R.v1637 (state s) (inputs i) = Zmod.unsigned (N.v1637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1637 s i)) at 1.
  unfold R.v1637, N.v1637.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1638 (s : N.State) (i : N.Inputs) :
  R.v1638 (state s) (inputs i) = Zmod.unsigned (N.v1638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1638 s i)) at 1.
  unfold R.v1638, N.v1638.
  rewrite ?node_1637.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r630_nr_5F630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r630_nr_5F630 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1639 (s : N.State) (i : N.Inputs) :
  R.v1639 (state s) (inputs i) = Zmod.unsigned (N.v1639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1639 s i)) at 1.
  unfold R.v1639, N.v1639.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1640 (s : N.State) (i : N.Inputs) :
  R.v1640 (state s) (inputs i) = Zmod.unsigned (N.v1640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1640 s i)) at 1.
  unfold R.v1640, N.v1640.
  rewrite ?node_1639.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r631_nr_5F631.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r631_nr_5F631 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1641 (s : N.State) (i : N.Inputs) :
  R.v1641 (state s) (inputs i) = Zmod.unsigned (N.v1641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1641 s i)) at 1.
  unfold R.v1641, N.v1641.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1642 (s : N.State) (i : N.Inputs) :
  R.v1642 (state s) (inputs i) = Zmod.unsigned (N.v1642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1642 s i)) at 1.
  unfold R.v1642, N.v1642.
  rewrite ?node_1641.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r632_nr_5F632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r632_nr_5F632 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1643 (s : N.State) (i : N.Inputs) :
  R.v1643 (state s) (inputs i) = Zmod.unsigned (N.v1643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1643 s i)) at 1.
  unfold R.v1643, N.v1643.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1644 (s : N.State) (i : N.Inputs) :
  R.v1644 (state s) (inputs i) = Zmod.unsigned (N.v1644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1644 s i)) at 1.
  unfold R.v1644, N.v1644.
  rewrite ?node_1643.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r633_nr_5F633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r633_nr_5F633 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1645 (s : N.State) (i : N.Inputs) :
  R.v1645 (state s) (inputs i) = Zmod.unsigned (N.v1645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1645 s i)) at 1.
  unfold R.v1645, N.v1645.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1646 (s : N.State) (i : N.Inputs) :
  R.v1646 (state s) (inputs i) = Zmod.unsigned (N.v1646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1646 s i)) at 1.
  unfold R.v1646, N.v1646.
  rewrite ?node_1645.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r634_nr_5F634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r634_nr_5F634 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1647 (s : N.State) (i : N.Inputs) :
  R.v1647 (state s) (inputs i) = Zmod.unsigned (N.v1647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1647 s i)) at 1.
  unfold R.v1647, N.v1647.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1648 (s : N.State) (i : N.Inputs) :
  R.v1648 (state s) (inputs i) = Zmod.unsigned (N.v1648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1648 s i)) at 1.
  unfold R.v1648, N.v1648.
  rewrite ?node_1647.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r635_nr_5F635.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r635_nr_5F635 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1649 (s : N.State) (i : N.Inputs) :
  R.v1649 (state s) (inputs i) = Zmod.unsigned (N.v1649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1649 s i)) at 1.
  unfold R.v1649, N.v1649.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1650 (s : N.State) (i : N.Inputs) :
  R.v1650 (state s) (inputs i) = Zmod.unsigned (N.v1650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1650 s i)) at 1.
  unfold R.v1650, N.v1650.
  rewrite ?node_1649.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r636_nr_5F636.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r636_nr_5F636 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1651 (s : N.State) (i : N.Inputs) :
  R.v1651 (state s) (inputs i) = Zmod.unsigned (N.v1651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1651 s i)) at 1.
  unfold R.v1651, N.v1651.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1652 (s : N.State) (i : N.Inputs) :
  R.v1652 (state s) (inputs i) = Zmod.unsigned (N.v1652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1652 s i)) at 1.
  unfold R.v1652, N.v1652.
  rewrite ?node_1651.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r637_nr_5F637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r637_nr_5F637 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1653 (s : N.State) (i : N.Inputs) :
  R.v1653 (state s) (inputs i) = Zmod.unsigned (N.v1653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1653 s i)) at 1.
  unfold R.v1653, N.v1653.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1654 (s : N.State) (i : N.Inputs) :
  R.v1654 (state s) (inputs i) = Zmod.unsigned (N.v1654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1654 s i)) at 1.
  unfold R.v1654, N.v1654.
  rewrite ?node_1653.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r638_nr_5F638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r638_nr_5F638 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1655 (s : N.State) (i : N.Inputs) :
  R.v1655 (state s) (inputs i) = Zmod.unsigned (N.v1655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1655 s i)) at 1.
  unfold R.v1655, N.v1655.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1656 (s : N.State) (i : N.Inputs) :
  R.v1656 (state s) (inputs i) = Zmod.unsigned (N.v1656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1656 s i)) at 1.
  unfold R.v1656, N.v1656.
  rewrite ?node_1655.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r639_nr_5F639.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r639_nr_5F639 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1657 (s : N.State) (i : N.Inputs) :
  R.v1657 (state s) (inputs i) = Zmod.unsigned (N.v1657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1657 s i)) at 1.
  unfold R.v1657, N.v1657.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1658 (s : N.State) (i : N.Inputs) :
  R.v1658 (state s) (inputs i) = Zmod.unsigned (N.v1658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1658 s i)) at 1.
  unfold R.v1658, N.v1658.
  rewrite ?node_1657.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r640_nr_5F640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r640_nr_5F640 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1659 (s : N.State) (i : N.Inputs) :
  R.v1659 (state s) (inputs i) = Zmod.unsigned (N.v1659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1659 s i)) at 1.
  unfold R.v1659, N.v1659.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1660 (s : N.State) (i : N.Inputs) :
  R.v1660 (state s) (inputs i) = Zmod.unsigned (N.v1660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1660 s i)) at 1.
  unfold R.v1660, N.v1660.
  rewrite ?node_1659.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r641_nr_5F641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r641_nr_5F641 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1661 (s : N.State) (i : N.Inputs) :
  R.v1661 (state s) (inputs i) = Zmod.unsigned (N.v1661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1661 s i)) at 1.
  unfold R.v1661, N.v1661.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1662 (s : N.State) (i : N.Inputs) :
  R.v1662 (state s) (inputs i) = Zmod.unsigned (N.v1662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1662 s i)) at 1.
  unfold R.v1662, N.v1662.
  rewrite ?node_1661.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r642_nr_5F642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r642_nr_5F642 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1663 (s : N.State) (i : N.Inputs) :
  R.v1663 (state s) (inputs i) = Zmod.unsigned (N.v1663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1663 s i)) at 1.
  unfold R.v1663, N.v1663.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1664 (s : N.State) (i : N.Inputs) :
  R.v1664 (state s) (inputs i) = Zmod.unsigned (N.v1664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1664 s i)) at 1.
  unfold R.v1664, N.v1664.
  rewrite ?node_1663.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r643_nr_5F643.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r643_nr_5F643 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1665 (s : N.State) (i : N.Inputs) :
  R.v1665 (state s) (inputs i) = Zmod.unsigned (N.v1665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1665 s i)) at 1.
  unfold R.v1665, N.v1665.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1666 (s : N.State) (i : N.Inputs) :
  R.v1666 (state s) (inputs i) = Zmod.unsigned (N.v1666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1666 s i)) at 1.
  unfold R.v1666, N.v1666.
  rewrite ?node_1665.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r644_nr_5F644.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r644_nr_5F644 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1667 (s : N.State) (i : N.Inputs) :
  R.v1667 (state s) (inputs i) = Zmod.unsigned (N.v1667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1667 s i)) at 1.
  unfold R.v1667, N.v1667.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1668 (s : N.State) (i : N.Inputs) :
  R.v1668 (state s) (inputs i) = Zmod.unsigned (N.v1668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1668 s i)) at 1.
  unfold R.v1668, N.v1668.
  rewrite ?node_1667.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r645_nr_5F645.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r645_nr_5F645 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1669 (s : N.State) (i : N.Inputs) :
  R.v1669 (state s) (inputs i) = Zmod.unsigned (N.v1669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1669 s i)) at 1.
  unfold R.v1669, N.v1669.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1670 (s : N.State) (i : N.Inputs) :
  R.v1670 (state s) (inputs i) = Zmod.unsigned (N.v1670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1670 s i)) at 1.
  unfold R.v1670, N.v1670.
  rewrite ?node_1669.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r646_nr_5F646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r646_nr_5F646 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1671 (s : N.State) (i : N.Inputs) :
  R.v1671 (state s) (inputs i) = Zmod.unsigned (N.v1671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1671 s i)) at 1.
  unfold R.v1671, N.v1671.
  rewrite ?node_1620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1672 (s : N.State) (i : N.Inputs) :
  R.v1672 (state s) (inputs i) = Zmod.unsigned (N.v1672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1672 s i)) at 1.
  unfold R.v1672, N.v1672.
  rewrite ?node_1671.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r647_nr_5F647.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r647_nr_5F647 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1673 (s : N.State) (i : N.Inputs) :
  R.v1673 (state s) (inputs i) = Zmod.unsigned (N.v1673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1673 s i)) at 1.
  unfold R.v1673, N.v1673.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1674 (s : N.State) (i : N.Inputs) :
  R.v1674 (state s) (inputs i) = Zmod.unsigned (N.v1674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1674 s i)) at 1.
  unfold R.v1674, N.v1674.
  rewrite ?node_1673.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r648_nr_5F648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r648_nr_5F648 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1675 (s : N.State) (i : N.Inputs) :
  R.v1675 (state s) (inputs i) = Zmod.unsigned (N.v1675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1675 s i)) at 1.
  unfold R.v1675, N.v1675.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1676 (s : N.State) (i : N.Inputs) :
  R.v1676 (state s) (inputs i) = Zmod.unsigned (N.v1676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1676 s i)) at 1.
  unfold R.v1676, N.v1676.
  rewrite ?node_1675.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r649_nr_5F649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r649_nr_5F649 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1677 (s : N.State) (i : N.Inputs) :
  R.v1677 (state s) (inputs i) = Zmod.unsigned (N.v1677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1677 s i)) at 1.
  unfold R.v1677, N.v1677.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1678 (s : N.State) (i : N.Inputs) :
  R.v1678 (state s) (inputs i) = Zmod.unsigned (N.v1678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1678 s i)) at 1.
  unfold R.v1678, N.v1678.
  rewrite ?node_1677.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r650_nr_5F650.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r650_nr_5F650 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1679 (s : N.State) (i : N.Inputs) :
  R.v1679 (state s) (inputs i) = Zmod.unsigned (N.v1679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1679 s i)) at 1.
  unfold R.v1679, N.v1679.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1680 (s : N.State) (i : N.Inputs) :
  R.v1680 (state s) (inputs i) = Zmod.unsigned (N.v1680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1680 s i)) at 1.
  unfold R.v1680, N.v1680.
  rewrite ?node_1679.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r651_nr_5F651.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r651_nr_5F651 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1681 (s : N.State) (i : N.Inputs) :
  R.v1681 (state s) (inputs i) = Zmod.unsigned (N.v1681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1681 s i)) at 1.
  unfold R.v1681, N.v1681.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1682 (s : N.State) (i : N.Inputs) :
  R.v1682 (state s) (inputs i) = Zmod.unsigned (N.v1682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1682 s i)) at 1.
  unfold R.v1682, N.v1682.
  rewrite ?node_1681.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r652_nr_5F652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r652_nr_5F652 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1683 (s : N.State) (i : N.Inputs) :
  R.v1683 (state s) (inputs i) = Zmod.unsigned (N.v1683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1683 s i)) at 1.
  unfold R.v1683, N.v1683.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1684 (s : N.State) (i : N.Inputs) :
  R.v1684 (state s) (inputs i) = Zmod.unsigned (N.v1684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1684 s i)) at 1.
  unfold R.v1684, N.v1684.
  rewrite ?node_1683.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r653_nr_5F653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r653_nr_5F653 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1685 (s : N.State) (i : N.Inputs) :
  R.v1685 (state s) (inputs i) = Zmod.unsigned (N.v1685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1685 s i)) at 1.
  unfold R.v1685, N.v1685.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1686 (s : N.State) (i : N.Inputs) :
  R.v1686 (state s) (inputs i) = Zmod.unsigned (N.v1686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1686 s i)) at 1.
  unfold R.v1686, N.v1686.
  rewrite ?node_1685.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r654_nr_5F654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r654_nr_5F654 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1687 (s : N.State) (i : N.Inputs) :
  R.v1687 (state s) (inputs i) = Zmod.unsigned (N.v1687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1687 s i)) at 1.
  unfold R.v1687, N.v1687.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1688 (s : N.State) (i : N.Inputs) :
  R.v1688 (state s) (inputs i) = Zmod.unsigned (N.v1688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1688 s i)) at 1.
  unfold R.v1688, N.v1688.
  rewrite ?node_1687.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r655_nr_5F655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r655_nr_5F655 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1689 (s : N.State) (i : N.Inputs) :
  R.v1689 (state s) (inputs i) = Zmod.unsigned (N.v1689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1689 s i)) at 1.
  unfold R.v1689, N.v1689.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1690 (s : N.State) (i : N.Inputs) :
  R.v1690 (state s) (inputs i) = Zmod.unsigned (N.v1690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1690 s i)) at 1.
  unfold R.v1690, N.v1690.
  rewrite ?node_1689.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r656_nr_5F656.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r656_nr_5F656 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1691 (s : N.State) (i : N.Inputs) :
  R.v1691 (state s) (inputs i) = Zmod.unsigned (N.v1691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1691 s i)) at 1.
  unfold R.v1691, N.v1691.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1692 (s : N.State) (i : N.Inputs) :
  R.v1692 (state s) (inputs i) = Zmod.unsigned (N.v1692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1692 s i)) at 1.
  unfold R.v1692, N.v1692.
  rewrite ?node_1691.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r657_nr_5F657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r657_nr_5F657 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1693 (s : N.State) (i : N.Inputs) :
  R.v1693 (state s) (inputs i) = Zmod.unsigned (N.v1693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1693 s i)) at 1.
  unfold R.v1693, N.v1693.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1694 (s : N.State) (i : N.Inputs) :
  R.v1694 (state s) (inputs i) = Zmod.unsigned (N.v1694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1694 s i)) at 1.
  unfold R.v1694, N.v1694.
  rewrite ?node_1693.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r658_nr_5F658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r658_nr_5F658 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1695 (s : N.State) (i : N.Inputs) :
  R.v1695 (state s) (inputs i) = Zmod.unsigned (N.v1695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1695 s i)) at 1.
  unfold R.v1695, N.v1695.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1696 (s : N.State) (i : N.Inputs) :
  R.v1696 (state s) (inputs i) = Zmod.unsigned (N.v1696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1696 s i)) at 1.
  unfold R.v1696, N.v1696.
  rewrite ?node_1695.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r659_nr_5F659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r659_nr_5F659 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1697 (s : N.State) (i : N.Inputs) :
  R.v1697 (state s) (inputs i) = Zmod.unsigned (N.v1697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1697 s i)) at 1.
  unfold R.v1697, N.v1697.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1698 (s : N.State) (i : N.Inputs) :
  R.v1698 (state s) (inputs i) = Zmod.unsigned (N.v1698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1698 s i)) at 1.
  unfold R.v1698, N.v1698.
  rewrite ?node_1697.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r660_nr_5F660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r660_nr_5F660 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1699 (s : N.State) (i : N.Inputs) :
  R.v1699 (state s) (inputs i) = Zmod.unsigned (N.v1699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1699 s i)) at 1.
  unfold R.v1699, N.v1699.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1700 (s : N.State) (i : N.Inputs) :
  R.v1700 (state s) (inputs i) = Zmod.unsigned (N.v1700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1700 s i)) at 1.
  unfold R.v1700, N.v1700.
  rewrite ?node_1699.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r661_nr_5F661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r661_nr_5F661 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1701 (s : N.State) (i : N.Inputs) :
  R.v1701 (state s) (inputs i) = Zmod.unsigned (N.v1701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1701 s i)) at 1.
  unfold R.v1701, N.v1701.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1702 (s : N.State) (i : N.Inputs) :
  R.v1702 (state s) (inputs i) = Zmod.unsigned (N.v1702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1702 s i)) at 1.
  unfold R.v1702, N.v1702.
  rewrite ?node_1701.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r662_nr_5F662.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r662_nr_5F662 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1703 (s : N.State) (i : N.Inputs) :
  R.v1703 (state s) (inputs i) = Zmod.unsigned (N.v1703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1703 s i)) at 1.
  unfold R.v1703, N.v1703.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1704 (s : N.State) (i : N.Inputs) :
  R.v1704 (state s) (inputs i) = Zmod.unsigned (N.v1704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1704 s i)) at 1.
  unfold R.v1704, N.v1704.
  rewrite ?node_1703.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r663_nr_5F663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r663_nr_5F663 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1705 (s : N.State) (i : N.Inputs) :
  R.v1705 (state s) (inputs i) = Zmod.unsigned (N.v1705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1705 s i)) at 1.
  unfold R.v1705, N.v1705.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1706 (s : N.State) (i : N.Inputs) :
  R.v1706 (state s) (inputs i) = Zmod.unsigned (N.v1706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1706 s i)) at 1.
  unfold R.v1706, N.v1706.
  rewrite ?node_1705.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r664_nr_5F664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r664_nr_5F664 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1707 (s : N.State) (i : N.Inputs) :
  R.v1707 (state s) (inputs i) = Zmod.unsigned (N.v1707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1707 s i)) at 1.
  unfold R.v1707, N.v1707.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1708 (s : N.State) (i : N.Inputs) :
  R.v1708 (state s) (inputs i) = Zmod.unsigned (N.v1708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1708 s i)) at 1.
  unfold R.v1708, N.v1708.
  rewrite ?node_1707.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r665_nr_5F665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r665_nr_5F665 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1709 (s : N.State) (i : N.Inputs) :
  R.v1709 (state s) (inputs i) = Zmod.unsigned (N.v1709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1709 s i)) at 1.
  unfold R.v1709, N.v1709.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1710 (s : N.State) (i : N.Inputs) :
  R.v1710 (state s) (inputs i) = Zmod.unsigned (N.v1710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1710 s i)) at 1.
  unfold R.v1710, N.v1710.
  rewrite ?node_1709.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r666_nr_5F666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r666_nr_5F666 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1711 (s : N.State) (i : N.Inputs) :
  R.v1711 (state s) (inputs i) = Zmod.unsigned (N.v1711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1711 s i)) at 1.
  unfold R.v1711, N.v1711.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1712 (s : N.State) (i : N.Inputs) :
  R.v1712 (state s) (inputs i) = Zmod.unsigned (N.v1712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1712 s i)) at 1.
  unfold R.v1712, N.v1712.
  rewrite ?node_1711.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r667_nr_5F667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r667_nr_5F667 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1713 (s : N.State) (i : N.Inputs) :
  R.v1713 (state s) (inputs i) = Zmod.unsigned (N.v1713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1713 s i)) at 1.
  unfold R.v1713, N.v1713.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1714 (s : N.State) (i : N.Inputs) :
  R.v1714 (state s) (inputs i) = Zmod.unsigned (N.v1714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1714 s i)) at 1.
  unfold R.v1714, N.v1714.
  rewrite ?node_1713.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r668_nr_5F668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r668_nr_5F668 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1715 (s : N.State) (i : N.Inputs) :
  R.v1715 (state s) (inputs i) = Zmod.unsigned (N.v1715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1715 s i)) at 1.
  unfold R.v1715, N.v1715.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1716 (s : N.State) (i : N.Inputs) :
  R.v1716 (state s) (inputs i) = Zmod.unsigned (N.v1716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1716 s i)) at 1.
  unfold R.v1716, N.v1716.
  rewrite ?node_1715.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r669_nr_5F669.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r669_nr_5F669 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1717 (s : N.State) (i : N.Inputs) :
  R.v1717 (state s) (inputs i) = Zmod.unsigned (N.v1717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1717 s i)) at 1.
  unfold R.v1717, N.v1717.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1718 (s : N.State) (i : N.Inputs) :
  R.v1718 (state s) (inputs i) = Zmod.unsigned (N.v1718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1718 s i)) at 1.
  unfold R.v1718, N.v1718.
  rewrite ?node_1717.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r670_nr_5F670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r670_nr_5F670 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1719 (s : N.State) (i : N.Inputs) :
  R.v1719 (state s) (inputs i) = Zmod.unsigned (N.v1719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1719 s i)) at 1.
  unfold R.v1719, N.v1719.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1720 (s : N.State) (i : N.Inputs) :
  R.v1720 (state s) (inputs i) = Zmod.unsigned (N.v1720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1720 s i)) at 1.
  unfold R.v1720, N.v1720.
  rewrite ?node_1719.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r671_nr_5F671.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r671_nr_5F671 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1721 (s : N.State) (i : N.Inputs) :
  R.v1721 (state s) (inputs i) = Zmod.unsigned (N.v1721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1721 s i)) at 1.
  unfold R.v1721, N.v1721.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1722 (s : N.State) (i : N.Inputs) :
  R.v1722 (state s) (inputs i) = Zmod.unsigned (N.v1722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1722 s i)) at 1.
  unfold R.v1722, N.v1722.
  unfold R.v33, N.v33.
  rewrite ?node_1721.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1723 (s : N.State) (i : N.Inputs) :
  R.v1723 (state s) (inputs i) = Zmod.unsigned (N.v1723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1723 s i)) at 1.
  unfold R.v1723, N.v1723.
  unfold R.v35, N.v35.
  rewrite ?node_1721.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1724 (s : N.State) (i : N.Inputs) :
  R.v1724 (state s) (inputs i) = Zmod.unsigned (N.v1724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1724 s i)) at 1.
  unfold R.v1724, N.v1724.
  rewrite ?node_1722.
  rewrite ?node_1723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1725 (s : N.State) (i : N.Inputs) :
  R.v1725 (state s) (inputs i) = Zmod.unsigned (N.v1725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1725 s i)) at 1.
  unfold R.v1725, N.v1725.
  unfold R.v39, N.v39.
  rewrite ?node_1721.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1726 (s : N.State) (i : N.Inputs) :
  R.v1726 (state s) (inputs i) = Zmod.unsigned (N.v1726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1726 s i)) at 1.
  unfold R.v1726, N.v1726.
  unfold R.v42, N.v42.
  rewrite ?node_1721.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1727 (s : N.State) (i : N.Inputs) :
  R.v1727 (state s) (inputs i) = Zmod.unsigned (N.v1727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1727 s i)) at 1.
  unfold R.v1727, N.v1727.
  unfold R.v45, N.v45.
  rewrite ?node_1721.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1728 (s : N.State) (i : N.Inputs) :
  R.v1728 (state s) (inputs i) = Zmod.unsigned (N.v1728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1728 s i)) at 1.
  unfold R.v1728, N.v1728.
  unfold R.v47, N.v47.
  rewrite ?node_1721.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1729 (s : N.State) (i : N.Inputs) :
  R.v1729 (state s) (inputs i) = Zmod.unsigned (N.v1729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1729 s i)) at 1.
  unfold R.v1729, N.v1729.
  rewrite ?node_1727.
  rewrite ?node_1728.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1730 (s : N.State) (i : N.Inputs) :
  R.v1730 (state s) (inputs i) = Zmod.unsigned (N.v1730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1730 s i)) at 1.
  unfold R.v1730, N.v1730.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_1729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1731 (s : N.State) (i : N.Inputs) :
  R.v1731 (state s) (inputs i) = Zmod.unsigned (N.v1731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1731 s i)) at 1.
  unfold R.v1731, N.v1731.
  rewrite ?node_44.
  rewrite ?node_1726.
  rewrite ?node_1730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1732 (s : N.State) (i : N.Inputs) :
  R.v1732 (state s) (inputs i) = Zmod.unsigned (N.v1732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1732 s i)) at 1.
  unfold R.v1732, N.v1732.
  rewrite ?node_41.
  rewrite ?node_1725.
  rewrite ?node_1731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1733 (s : N.State) (i : N.Inputs) :
  R.v1733 (state s) (inputs i) = Zmod.unsigned (N.v1733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1733 s i)) at 1.
  unfold R.v1733, N.v1733.
  rewrite ?node_38.
  rewrite ?node_1724.
  rewrite ?node_1732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1734 (s : N.State) (i : N.Inputs) :
  R.v1734 (state s) (inputs i) = Zmod.unsigned (N.v1734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1734 s i)) at 1.
  unfold R.v1734, N.v1734.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1735 (s : N.State) (i : N.Inputs) :
  R.v1735 (state s) (inputs i) = Zmod.unsigned (N.v1735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1735 s i)) at 1.
  unfold R.v1735, N.v1735.
  rewrite ?node_1734.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r672_nr_5F672.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r672_nr_5F672 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1736 (s : N.State) (i : N.Inputs) :
  R.v1736 (state s) (inputs i) = Zmod.unsigned (N.v1736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1736 s i)) at 1.
  unfold R.v1736, N.v1736.
  unfold R.v6, N.v6.
  rewrite ?node_1725.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1737 (s : N.State) (i : N.Inputs) :
  R.v1737 (state s) (inputs i) = Zmod.unsigned (N.v1737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1737 s i)) at 1.
  unfold R.v1737, N.v1737.
  unfold R.v19, N.v19.
  rewrite ?node_1724.
  rewrite ?node_1736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1738 (s : N.State) (i : N.Inputs) :
  R.v1738 (state s) (inputs i) = Zmod.unsigned (N.v1738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1738 s i)) at 1.
  unfold R.v1738, N.v1738.
  rewrite ?node_1737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1739 (s : N.State) (i : N.Inputs) :
  R.v1739 (state s) (inputs i) = Zmod.unsigned (N.v1739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1739 s i)) at 1.
  unfold R.v1739, N.v1739.
  rewrite ?node_1738.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r673_nr_5F673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r673_nr_5F673 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1740 (s : N.State) (i : N.Inputs) :
  R.v1740 (state s) (inputs i) = Zmod.unsigned (N.v1740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1740 s i)) at 1.
  unfold R.v1740, N.v1740.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1741 (s : N.State) (i : N.Inputs) :
  R.v1741 (state s) (inputs i) = Zmod.unsigned (N.v1741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1741 s i)) at 1.
  unfold R.v1741, N.v1741.
  rewrite ?node_1740.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r674_nr_5F674.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r674_nr_5F674 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1742 (s : N.State) (i : N.Inputs) :
  R.v1742 (state s) (inputs i) = Zmod.unsigned (N.v1742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1742 s i)) at 1.
  unfold R.v1742, N.v1742.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1743 (s : N.State) (i : N.Inputs) :
  R.v1743 (state s) (inputs i) = Zmod.unsigned (N.v1743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1743 s i)) at 1.
  unfold R.v1743, N.v1743.
  rewrite ?node_1742.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r675_nr_5F675.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r675_nr_5F675 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1744 (s : N.State) (i : N.Inputs) :
  R.v1744 (state s) (inputs i) = Zmod.unsigned (N.v1744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1744 s i)) at 1.
  unfold R.v1744, N.v1744.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1745 (s : N.State) (i : N.Inputs) :
  R.v1745 (state s) (inputs i) = Zmod.unsigned (N.v1745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1745 s i)) at 1.
  unfold R.v1745, N.v1745.
  rewrite ?node_1744.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r676_nr_5F676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r676_nr_5F676 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1746 (s : N.State) (i : N.Inputs) :
  R.v1746 (state s) (inputs i) = Zmod.unsigned (N.v1746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1746 s i)) at 1.
  unfold R.v1746, N.v1746.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1747 (s : N.State) (i : N.Inputs) :
  R.v1747 (state s) (inputs i) = Zmod.unsigned (N.v1747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1747 s i)) at 1.
  unfold R.v1747, N.v1747.
  rewrite ?node_1746.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r677_nr_5F677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r677_nr_5F677 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1748 (s : N.State) (i : N.Inputs) :
  R.v1748 (state s) (inputs i) = Zmod.unsigned (N.v1748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1748 s i)) at 1.
  unfold R.v1748, N.v1748.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1749 (s : N.State) (i : N.Inputs) :
  R.v1749 (state s) (inputs i) = Zmod.unsigned (N.v1749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1749 s i)) at 1.
  unfold R.v1749, N.v1749.
  rewrite ?node_1748.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r678_nr_5F678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r678_nr_5F678 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1750 (s : N.State) (i : N.Inputs) :
  R.v1750 (state s) (inputs i) = Zmod.unsigned (N.v1750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1750 s i)) at 1.
  unfold R.v1750, N.v1750.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1751 (s : N.State) (i : N.Inputs) :
  R.v1751 (state s) (inputs i) = Zmod.unsigned (N.v1751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1751 s i)) at 1.
  unfold R.v1751, N.v1751.
  rewrite ?node_1750.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r679_nr_5F679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r679_nr_5F679 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1752 (s : N.State) (i : N.Inputs) :
  R.v1752 (state s) (inputs i) = Zmod.unsigned (N.v1752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1752 s i)) at 1.
  unfold R.v1752, N.v1752.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1753 (s : N.State) (i : N.Inputs) :
  R.v1753 (state s) (inputs i) = Zmod.unsigned (N.v1753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1753 s i)) at 1.
  unfold R.v1753, N.v1753.
  rewrite ?node_1752.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r680_nr_5F680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r680_nr_5F680 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1754 (s : N.State) (i : N.Inputs) :
  R.v1754 (state s) (inputs i) = Zmod.unsigned (N.v1754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1754 s i)) at 1.
  unfold R.v1754, N.v1754.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1755 (s : N.State) (i : N.Inputs) :
  R.v1755 (state s) (inputs i) = Zmod.unsigned (N.v1755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1755 s i)) at 1.
  unfold R.v1755, N.v1755.
  rewrite ?node_1754.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r681_nr_5F681.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r681_nr_5F681 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1756 (s : N.State) (i : N.Inputs) :
  R.v1756 (state s) (inputs i) = Zmod.unsigned (N.v1756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1756 s i)) at 1.
  unfold R.v1756, N.v1756.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1757 (s : N.State) (i : N.Inputs) :
  R.v1757 (state s) (inputs i) = Zmod.unsigned (N.v1757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1757 s i)) at 1.
  unfold R.v1757, N.v1757.
  rewrite ?node_1756.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r682_nr_5F682.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r682_nr_5F682 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1758 (s : N.State) (i : N.Inputs) :
  R.v1758 (state s) (inputs i) = Zmod.unsigned (N.v1758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1758 s i)) at 1.
  unfold R.v1758, N.v1758.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1759 (s : N.State) (i : N.Inputs) :
  R.v1759 (state s) (inputs i) = Zmod.unsigned (N.v1759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1759 s i)) at 1.
  unfold R.v1759, N.v1759.
  rewrite ?node_1758.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r683_nr_5F683.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r683_nr_5F683 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1760 (s : N.State) (i : N.Inputs) :
  R.v1760 (state s) (inputs i) = Zmod.unsigned (N.v1760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1760 s i)) at 1.
  unfold R.v1760, N.v1760.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1761 (s : N.State) (i : N.Inputs) :
  R.v1761 (state s) (inputs i) = Zmod.unsigned (N.v1761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1761 s i)) at 1.
  unfold R.v1761, N.v1761.
  rewrite ?node_1760.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r684_nr_5F684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r684_nr_5F684 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1762 (s : N.State) (i : N.Inputs) :
  R.v1762 (state s) (inputs i) = Zmod.unsigned (N.v1762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1762 s i)) at 1.
  unfold R.v1762, N.v1762.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1763 (s : N.State) (i : N.Inputs) :
  R.v1763 (state s) (inputs i) = Zmod.unsigned (N.v1763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1763 s i)) at 1.
  unfold R.v1763, N.v1763.
  rewrite ?node_1762.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r685_nr_5F685.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r685_nr_5F685 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1764 (s : N.State) (i : N.Inputs) :
  R.v1764 (state s) (inputs i) = Zmod.unsigned (N.v1764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1764 s i)) at 1.
  unfold R.v1764, N.v1764.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1765 (s : N.State) (i : N.Inputs) :
  R.v1765 (state s) (inputs i) = Zmod.unsigned (N.v1765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1765 s i)) at 1.
  unfold R.v1765, N.v1765.
  rewrite ?node_1764.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r686_nr_5F686.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r686_nr_5F686 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1766 (s : N.State) (i : N.Inputs) :
  R.v1766 (state s) (inputs i) = Zmod.unsigned (N.v1766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1766 s i)) at 1.
  unfold R.v1766, N.v1766.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1767 (s : N.State) (i : N.Inputs) :
  R.v1767 (state s) (inputs i) = Zmod.unsigned (N.v1767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1767 s i)) at 1.
  unfold R.v1767, N.v1767.
  rewrite ?node_1766.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r687_nr_5F687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r687_nr_5F687 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1768 (s : N.State) (i : N.Inputs) :
  R.v1768 (state s) (inputs i) = Zmod.unsigned (N.v1768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1768 s i)) at 1.
  unfold R.v1768, N.v1768.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1769 (s : N.State) (i : N.Inputs) :
  R.v1769 (state s) (inputs i) = Zmod.unsigned (N.v1769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1769 s i)) at 1.
  unfold R.v1769, N.v1769.
  rewrite ?node_1768.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r688_nr_5F688.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r688_nr_5F688 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1770 (s : N.State) (i : N.Inputs) :
  R.v1770 (state s) (inputs i) = Zmod.unsigned (N.v1770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1770 s i)) at 1.
  unfold R.v1770, N.v1770.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1771 (s : N.State) (i : N.Inputs) :
  R.v1771 (state s) (inputs i) = Zmod.unsigned (N.v1771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1771 s i)) at 1.
  unfold R.v1771, N.v1771.
  rewrite ?node_1770.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r689_nr_5F689.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r689_nr_5F689 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1772 (s : N.State) (i : N.Inputs) :
  R.v1772 (state s) (inputs i) = Zmod.unsigned (N.v1772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1772 s i)) at 1.
  unfold R.v1772, N.v1772.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1773 (s : N.State) (i : N.Inputs) :
  R.v1773 (state s) (inputs i) = Zmod.unsigned (N.v1773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1773 s i)) at 1.
  unfold R.v1773, N.v1773.
  rewrite ?node_1772.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r690_nr_5F690.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r690_nr_5F690 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1774 (s : N.State) (i : N.Inputs) :
  R.v1774 (state s) (inputs i) = Zmod.unsigned (N.v1774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1774 s i)) at 1.
  unfold R.v1774, N.v1774.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1775 (s : N.State) (i : N.Inputs) :
  R.v1775 (state s) (inputs i) = Zmod.unsigned (N.v1775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1775 s i)) at 1.
  unfold R.v1775, N.v1775.
  rewrite ?node_1774.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r691_nr_5F691.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r691_nr_5F691 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1776 (s : N.State) (i : N.Inputs) :
  R.v1776 (state s) (inputs i) = Zmod.unsigned (N.v1776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1776 s i)) at 1.
  unfold R.v1776, N.v1776.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1777 (s : N.State) (i : N.Inputs) :
  R.v1777 (state s) (inputs i) = Zmod.unsigned (N.v1777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1777 s i)) at 1.
  unfold R.v1777, N.v1777.
  rewrite ?node_1776.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r692_nr_5F692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r692_nr_5F692 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1778 (s : N.State) (i : N.Inputs) :
  R.v1778 (state s) (inputs i) = Zmod.unsigned (N.v1778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1778 s i)) at 1.
  unfold R.v1778, N.v1778.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1779 (s : N.State) (i : N.Inputs) :
  R.v1779 (state s) (inputs i) = Zmod.unsigned (N.v1779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1779 s i)) at 1.
  unfold R.v1779, N.v1779.
  rewrite ?node_1778.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r693_nr_5F693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r693_nr_5F693 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1780 (s : N.State) (i : N.Inputs) :
  R.v1780 (state s) (inputs i) = Zmod.unsigned (N.v1780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1780 s i)) at 1.
  unfold R.v1780, N.v1780.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1781 (s : N.State) (i : N.Inputs) :
  R.v1781 (state s) (inputs i) = Zmod.unsigned (N.v1781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1781 s i)) at 1.
  unfold R.v1781, N.v1781.
  rewrite ?node_1780.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r694_nr_5F694.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r694_nr_5F694 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1782 (s : N.State) (i : N.Inputs) :
  R.v1782 (state s) (inputs i) = Zmod.unsigned (N.v1782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1782 s i)) at 1.
  unfold R.v1782, N.v1782.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1783 (s : N.State) (i : N.Inputs) :
  R.v1783 (state s) (inputs i) = Zmod.unsigned (N.v1783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1783 s i)) at 1.
  unfold R.v1783, N.v1783.
  rewrite ?node_1782.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r695_nr_5F695.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r695_nr_5F695 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1784 (s : N.State) (i : N.Inputs) :
  R.v1784 (state s) (inputs i) = Zmod.unsigned (N.v1784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1784 s i)) at 1.
  unfold R.v1784, N.v1784.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1785 (s : N.State) (i : N.Inputs) :
  R.v1785 (state s) (inputs i) = Zmod.unsigned (N.v1785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1785 s i)) at 1.
  unfold R.v1785, N.v1785.
  rewrite ?node_1784.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r696_nr_5F696.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r696_nr_5F696 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1786 (s : N.State) (i : N.Inputs) :
  R.v1786 (state s) (inputs i) = Zmod.unsigned (N.v1786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1786 s i)) at 1.
  unfold R.v1786, N.v1786.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1787 (s : N.State) (i : N.Inputs) :
  R.v1787 (state s) (inputs i) = Zmod.unsigned (N.v1787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1787 s i)) at 1.
  unfold R.v1787, N.v1787.
  rewrite ?node_1786.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r697_nr_5F697.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r697_nr_5F697 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1788 (s : N.State) (i : N.Inputs) :
  R.v1788 (state s) (inputs i) = Zmod.unsigned (N.v1788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1788 s i)) at 1.
  unfold R.v1788, N.v1788.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1789 (s : N.State) (i : N.Inputs) :
  R.v1789 (state s) (inputs i) = Zmod.unsigned (N.v1789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1789 s i)) at 1.
  unfold R.v1789, N.v1789.
  rewrite ?node_1788.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r698_nr_5F698.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r698_nr_5F698 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1790 (s : N.State) (i : N.Inputs) :
  R.v1790 (state s) (inputs i) = Zmod.unsigned (N.v1790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1790 s i)) at 1.
  unfold R.v1790, N.v1790.
  rewrite ?node_1737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1791 (s : N.State) (i : N.Inputs) :
  R.v1791 (state s) (inputs i) = Zmod.unsigned (N.v1791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1791 s i)) at 1.
  unfold R.v1791, N.v1791.
  rewrite ?node_1790.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r699_nr_5F699.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r699_nr_5F699 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1792 (s : N.State) (i : N.Inputs) :
  R.v1792 (state s) (inputs i) = Zmod.unsigned (N.v1792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1792 s i)) at 1.
  unfold R.v1792, N.v1792.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1793 (s : N.State) (i : N.Inputs) :
  R.v1793 (state s) (inputs i) = Zmod.unsigned (N.v1793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1793 s i)) at 1.
  unfold R.v1793, N.v1793.
  rewrite ?node_1792.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r700_nr_5F700.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r700_nr_5F700 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1794 (s : N.State) (i : N.Inputs) :
  R.v1794 (state s) (inputs i) = Zmod.unsigned (N.v1794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1794 s i)) at 1.
  unfold R.v1794, N.v1794.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1795 (s : N.State) (i : N.Inputs) :
  R.v1795 (state s) (inputs i) = Zmod.unsigned (N.v1795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1795 s i)) at 1.
  unfold R.v1795, N.v1795.
  rewrite ?node_1794.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r701_nr_5F701.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r701_nr_5F701 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1796 (s : N.State) (i : N.Inputs) :
  R.v1796 (state s) (inputs i) = Zmod.unsigned (N.v1796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1796 s i)) at 1.
  unfold R.v1796, N.v1796.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1797 (s : N.State) (i : N.Inputs) :
  R.v1797 (state s) (inputs i) = Zmod.unsigned (N.v1797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1797 s i)) at 1.
  unfold R.v1797, N.v1797.
  rewrite ?node_1796.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r702_nr_5F702.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r702_nr_5F702 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1798 (s : N.State) (i : N.Inputs) :
  R.v1798 (state s) (inputs i) = Zmod.unsigned (N.v1798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1798 s i)) at 1.
  unfold R.v1798, N.v1798.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1799 (s : N.State) (i : N.Inputs) :
  R.v1799 (state s) (inputs i) = Zmod.unsigned (N.v1799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1799 s i)) at 1.
  unfold R.v1799, N.v1799.
  rewrite ?node_1798.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r703_nr_5F703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r703_nr_5F703 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1800 (s : N.State) (i : N.Inputs) :
  R.v1800 (state s) (inputs i) = Zmod.unsigned (N.v1800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1800 s i)) at 1.
  unfold R.v1800, N.v1800.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1801 (s : N.State) (i : N.Inputs) :
  R.v1801 (state s) (inputs i) = Zmod.unsigned (N.v1801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1801 s i)) at 1.
  unfold R.v1801, N.v1801.
  rewrite ?node_1800.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r704_nr_5F704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r704_nr_5F704 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1802 (s : N.State) (i : N.Inputs) :
  R.v1802 (state s) (inputs i) = Zmod.unsigned (N.v1802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1802 s i)) at 1.
  unfold R.v1802, N.v1802.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1803 (s : N.State) (i : N.Inputs) :
  R.v1803 (state s) (inputs i) = Zmod.unsigned (N.v1803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1803 s i)) at 1.
  unfold R.v1803, N.v1803.
  rewrite ?node_1802.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r705_nr_5F705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r705_nr_5F705 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1804 (s : N.State) (i : N.Inputs) :
  R.v1804 (state s) (inputs i) = Zmod.unsigned (N.v1804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1804 s i)) at 1.
  unfold R.v1804, N.v1804.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1805 (s : N.State) (i : N.Inputs) :
  R.v1805 (state s) (inputs i) = Zmod.unsigned (N.v1805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1805 s i)) at 1.
  unfold R.v1805, N.v1805.
  rewrite ?node_1804.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r706_nr_5F706.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r706_nr_5F706 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1806 (s : N.State) (i : N.Inputs) :
  R.v1806 (state s) (inputs i) = Zmod.unsigned (N.v1806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1806 s i)) at 1.
  unfold R.v1806, N.v1806.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1807 (s : N.State) (i : N.Inputs) :
  R.v1807 (state s) (inputs i) = Zmod.unsigned (N.v1807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1807 s i)) at 1.
  unfold R.v1807, N.v1807.
  rewrite ?node_1806.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r707_nr_5F707.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r707_nr_5F707 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1808 (s : N.State) (i : N.Inputs) :
  R.v1808 (state s) (inputs i) = Zmod.unsigned (N.v1808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1808 s i)) at 1.
  unfold R.v1808, N.v1808.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1809 (s : N.State) (i : N.Inputs) :
  R.v1809 (state s) (inputs i) = Zmod.unsigned (N.v1809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1809 s i)) at 1.
  unfold R.v1809, N.v1809.
  rewrite ?node_1808.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r708_nr_5F708.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r708_nr_5F708 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1810 (s : N.State) (i : N.Inputs) :
  R.v1810 (state s) (inputs i) = Zmod.unsigned (N.v1810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1810 s i)) at 1.
  unfold R.v1810, N.v1810.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1811 (s : N.State) (i : N.Inputs) :
  R.v1811 (state s) (inputs i) = Zmod.unsigned (N.v1811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1811 s i)) at 1.
  unfold R.v1811, N.v1811.
  rewrite ?node_1810.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r709_nr_5F709.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r709_nr_5F709 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1812 (s : N.State) (i : N.Inputs) :
  R.v1812 (state s) (inputs i) = Zmod.unsigned (N.v1812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1812 s i)) at 1.
  unfold R.v1812, N.v1812.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1813 (s : N.State) (i : N.Inputs) :
  R.v1813 (state s) (inputs i) = Zmod.unsigned (N.v1813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1813 s i)) at 1.
  unfold R.v1813, N.v1813.
  rewrite ?node_1812.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r710_nr_5F710.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r710_nr_5F710 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1814 (s : N.State) (i : N.Inputs) :
  R.v1814 (state s) (inputs i) = Zmod.unsigned (N.v1814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1814 s i)) at 1.
  unfold R.v1814, N.v1814.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1815 (s : N.State) (i : N.Inputs) :
  R.v1815 (state s) (inputs i) = Zmod.unsigned (N.v1815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1815 s i)) at 1.
  unfold R.v1815, N.v1815.
  rewrite ?node_1814.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r711_nr_5F711.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r711_nr_5F711 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1816 (s : N.State) (i : N.Inputs) :
  R.v1816 (state s) (inputs i) = Zmod.unsigned (N.v1816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1816 s i)) at 1.
  unfold R.v1816, N.v1816.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1817 (s : N.State) (i : N.Inputs) :
  R.v1817 (state s) (inputs i) = Zmod.unsigned (N.v1817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1817 s i)) at 1.
  unfold R.v1817, N.v1817.
  rewrite ?node_1816.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r712_nr_5F712.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r712_nr_5F712 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1818 (s : N.State) (i : N.Inputs) :
  R.v1818 (state s) (inputs i) = Zmod.unsigned (N.v1818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1818 s i)) at 1.
  unfold R.v1818, N.v1818.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1819 (s : N.State) (i : N.Inputs) :
  R.v1819 (state s) (inputs i) = Zmod.unsigned (N.v1819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1819 s i)) at 1.
  unfold R.v1819, N.v1819.
  rewrite ?node_1818.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r713_nr_5F713.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r713_nr_5F713 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1820 (s : N.State) (i : N.Inputs) :
  R.v1820 (state s) (inputs i) = Zmod.unsigned (N.v1820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1820 s i)) at 1.
  unfold R.v1820, N.v1820.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1821 (s : N.State) (i : N.Inputs) :
  R.v1821 (state s) (inputs i) = Zmod.unsigned (N.v1821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1821 s i)) at 1.
  unfold R.v1821, N.v1821.
  rewrite ?node_1820.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r714_nr_5F714.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r714_nr_5F714 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1822 (s : N.State) (i : N.Inputs) :
  R.v1822 (state s) (inputs i) = Zmod.unsigned (N.v1822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1822 s i)) at 1.
  unfold R.v1822, N.v1822.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1823 (s : N.State) (i : N.Inputs) :
  R.v1823 (state s) (inputs i) = Zmod.unsigned (N.v1823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1823 s i)) at 1.
  unfold R.v1823, N.v1823.
  rewrite ?node_1822.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r715_nr_5F715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r715_nr_5F715 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1824 (s : N.State) (i : N.Inputs) :
  R.v1824 (state s) (inputs i) = Zmod.unsigned (N.v1824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1824 s i)) at 1.
  unfold R.v1824, N.v1824.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1825 (s : N.State) (i : N.Inputs) :
  R.v1825 (state s) (inputs i) = Zmod.unsigned (N.v1825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1825 s i)) at 1.
  unfold R.v1825, N.v1825.
  rewrite ?node_1824.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r716_nr_5F716.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r716_nr_5F716 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1826 (s : N.State) (i : N.Inputs) :
  R.v1826 (state s) (inputs i) = Zmod.unsigned (N.v1826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1826 s i)) at 1.
  unfold R.v1826, N.v1826.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1827 (s : N.State) (i : N.Inputs) :
  R.v1827 (state s) (inputs i) = Zmod.unsigned (N.v1827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1827 s i)) at 1.
  unfold R.v1827, N.v1827.
  rewrite ?node_1826.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r717_nr_5F717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r717_nr_5F717 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1828 (s : N.State) (i : N.Inputs) :
  R.v1828 (state s) (inputs i) = Zmod.unsigned (N.v1828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1828 s i)) at 1.
  unfold R.v1828, N.v1828.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1829 (s : N.State) (i : N.Inputs) :
  R.v1829 (state s) (inputs i) = Zmod.unsigned (N.v1829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1829 s i)) at 1.
  unfold R.v1829, N.v1829.
  rewrite ?node_1828.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r718_nr_5F718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r718_nr_5F718 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1830 (s : N.State) (i : N.Inputs) :
  R.v1830 (state s) (inputs i) = Zmod.unsigned (N.v1830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1830 s i)) at 1.
  unfold R.v1830, N.v1830.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1831 (s : N.State) (i : N.Inputs) :
  R.v1831 (state s) (inputs i) = Zmod.unsigned (N.v1831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1831 s i)) at 1.
  unfold R.v1831, N.v1831.
  rewrite ?node_1830.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r719_nr_5F719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r719_nr_5F719 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1832 (s : N.State) (i : N.Inputs) :
  R.v1832 (state s) (inputs i) = Zmod.unsigned (N.v1832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1832 s i)) at 1.
  unfold R.v1832, N.v1832.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1833 (s : N.State) (i : N.Inputs) :
  R.v1833 (state s) (inputs i) = Zmod.unsigned (N.v1833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1833 s i)) at 1.
  unfold R.v1833, N.v1833.
  rewrite ?node_1832.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r720_nr_5F720.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r720_nr_5F720 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1834 (s : N.State) (i : N.Inputs) :
  R.v1834 (state s) (inputs i) = Zmod.unsigned (N.v1834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1834 s i)) at 1.
  unfold R.v1834, N.v1834.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1835 (s : N.State) (i : N.Inputs) :
  R.v1835 (state s) (inputs i) = Zmod.unsigned (N.v1835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1835 s i)) at 1.
  unfold R.v1835, N.v1835.
  rewrite ?node_1834.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r721_nr_5F721.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r721_nr_5F721 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1836 (s : N.State) (i : N.Inputs) :
  R.v1836 (state s) (inputs i) = Zmod.unsigned (N.v1836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1836 s i)) at 1.
  unfold R.v1836, N.v1836.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1837 (s : N.State) (i : N.Inputs) :
  R.v1837 (state s) (inputs i) = Zmod.unsigned (N.v1837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1837 s i)) at 1.
  unfold R.v1837, N.v1837.
  rewrite ?node_1836.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r722_nr_5F722.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r722_nr_5F722 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1838 (s : N.State) (i : N.Inputs) :
  R.v1838 (state s) (inputs i) = Zmod.unsigned (N.v1838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1838 s i)) at 1.
  unfold R.v1838, N.v1838.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1839 (s : N.State) (i : N.Inputs) :
  R.v1839 (state s) (inputs i) = Zmod.unsigned (N.v1839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1839 s i)) at 1.
  unfold R.v1839, N.v1839.
  rewrite ?node_1838.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r723_nr_5F723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r723_nr_5F723 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1840 (s : N.State) (i : N.Inputs) :
  R.v1840 (state s) (inputs i) = Zmod.unsigned (N.v1840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1840 s i)) at 1.
  unfold R.v1840, N.v1840.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1841 (s : N.State) (i : N.Inputs) :
  R.v1841 (state s) (inputs i) = Zmod.unsigned (N.v1841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1841 s i)) at 1.
  unfold R.v1841, N.v1841.
  rewrite ?node_1840.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r724_nr_5F724.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r724_nr_5F724 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1842 (s : N.State) (i : N.Inputs) :
  R.v1842 (state s) (inputs i) = Zmod.unsigned (N.v1842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1842 s i)) at 1.
  unfold R.v1842, N.v1842.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1843 (s : N.State) (i : N.Inputs) :
  R.v1843 (state s) (inputs i) = Zmod.unsigned (N.v1843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1843 s i)) at 1.
  unfold R.v1843, N.v1843.
  unfold R.v33, N.v33.
  rewrite ?node_1842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1844 (s : N.State) (i : N.Inputs) :
  R.v1844 (state s) (inputs i) = Zmod.unsigned (N.v1844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1844 s i)) at 1.
  unfold R.v1844, N.v1844.
  unfold R.v35, N.v35.
  rewrite ?node_1842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1845 (s : N.State) (i : N.Inputs) :
  R.v1845 (state s) (inputs i) = Zmod.unsigned (N.v1845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1845 s i)) at 1.
  unfold R.v1845, N.v1845.
  rewrite ?node_1843.
  rewrite ?node_1844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1846 (s : N.State) (i : N.Inputs) :
  R.v1846 (state s) (inputs i) = Zmod.unsigned (N.v1846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1846 s i)) at 1.
  unfold R.v1846, N.v1846.
  unfold R.v39, N.v39.
  rewrite ?node_1842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1847 (s : N.State) (i : N.Inputs) :
  R.v1847 (state s) (inputs i) = Zmod.unsigned (N.v1847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1847 s i)) at 1.
  unfold R.v1847, N.v1847.
  unfold R.v42, N.v42.
  rewrite ?node_1842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1848 (s : N.State) (i : N.Inputs) :
  R.v1848 (state s) (inputs i) = Zmod.unsigned (N.v1848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1848 s i)) at 1.
  unfold R.v1848, N.v1848.
  unfold R.v45, N.v45.
  rewrite ?node_1842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1849 (s : N.State) (i : N.Inputs) :
  R.v1849 (state s) (inputs i) = Zmod.unsigned (N.v1849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1849 s i)) at 1.
  unfold R.v1849, N.v1849.
  unfold R.v47, N.v47.
  rewrite ?node_1842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1850 (s : N.State) (i : N.Inputs) :
  R.v1850 (state s) (inputs i) = Zmod.unsigned (N.v1850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1850 s i)) at 1.
  unfold R.v1850, N.v1850.
  rewrite ?node_1848.
  rewrite ?node_1849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1851 (s : N.State) (i : N.Inputs) :
  R.v1851 (state s) (inputs i) = Zmod.unsigned (N.v1851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1851 s i)) at 1.
  unfold R.v1851, N.v1851.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_1850.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1852 (s : N.State) (i : N.Inputs) :
  R.v1852 (state s) (inputs i) = Zmod.unsigned (N.v1852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1852 s i)) at 1.
  unfold R.v1852, N.v1852.
  rewrite ?node_44.
  rewrite ?node_1847.
  rewrite ?node_1851.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1853 (s : N.State) (i : N.Inputs) :
  R.v1853 (state s) (inputs i) = Zmod.unsigned (N.v1853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1853 s i)) at 1.
  unfold R.v1853, N.v1853.
  rewrite ?node_41.
  rewrite ?node_1846.
  rewrite ?node_1852.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1854 (s : N.State) (i : N.Inputs) :
  R.v1854 (state s) (inputs i) = Zmod.unsigned (N.v1854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1854 s i)) at 1.
  unfold R.v1854, N.v1854.
  rewrite ?node_38.
  rewrite ?node_1845.
  rewrite ?node_1853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1855 (s : N.State) (i : N.Inputs) :
  R.v1855 (state s) (inputs i) = Zmod.unsigned (N.v1855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1855 s i)) at 1.
  unfold R.v1855, N.v1855.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1856 (s : N.State) (i : N.Inputs) :
  R.v1856 (state s) (inputs i) = Zmod.unsigned (N.v1856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1856 s i)) at 1.
  unfold R.v1856, N.v1856.
  rewrite ?node_1855.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r725_nr_5F725.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r725_nr_5F725 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1857 (s : N.State) (i : N.Inputs) :
  R.v1857 (state s) (inputs i) = Zmod.unsigned (N.v1857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1857 s i)) at 1.
  unfold R.v1857, N.v1857.
  unfold R.v6, N.v6.
  rewrite ?node_1846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1858 (s : N.State) (i : N.Inputs) :
  R.v1858 (state s) (inputs i) = Zmod.unsigned (N.v1858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1858 s i)) at 1.
  unfold R.v1858, N.v1858.
  unfold R.v19, N.v19.
  rewrite ?node_1845.
  rewrite ?node_1857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1859 (s : N.State) (i : N.Inputs) :
  R.v1859 (state s) (inputs i) = Zmod.unsigned (N.v1859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1859 s i)) at 1.
  unfold R.v1859, N.v1859.
  rewrite ?node_1858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1860 (s : N.State) (i : N.Inputs) :
  R.v1860 (state s) (inputs i) = Zmod.unsigned (N.v1860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1860 s i)) at 1.
  unfold R.v1860, N.v1860.
  rewrite ?node_1859.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r726_nr_5F726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r726_nr_5F726 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1861 (s : N.State) (i : N.Inputs) :
  R.v1861 (state s) (inputs i) = Zmod.unsigned (N.v1861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1861 s i)) at 1.
  unfold R.v1861, N.v1861.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1862 (s : N.State) (i : N.Inputs) :
  R.v1862 (state s) (inputs i) = Zmod.unsigned (N.v1862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1862 s i)) at 1.
  unfold R.v1862, N.v1862.
  rewrite ?node_1861.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r727_nr_5F727.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r727_nr_5F727 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1863 (s : N.State) (i : N.Inputs) :
  R.v1863 (state s) (inputs i) = Zmod.unsigned (N.v1863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1863 s i)) at 1.
  unfold R.v1863, N.v1863.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1864 (s : N.State) (i : N.Inputs) :
  R.v1864 (state s) (inputs i) = Zmod.unsigned (N.v1864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1864 s i)) at 1.
  unfold R.v1864, N.v1864.
  rewrite ?node_1863.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r728_nr_5F728.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r728_nr_5F728 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1865 (s : N.State) (i : N.Inputs) :
  R.v1865 (state s) (inputs i) = Zmod.unsigned (N.v1865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1865 s i)) at 1.
  unfold R.v1865, N.v1865.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1866 (s : N.State) (i : N.Inputs) :
  R.v1866 (state s) (inputs i) = Zmod.unsigned (N.v1866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1866 s i)) at 1.
  unfold R.v1866, N.v1866.
  rewrite ?node_1865.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r729_nr_5F729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r729_nr_5F729 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1867 (s : N.State) (i : N.Inputs) :
  R.v1867 (state s) (inputs i) = Zmod.unsigned (N.v1867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1867 s i)) at 1.
  unfold R.v1867, N.v1867.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1868 (s : N.State) (i : N.Inputs) :
  R.v1868 (state s) (inputs i) = Zmod.unsigned (N.v1868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1868 s i)) at 1.
  unfold R.v1868, N.v1868.
  rewrite ?node_1867.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r730_nr_5F730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r730_nr_5F730 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1869 (s : N.State) (i : N.Inputs) :
  R.v1869 (state s) (inputs i) = Zmod.unsigned (N.v1869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1869 s i)) at 1.
  unfold R.v1869, N.v1869.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1870 (s : N.State) (i : N.Inputs) :
  R.v1870 (state s) (inputs i) = Zmod.unsigned (N.v1870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1870 s i)) at 1.
  unfold R.v1870, N.v1870.
  rewrite ?node_1869.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r731_nr_5F731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r731_nr_5F731 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1871 (s : N.State) (i : N.Inputs) :
  R.v1871 (state s) (inputs i) = Zmod.unsigned (N.v1871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1871 s i)) at 1.
  unfold R.v1871, N.v1871.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1872 (s : N.State) (i : N.Inputs) :
  R.v1872 (state s) (inputs i) = Zmod.unsigned (N.v1872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1872 s i)) at 1.
  unfold R.v1872, N.v1872.
  rewrite ?node_1871.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r732_nr_5F732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r732_nr_5F732 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1873 (s : N.State) (i : N.Inputs) :
  R.v1873 (state s) (inputs i) = Zmod.unsigned (N.v1873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1873 s i)) at 1.
  unfold R.v1873, N.v1873.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1874 (s : N.State) (i : N.Inputs) :
  R.v1874 (state s) (inputs i) = Zmod.unsigned (N.v1874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1874 s i)) at 1.
  unfold R.v1874, N.v1874.
  rewrite ?node_1873.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r733_nr_5F733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r733_nr_5F733 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1875 (s : N.State) (i : N.Inputs) :
  R.v1875 (state s) (inputs i) = Zmod.unsigned (N.v1875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1875 s i)) at 1.
  unfold R.v1875, N.v1875.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1876 (s : N.State) (i : N.Inputs) :
  R.v1876 (state s) (inputs i) = Zmod.unsigned (N.v1876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1876 s i)) at 1.
  unfold R.v1876, N.v1876.
  rewrite ?node_1875.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r734_nr_5F734.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r734_nr_5F734 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1877 (s : N.State) (i : N.Inputs) :
  R.v1877 (state s) (inputs i) = Zmod.unsigned (N.v1877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1877 s i)) at 1.
  unfold R.v1877, N.v1877.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1878 (s : N.State) (i : N.Inputs) :
  R.v1878 (state s) (inputs i) = Zmod.unsigned (N.v1878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1878 s i)) at 1.
  unfold R.v1878, N.v1878.
  rewrite ?node_1877.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r735_nr_5F735.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r735_nr_5F735 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1879 (s : N.State) (i : N.Inputs) :
  R.v1879 (state s) (inputs i) = Zmod.unsigned (N.v1879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1879 s i)) at 1.
  unfold R.v1879, N.v1879.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1880 (s : N.State) (i : N.Inputs) :
  R.v1880 (state s) (inputs i) = Zmod.unsigned (N.v1880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1880 s i)) at 1.
  unfold R.v1880, N.v1880.
  rewrite ?node_1879.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r736_nr_5F736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r736_nr_5F736 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1881 (s : N.State) (i : N.Inputs) :
  R.v1881 (state s) (inputs i) = Zmod.unsigned (N.v1881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1881 s i)) at 1.
  unfold R.v1881, N.v1881.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1882 (s : N.State) (i : N.Inputs) :
  R.v1882 (state s) (inputs i) = Zmod.unsigned (N.v1882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1882 s i)) at 1.
  unfold R.v1882, N.v1882.
  rewrite ?node_1881.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r737_nr_5F737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r737_nr_5F737 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1883 (s : N.State) (i : N.Inputs) :
  R.v1883 (state s) (inputs i) = Zmod.unsigned (N.v1883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1883 s i)) at 1.
  unfold R.v1883, N.v1883.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1884 (s : N.State) (i : N.Inputs) :
  R.v1884 (state s) (inputs i) = Zmod.unsigned (N.v1884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1884 s i)) at 1.
  unfold R.v1884, N.v1884.
  rewrite ?node_1883.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r738_nr_5F738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r738_nr_5F738 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1885 (s : N.State) (i : N.Inputs) :
  R.v1885 (state s) (inputs i) = Zmod.unsigned (N.v1885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1885 s i)) at 1.
  unfold R.v1885, N.v1885.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1886 (s : N.State) (i : N.Inputs) :
  R.v1886 (state s) (inputs i) = Zmod.unsigned (N.v1886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1886 s i)) at 1.
  unfold R.v1886, N.v1886.
  rewrite ?node_1885.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r739_nr_5F739.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r739_nr_5F739 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1887 (s : N.State) (i : N.Inputs) :
  R.v1887 (state s) (inputs i) = Zmod.unsigned (N.v1887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1887 s i)) at 1.
  unfold R.v1887, N.v1887.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1888 (s : N.State) (i : N.Inputs) :
  R.v1888 (state s) (inputs i) = Zmod.unsigned (N.v1888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1888 s i)) at 1.
  unfold R.v1888, N.v1888.
  rewrite ?node_1887.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r740_nr_5F740.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r740_nr_5F740 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1889 (s : N.State) (i : N.Inputs) :
  R.v1889 (state s) (inputs i) = Zmod.unsigned (N.v1889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1889 s i)) at 1.
  unfold R.v1889, N.v1889.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1890 (s : N.State) (i : N.Inputs) :
  R.v1890 (state s) (inputs i) = Zmod.unsigned (N.v1890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1890 s i)) at 1.
  unfold R.v1890, N.v1890.
  rewrite ?node_1889.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r741_nr_5F741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r741_nr_5F741 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1891 (s : N.State) (i : N.Inputs) :
  R.v1891 (state s) (inputs i) = Zmod.unsigned (N.v1891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1891 s i)) at 1.
  unfold R.v1891, N.v1891.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1892 (s : N.State) (i : N.Inputs) :
  R.v1892 (state s) (inputs i) = Zmod.unsigned (N.v1892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1892 s i)) at 1.
  unfold R.v1892, N.v1892.
  rewrite ?node_1891.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r742_nr_5F742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r742_nr_5F742 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1893 (s : N.State) (i : N.Inputs) :
  R.v1893 (state s) (inputs i) = Zmod.unsigned (N.v1893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1893 s i)) at 1.
  unfold R.v1893, N.v1893.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1894 (s : N.State) (i : N.Inputs) :
  R.v1894 (state s) (inputs i) = Zmod.unsigned (N.v1894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1894 s i)) at 1.
  unfold R.v1894, N.v1894.
  rewrite ?node_1893.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r743_nr_5F743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r743_nr_5F743 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1895 (s : N.State) (i : N.Inputs) :
  R.v1895 (state s) (inputs i) = Zmod.unsigned (N.v1895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1895 s i)) at 1.
  unfold R.v1895, N.v1895.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1896 (s : N.State) (i : N.Inputs) :
  R.v1896 (state s) (inputs i) = Zmod.unsigned (N.v1896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1896 s i)) at 1.
  unfold R.v1896, N.v1896.
  rewrite ?node_1895.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r744_nr_5F744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r744_nr_5F744 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1897 (s : N.State) (i : N.Inputs) :
  R.v1897 (state s) (inputs i) = Zmod.unsigned (N.v1897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1897 s i)) at 1.
  unfold R.v1897, N.v1897.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1898 (s : N.State) (i : N.Inputs) :
  R.v1898 (state s) (inputs i) = Zmod.unsigned (N.v1898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1898 s i)) at 1.
  unfold R.v1898, N.v1898.
  rewrite ?node_1897.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r745_nr_5F745.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r745_nr_5F745 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1899 (s : N.State) (i : N.Inputs) :
  R.v1899 (state s) (inputs i) = Zmod.unsigned (N.v1899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1899 s i)) at 1.
  unfold R.v1899, N.v1899.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1900 (s : N.State) (i : N.Inputs) :
  R.v1900 (state s) (inputs i) = Zmod.unsigned (N.v1900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1900 s i)) at 1.
  unfold R.v1900, N.v1900.
  rewrite ?node_1899.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r746_nr_5F746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r746_nr_5F746 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1901 (s : N.State) (i : N.Inputs) :
  R.v1901 (state s) (inputs i) = Zmod.unsigned (N.v1901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1901 s i)) at 1.
  unfold R.v1901, N.v1901.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1902 (s : N.State) (i : N.Inputs) :
  R.v1902 (state s) (inputs i) = Zmod.unsigned (N.v1902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1902 s i)) at 1.
  unfold R.v1902, N.v1902.
  rewrite ?node_1901.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r747_nr_5F747.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r747_nr_5F747 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1903 (s : N.State) (i : N.Inputs) :
  R.v1903 (state s) (inputs i) = Zmod.unsigned (N.v1903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1903 s i)) at 1.
  unfold R.v1903, N.v1903.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1904 (s : N.State) (i : N.Inputs) :
  R.v1904 (state s) (inputs i) = Zmod.unsigned (N.v1904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1904 s i)) at 1.
  unfold R.v1904, N.v1904.
  rewrite ?node_1903.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r748_nr_5F748.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r748_nr_5F748 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1905 (s : N.State) (i : N.Inputs) :
  R.v1905 (state s) (inputs i) = Zmod.unsigned (N.v1905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1905 s i)) at 1.
  unfold R.v1905, N.v1905.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1906 (s : N.State) (i : N.Inputs) :
  R.v1906 (state s) (inputs i) = Zmod.unsigned (N.v1906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1906 s i)) at 1.
  unfold R.v1906, N.v1906.
  rewrite ?node_1905.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r749_nr_5F749.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r749_nr_5F749 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1907 (s : N.State) (i : N.Inputs) :
  R.v1907 (state s) (inputs i) = Zmod.unsigned (N.v1907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1907 s i)) at 1.
  unfold R.v1907, N.v1907.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1908 (s : N.State) (i : N.Inputs) :
  R.v1908 (state s) (inputs i) = Zmod.unsigned (N.v1908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1908 s i)) at 1.
  unfold R.v1908, N.v1908.
  rewrite ?node_1907.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r750_nr_5F750.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r750_nr_5F750 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1909 (s : N.State) (i : N.Inputs) :
  R.v1909 (state s) (inputs i) = Zmod.unsigned (N.v1909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1909 s i)) at 1.
  unfold R.v1909, N.v1909.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1910 (s : N.State) (i : N.Inputs) :
  R.v1910 (state s) (inputs i) = Zmod.unsigned (N.v1910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1910 s i)) at 1.
  unfold R.v1910, N.v1910.
  rewrite ?node_1909.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r751_nr_5F751.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r751_nr_5F751 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1911 (s : N.State) (i : N.Inputs) :
  R.v1911 (state s) (inputs i) = Zmod.unsigned (N.v1911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1911 s i)) at 1.
  unfold R.v1911, N.v1911.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1912 (s : N.State) (i : N.Inputs) :
  R.v1912 (state s) (inputs i) = Zmod.unsigned (N.v1912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1912 s i)) at 1.
  unfold R.v1912, N.v1912.
  rewrite ?node_1911.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r752_nr_5F752.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r752_nr_5F752 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1913 (s : N.State) (i : N.Inputs) :
  R.v1913 (state s) (inputs i) = Zmod.unsigned (N.v1913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1913 s i)) at 1.
  unfold R.v1913, N.v1913.
  rewrite ?node_1858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1914 (s : N.State) (i : N.Inputs) :
  R.v1914 (state s) (inputs i) = Zmod.unsigned (N.v1914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1914 s i)) at 1.
  unfold R.v1914, N.v1914.
  rewrite ?node_1913.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r753_nr_5F753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r753_nr_5F753 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1915 (s : N.State) (i : N.Inputs) :
  R.v1915 (state s) (inputs i) = Zmod.unsigned (N.v1915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1915 s i)) at 1.
  unfold R.v1915, N.v1915.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1916 (s : N.State) (i : N.Inputs) :
  R.v1916 (state s) (inputs i) = Zmod.unsigned (N.v1916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1916 s i)) at 1.
  unfold R.v1916, N.v1916.
  rewrite ?node_1915.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r754_nr_5F754.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r754_nr_5F754 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1917 (s : N.State) (i : N.Inputs) :
  R.v1917 (state s) (inputs i) = Zmod.unsigned (N.v1917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1917 s i)) at 1.
  unfold R.v1917, N.v1917.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1918 (s : N.State) (i : N.Inputs) :
  R.v1918 (state s) (inputs i) = Zmod.unsigned (N.v1918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1918 s i)) at 1.
  unfold R.v1918, N.v1918.
  rewrite ?node_1917.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r755_nr_5F755.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r755_nr_5F755 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1919 (s : N.State) (i : N.Inputs) :
  R.v1919 (state s) (inputs i) = Zmod.unsigned (N.v1919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1919 s i)) at 1.
  unfold R.v1919, N.v1919.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1920 (s : N.State) (i : N.Inputs) :
  R.v1920 (state s) (inputs i) = Zmod.unsigned (N.v1920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1920 s i)) at 1.
  unfold R.v1920, N.v1920.
  rewrite ?node_1919.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r756_nr_5F756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r756_nr_5F756 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1921 (s : N.State) (i : N.Inputs) :
  R.v1921 (state s) (inputs i) = Zmod.unsigned (N.v1921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1921 s i)) at 1.
  unfold R.v1921, N.v1921.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1922 (s : N.State) (i : N.Inputs) :
  R.v1922 (state s) (inputs i) = Zmod.unsigned (N.v1922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1922 s i)) at 1.
  unfold R.v1922, N.v1922.
  rewrite ?node_1921.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r757_nr_5F757.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r757_nr_5F757 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1923 (s : N.State) (i : N.Inputs) :
  R.v1923 (state s) (inputs i) = Zmod.unsigned (N.v1923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1923 s i)) at 1.
  unfold R.v1923, N.v1923.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1924 (s : N.State) (i : N.Inputs) :
  R.v1924 (state s) (inputs i) = Zmod.unsigned (N.v1924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1924 s i)) at 1.
  unfold R.v1924, N.v1924.
  rewrite ?node_1923.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r758_nr_5F758.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r758_nr_5F758 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1925 (s : N.State) (i : N.Inputs) :
  R.v1925 (state s) (inputs i) = Zmod.unsigned (N.v1925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1925 s i)) at 1.
  unfold R.v1925, N.v1925.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1926 (s : N.State) (i : N.Inputs) :
  R.v1926 (state s) (inputs i) = Zmod.unsigned (N.v1926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1926 s i)) at 1.
  unfold R.v1926, N.v1926.
  rewrite ?node_1925.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r759_nr_5F759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r759_nr_5F759 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1927 (s : N.State) (i : N.Inputs) :
  R.v1927 (state s) (inputs i) = Zmod.unsigned (N.v1927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1927 s i)) at 1.
  unfold R.v1927, N.v1927.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1928 (s : N.State) (i : N.Inputs) :
  R.v1928 (state s) (inputs i) = Zmod.unsigned (N.v1928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1928 s i)) at 1.
  unfold R.v1928, N.v1928.
  rewrite ?node_1927.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r760_nr_5F760.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r760_nr_5F760 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1929 (s : N.State) (i : N.Inputs) :
  R.v1929 (state s) (inputs i) = Zmod.unsigned (N.v1929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1929 s i)) at 1.
  unfold R.v1929, N.v1929.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1930 (s : N.State) (i : N.Inputs) :
  R.v1930 (state s) (inputs i) = Zmod.unsigned (N.v1930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1930 s i)) at 1.
  unfold R.v1930, N.v1930.
  rewrite ?node_1929.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r761_nr_5F761.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r761_nr_5F761 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1931 (s : N.State) (i : N.Inputs) :
  R.v1931 (state s) (inputs i) = Zmod.unsigned (N.v1931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1931 s i)) at 1.
  unfold R.v1931, N.v1931.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1932 (s : N.State) (i : N.Inputs) :
  R.v1932 (state s) (inputs i) = Zmod.unsigned (N.v1932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1932 s i)) at 1.
  unfold R.v1932, N.v1932.
  rewrite ?node_1931.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r762_nr_5F762.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r762_nr_5F762 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1933 (s : N.State) (i : N.Inputs) :
  R.v1933 (state s) (inputs i) = Zmod.unsigned (N.v1933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1933 s i)) at 1.
  unfold R.v1933, N.v1933.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1934 (s : N.State) (i : N.Inputs) :
  R.v1934 (state s) (inputs i) = Zmod.unsigned (N.v1934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1934 s i)) at 1.
  unfold R.v1934, N.v1934.
  rewrite ?node_1933.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r763_nr_5F763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r763_nr_5F763 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1935 (s : N.State) (i : N.Inputs) :
  R.v1935 (state s) (inputs i) = Zmod.unsigned (N.v1935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1935 s i)) at 1.
  unfold R.v1935, N.v1935.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1936 (s : N.State) (i : N.Inputs) :
  R.v1936 (state s) (inputs i) = Zmod.unsigned (N.v1936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1936 s i)) at 1.
  unfold R.v1936, N.v1936.
  rewrite ?node_1935.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r764_nr_5F764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r764_nr_5F764 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1937 (s : N.State) (i : N.Inputs) :
  R.v1937 (state s) (inputs i) = Zmod.unsigned (N.v1937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1937 s i)) at 1.
  unfold R.v1937, N.v1937.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1938 (s : N.State) (i : N.Inputs) :
  R.v1938 (state s) (inputs i) = Zmod.unsigned (N.v1938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1938 s i)) at 1.
  unfold R.v1938, N.v1938.
  rewrite ?node_1937.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r765_nr_5F765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r765_nr_5F765 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1939 (s : N.State) (i : N.Inputs) :
  R.v1939 (state s) (inputs i) = Zmod.unsigned (N.v1939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1939 s i)) at 1.
  unfold R.v1939, N.v1939.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1940 (s : N.State) (i : N.Inputs) :
  R.v1940 (state s) (inputs i) = Zmod.unsigned (N.v1940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1940 s i)) at 1.
  unfold R.v1940, N.v1940.
  rewrite ?node_1939.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r766_nr_5F766.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r766_nr_5F766 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1941 (s : N.State) (i : N.Inputs) :
  R.v1941 (state s) (inputs i) = Zmod.unsigned (N.v1941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1941 s i)) at 1.
  unfold R.v1941, N.v1941.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1942 (s : N.State) (i : N.Inputs) :
  R.v1942 (state s) (inputs i) = Zmod.unsigned (N.v1942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1942 s i)) at 1.
  unfold R.v1942, N.v1942.
  rewrite ?node_1941.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r767_nr_5F767.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r767_nr_5F767 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1943 (s : N.State) (i : N.Inputs) :
  R.v1943 (state s) (inputs i) = Zmod.unsigned (N.v1943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1943 s i)) at 1.
  unfold R.v1943, N.v1943.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1944 (s : N.State) (i : N.Inputs) :
  R.v1944 (state s) (inputs i) = Zmod.unsigned (N.v1944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1944 s i)) at 1.
  unfold R.v1944, N.v1944.
  rewrite ?node_1943.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r768_nr_5F768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r768_nr_5F768 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1945 (s : N.State) (i : N.Inputs) :
  R.v1945 (state s) (inputs i) = Zmod.unsigned (N.v1945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1945 s i)) at 1.
  unfold R.v1945, N.v1945.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1946 (s : N.State) (i : N.Inputs) :
  R.v1946 (state s) (inputs i) = Zmod.unsigned (N.v1946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1946 s i)) at 1.
  unfold R.v1946, N.v1946.
  rewrite ?node_1945.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r769_nr_5F769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r769_nr_5F769 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1947 (s : N.State) (i : N.Inputs) :
  R.v1947 (state s) (inputs i) = Zmod.unsigned (N.v1947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1947 s i)) at 1.
  unfold R.v1947, N.v1947.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1948 (s : N.State) (i : N.Inputs) :
  R.v1948 (state s) (inputs i) = Zmod.unsigned (N.v1948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1948 s i)) at 1.
  unfold R.v1948, N.v1948.
  rewrite ?node_1947.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r770_nr_5F770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r770_nr_5F770 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1949 (s : N.State) (i : N.Inputs) :
  R.v1949 (state s) (inputs i) = Zmod.unsigned (N.v1949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1949 s i)) at 1.
  unfold R.v1949, N.v1949.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1950 (s : N.State) (i : N.Inputs) :
  R.v1950 (state s) (inputs i) = Zmod.unsigned (N.v1950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1950 s i)) at 1.
  unfold R.v1950, N.v1950.
  rewrite ?node_1949.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r771_nr_5F771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r771_nr_5F771 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1951 (s : N.State) (i : N.Inputs) :
  R.v1951 (state s) (inputs i) = Zmod.unsigned (N.v1951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1951 s i)) at 1.
  unfold R.v1951, N.v1951.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1952 (s : N.State) (i : N.Inputs) :
  R.v1952 (state s) (inputs i) = Zmod.unsigned (N.v1952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1952 s i)) at 1.
  unfold R.v1952, N.v1952.
  rewrite ?node_1951.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r772_nr_5F772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r772_nr_5F772 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1953 (s : N.State) (i : N.Inputs) :
  R.v1953 (state s) (inputs i) = Zmod.unsigned (N.v1953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1953 s i)) at 1.
  unfold R.v1953, N.v1953.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1954 (s : N.State) (i : N.Inputs) :
  R.v1954 (state s) (inputs i) = Zmod.unsigned (N.v1954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1954 s i)) at 1.
  unfold R.v1954, N.v1954.
  rewrite ?node_1953.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r773_nr_5F773.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r773_nr_5F773 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1955 (s : N.State) (i : N.Inputs) :
  R.v1955 (state s) (inputs i) = Zmod.unsigned (N.v1955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1955 s i)) at 1.
  unfold R.v1955, N.v1955.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1956 (s : N.State) (i : N.Inputs) :
  R.v1956 (state s) (inputs i) = Zmod.unsigned (N.v1956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1956 s i)) at 1.
  unfold R.v1956, N.v1956.
  rewrite ?node_1955.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r774_nr_5F774.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r774_nr_5F774 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1957 (s : N.State) (i : N.Inputs) :
  R.v1957 (state s) (inputs i) = Zmod.unsigned (N.v1957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1957 s i)) at 1.
  unfold R.v1957, N.v1957.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1958 (s : N.State) (i : N.Inputs) :
  R.v1958 (state s) (inputs i) = Zmod.unsigned (N.v1958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1958 s i)) at 1.
  unfold R.v1958, N.v1958.
  rewrite ?node_1957.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r775_nr_5F775.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r775_nr_5F775 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1959 (s : N.State) (i : N.Inputs) :
  R.v1959 (state s) (inputs i) = Zmod.unsigned (N.v1959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1959 s i)) at 1.
  unfold R.v1959, N.v1959.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1960 (s : N.State) (i : N.Inputs) :
  R.v1960 (state s) (inputs i) = Zmod.unsigned (N.v1960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1960 s i)) at 1.
  unfold R.v1960, N.v1960.
  rewrite ?node_1959.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r776_nr_5F776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r776_nr_5F776 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1961 (s : N.State) (i : N.Inputs) :
  R.v1961 (state s) (inputs i) = Zmod.unsigned (N.v1961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1961 s i)) at 1.
  unfold R.v1961, N.v1961.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1962 (s : N.State) (i : N.Inputs) :
  R.v1962 (state s) (inputs i) = Zmod.unsigned (N.v1962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1962 s i)) at 1.
  unfold R.v1962, N.v1962.
  rewrite ?node_1961.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r777_nr_5F777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r777_nr_5F777 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1963 (s : N.State) (i : N.Inputs) :
  R.v1963 (state s) (inputs i) = Zmod.unsigned (N.v1963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1963 s i)) at 1.
  unfold R.v1963, N.v1963.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1964 (s : N.State) (i : N.Inputs) :
  R.v1964 (state s) (inputs i) = Zmod.unsigned (N.v1964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1964 s i)) at 1.
  unfold R.v1964, N.v1964.
  rewrite ?node_1963.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r778_nr_5F778.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r778_nr_5F778 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1965 (s : N.State) (i : N.Inputs) :
  R.v1965 (state s) (inputs i) = Zmod.unsigned (N.v1965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1965 s i)) at 1.
  unfold R.v1965, N.v1965.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1966 (s : N.State) (i : N.Inputs) :
  R.v1966 (state s) (inputs i) = Zmod.unsigned (N.v1966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1966 s i)) at 1.
  unfold R.v1966, N.v1966.
  rewrite ?node_1965.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r779_nr_5F779.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r779_nr_5F779 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1967 (s : N.State) (i : N.Inputs) :
  R.v1967 (state s) (inputs i) = Zmod.unsigned (N.v1967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1967 s i)) at 1.
  unfold R.v1967, N.v1967.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1968 (s : N.State) (i : N.Inputs) :
  R.v1968 (state s) (inputs i) = Zmod.unsigned (N.v1968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1968 s i)) at 1.
  unfold R.v1968, N.v1968.
  unfold R.v33, N.v33.
  rewrite ?node_1967.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1969 (s : N.State) (i : N.Inputs) :
  R.v1969 (state s) (inputs i) = Zmod.unsigned (N.v1969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1969 s i)) at 1.
  unfold R.v1969, N.v1969.
  unfold R.v35, N.v35.
  rewrite ?node_1967.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1970 (s : N.State) (i : N.Inputs) :
  R.v1970 (state s) (inputs i) = Zmod.unsigned (N.v1970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1970 s i)) at 1.
  unfold R.v1970, N.v1970.
  rewrite ?node_1968.
  rewrite ?node_1969.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1971 (s : N.State) (i : N.Inputs) :
  R.v1971 (state s) (inputs i) = Zmod.unsigned (N.v1971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1971 s i)) at 1.
  unfold R.v1971, N.v1971.
  unfold R.v39, N.v39.
  rewrite ?node_1967.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1972 (s : N.State) (i : N.Inputs) :
  R.v1972 (state s) (inputs i) = Zmod.unsigned (N.v1972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1972 s i)) at 1.
  unfold R.v1972, N.v1972.
  unfold R.v42, N.v42.
  rewrite ?node_1967.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1973 (s : N.State) (i : N.Inputs) :
  R.v1973 (state s) (inputs i) = Zmod.unsigned (N.v1973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1973 s i)) at 1.
  unfold R.v1973, N.v1973.
  unfold R.v45, N.v45.
  rewrite ?node_1967.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1974 (s : N.State) (i : N.Inputs) :
  R.v1974 (state s) (inputs i) = Zmod.unsigned (N.v1974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1974 s i)) at 1.
  unfold R.v1974, N.v1974.
  unfold R.v47, N.v47.
  rewrite ?node_1967.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1975 (s : N.State) (i : N.Inputs) :
  R.v1975 (state s) (inputs i) = Zmod.unsigned (N.v1975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1975 s i)) at 1.
  unfold R.v1975, N.v1975.
  rewrite ?node_1973.
  rewrite ?node_1974.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1976 (s : N.State) (i : N.Inputs) :
  R.v1976 (state s) (inputs i) = Zmod.unsigned (N.v1976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1976 s i)) at 1.
  unfold R.v1976, N.v1976.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_1975.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1977 (s : N.State) (i : N.Inputs) :
  R.v1977 (state s) (inputs i) = Zmod.unsigned (N.v1977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1977 s i)) at 1.
  unfold R.v1977, N.v1977.
  rewrite ?node_44.
  rewrite ?node_1972.
  rewrite ?node_1976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1978 (s : N.State) (i : N.Inputs) :
  R.v1978 (state s) (inputs i) = Zmod.unsigned (N.v1978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1978 s i)) at 1.
  unfold R.v1978, N.v1978.
  rewrite ?node_41.
  rewrite ?node_1971.
  rewrite ?node_1977.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1979 (s : N.State) (i : N.Inputs) :
  R.v1979 (state s) (inputs i) = Zmod.unsigned (N.v1979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1979 s i)) at 1.
  unfold R.v1979, N.v1979.
  rewrite ?node_38.
  rewrite ?node_1970.
  rewrite ?node_1978.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1980 (s : N.State) (i : N.Inputs) :
  R.v1980 (state s) (inputs i) = Zmod.unsigned (N.v1980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1980 s i)) at 1.
  unfold R.v1980, N.v1980.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1981 (s : N.State) (i : N.Inputs) :
  R.v1981 (state s) (inputs i) = Zmod.unsigned (N.v1981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1981 s i)) at 1.
  unfold R.v1981, N.v1981.
  rewrite ?node_1980.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r780_nr_5F780.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r780_nr_5F780 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1982 (s : N.State) (i : N.Inputs) :
  R.v1982 (state s) (inputs i) = Zmod.unsigned (N.v1982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1982 s i)) at 1.
  unfold R.v1982, N.v1982.
  unfold R.v6, N.v6.
  rewrite ?node_1971.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1983 (s : N.State) (i : N.Inputs) :
  R.v1983 (state s) (inputs i) = Zmod.unsigned (N.v1983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1983 s i)) at 1.
  unfold R.v1983, N.v1983.
  unfold R.v19, N.v19.
  rewrite ?node_1970.
  rewrite ?node_1982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1984 (s : N.State) (i : N.Inputs) :
  R.v1984 (state s) (inputs i) = Zmod.unsigned (N.v1984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1984 s i)) at 1.
  unfold R.v1984, N.v1984.
  rewrite ?node_1983.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1985 (s : N.State) (i : N.Inputs) :
  R.v1985 (state s) (inputs i) = Zmod.unsigned (N.v1985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1985 s i)) at 1.
  unfold R.v1985, N.v1985.
  rewrite ?node_1984.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r781_nr_5F781.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r781_nr_5F781 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1986 (s : N.State) (i : N.Inputs) :
  R.v1986 (state s) (inputs i) = Zmod.unsigned (N.v1986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1986 s i)) at 1.
  unfold R.v1986, N.v1986.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1987 (s : N.State) (i : N.Inputs) :
  R.v1987 (state s) (inputs i) = Zmod.unsigned (N.v1987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1987 s i)) at 1.
  unfold R.v1987, N.v1987.
  rewrite ?node_1986.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r782_nr_5F782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r782_nr_5F782 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1988 (s : N.State) (i : N.Inputs) :
  R.v1988 (state s) (inputs i) = Zmod.unsigned (N.v1988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1988 s i)) at 1.
  unfold R.v1988, N.v1988.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1989 (s : N.State) (i : N.Inputs) :
  R.v1989 (state s) (inputs i) = Zmod.unsigned (N.v1989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1989 s i)) at 1.
  unfold R.v1989, N.v1989.
  rewrite ?node_1988.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r783_nr_5F783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r783_nr_5F783 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1990 (s : N.State) (i : N.Inputs) :
  R.v1990 (state s) (inputs i) = Zmod.unsigned (N.v1990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1990 s i)) at 1.
  unfold R.v1990, N.v1990.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1991 (s : N.State) (i : N.Inputs) :
  R.v1991 (state s) (inputs i) = Zmod.unsigned (N.v1991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1991 s i)) at 1.
  unfold R.v1991, N.v1991.
  rewrite ?node_1990.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r784_nr_5F784.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r784_nr_5F784 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1992 (s : N.State) (i : N.Inputs) :
  R.v1992 (state s) (inputs i) = Zmod.unsigned (N.v1992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1992 s i)) at 1.
  unfold R.v1992, N.v1992.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1993 (s : N.State) (i : N.Inputs) :
  R.v1993 (state s) (inputs i) = Zmod.unsigned (N.v1993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1993 s i)) at 1.
  unfold R.v1993, N.v1993.
  rewrite ?node_1992.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r785_nr_5F785.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r785_nr_5F785 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1994 (s : N.State) (i : N.Inputs) :
  R.v1994 (state s) (inputs i) = Zmod.unsigned (N.v1994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1994 s i)) at 1.
  unfold R.v1994, N.v1994.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1995 (s : N.State) (i : N.Inputs) :
  R.v1995 (state s) (inputs i) = Zmod.unsigned (N.v1995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1995 s i)) at 1.
  unfold R.v1995, N.v1995.
  rewrite ?node_1994.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r786_nr_5F786.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r786_nr_5F786 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1996 (s : N.State) (i : N.Inputs) :
  R.v1996 (state s) (inputs i) = Zmod.unsigned (N.v1996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1996 s i)) at 1.
  unfold R.v1996, N.v1996.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1997 (s : N.State) (i : N.Inputs) :
  R.v1997 (state s) (inputs i) = Zmod.unsigned (N.v1997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1997 s i)) at 1.
  unfold R.v1997, N.v1997.
  rewrite ?node_1996.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r787_nr_5F787.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r787_nr_5F787 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1998 (s : N.State) (i : N.Inputs) :
  R.v1998 (state s) (inputs i) = Zmod.unsigned (N.v1998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1998 s i)) at 1.
  unfold R.v1998, N.v1998.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1999 (s : N.State) (i : N.Inputs) :
  R.v1999 (state s) (inputs i) = Zmod.unsigned (N.v1999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1999 s i)) at 1.
  unfold R.v1999, N.v1999.
  rewrite ?node_1998.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r788_nr_5F788.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r788_nr_5F788 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
