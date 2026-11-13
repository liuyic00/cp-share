(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes003.
Lemma node_4000 (s : N.State) (i : N.Inputs) :
  R.v4000 (state s) (inputs i) = Zmod.unsigned (N.v4000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4000 s i)) at 1.
  unfold R.v4000, N.v4000.
  rewrite ?node_3999.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1738_nr_5F1747.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1738_nr_5F1747 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4001 (s : N.State) (i : N.Inputs) :
  R.v4001 (state s) (inputs i) = Zmod.unsigned (N.v4001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4001 s i)) at 1.
  unfold R.v4001, N.v4001.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4002 (s : N.State) (i : N.Inputs) :
  R.v4002 (state s) (inputs i) = Zmod.unsigned (N.v4002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4002 s i)) at 1.
  unfold R.v4002, N.v4002.
  rewrite ?node_4001.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1739_nr_5F1748.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1739_nr_5F1748 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4003 (s : N.State) (i : N.Inputs) :
  R.v4003 (state s) (inputs i) = Zmod.unsigned (N.v4003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4003 s i)) at 1.
  unfold R.v4003, N.v4003.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4004 (s : N.State) (i : N.Inputs) :
  R.v4004 (state s) (inputs i) = Zmod.unsigned (N.v4004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4004 s i)) at 1.
  unfold R.v4004, N.v4004.
  rewrite ?node_4003.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1740_nr_5F1749.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1740_nr_5F1749 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4005 (s : N.State) (i : N.Inputs) :
  R.v4005 (state s) (inputs i) = Zmod.unsigned (N.v4005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4005 s i)) at 1.
  unfold R.v4005, N.v4005.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4006 (s : N.State) (i : N.Inputs) :
  R.v4006 (state s) (inputs i) = Zmod.unsigned (N.v4006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4006 s i)) at 1.
  unfold R.v4006, N.v4006.
  rewrite ?node_4005.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1741_nr_5F1750.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1741_nr_5F1750 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4007 (s : N.State) (i : N.Inputs) :
  R.v4007 (state s) (inputs i) = Zmod.unsigned (N.v4007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4007 s i)) at 1.
  unfold R.v4007, N.v4007.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4008 (s : N.State) (i : N.Inputs) :
  R.v4008 (state s) (inputs i) = Zmod.unsigned (N.v4008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4008 s i)) at 1.
  unfold R.v4008, N.v4008.
  rewrite ?node_4007.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1742_nr_5F1751.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1742_nr_5F1751 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4009 (s : N.State) (i : N.Inputs) :
  R.v4009 (state s) (inputs i) = Zmod.unsigned (N.v4009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4009 s i)) at 1.
  unfold R.v4009, N.v4009.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4010 (s : N.State) (i : N.Inputs) :
  R.v4010 (state s) (inputs i) = Zmod.unsigned (N.v4010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4010 s i)) at 1.
  unfold R.v4010, N.v4010.
  rewrite ?node_4009.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1743_nr_5F1752.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1743_nr_5F1752 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4011 (s : N.State) (i : N.Inputs) :
  R.v4011 (state s) (inputs i) = Zmod.unsigned (N.v4011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4011 s i)) at 1.
  unfold R.v4011, N.v4011.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4012 (s : N.State) (i : N.Inputs) :
  R.v4012 (state s) (inputs i) = Zmod.unsigned (N.v4012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4012 s i)) at 1.
  unfold R.v4012, N.v4012.
  rewrite ?node_4011.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1744_nr_5F1753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1744_nr_5F1753 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4013 (s : N.State) (i : N.Inputs) :
  R.v4013 (state s) (inputs i) = Zmod.unsigned (N.v4013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4013 s i)) at 1.
  unfold R.v4013, N.v4013.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4014 (s : N.State) (i : N.Inputs) :
  R.v4014 (state s) (inputs i) = Zmod.unsigned (N.v4014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4014 s i)) at 1.
  unfold R.v4014, N.v4014.
  rewrite ?node_4013.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1745_nr_5F1754.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1745_nr_5F1754 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4015 (s : N.State) (i : N.Inputs) :
  R.v4015 (state s) (inputs i) = Zmod.unsigned (N.v4015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4015 s i)) at 1.
  unfold R.v4015, N.v4015.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4016 (s : N.State) (i : N.Inputs) :
  R.v4016 (state s) (inputs i) = Zmod.unsigned (N.v4016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4016 s i)) at 1.
  unfold R.v4016, N.v4016.
  rewrite ?node_4015.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1746_nr_5F1755.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1746_nr_5F1755 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4017 (s : N.State) (i : N.Inputs) :
  R.v4017 (state s) (inputs i) = Zmod.unsigned (N.v4017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4017 s i)) at 1.
  unfold R.v4017, N.v4017.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4018 (s : N.State) (i : N.Inputs) :
  R.v4018 (state s) (inputs i) = Zmod.unsigned (N.v4018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4018 s i)) at 1.
  unfold R.v4018, N.v4018.
  rewrite ?node_4017.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1747_nr_5F1756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1747_nr_5F1756 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4019 (s : N.State) (i : N.Inputs) :
  R.v4019 (state s) (inputs i) = Zmod.unsigned (N.v4019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4019 s i)) at 1.
  unfold R.v4019, N.v4019.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4020 (s : N.State) (i : N.Inputs) :
  R.v4020 (state s) (inputs i) = Zmod.unsigned (N.v4020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4020 s i)) at 1.
  unfold R.v4020, N.v4020.
  rewrite ?node_4019.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1748_nr_5F1757.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1748_nr_5F1757 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4021 (s : N.State) (i : N.Inputs) :
  R.v4021 (state s) (inputs i) = Zmod.unsigned (N.v4021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4021 s i)) at 1.
  unfold R.v4021, N.v4021.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4022 (s : N.State) (i : N.Inputs) :
  R.v4022 (state s) (inputs i) = Zmod.unsigned (N.v4022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4022 s i)) at 1.
  unfold R.v4022, N.v4022.
  rewrite ?node_4021.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1749_nr_5F1758.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1749_nr_5F1758 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4023 (s : N.State) (i : N.Inputs) :
  R.v4023 (state s) (inputs i) = Zmod.unsigned (N.v4023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4023 s i)) at 1.
  unfold R.v4023, N.v4023.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4024 (s : N.State) (i : N.Inputs) :
  R.v4024 (state s) (inputs i) = Zmod.unsigned (N.v4024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4024 s i)) at 1.
  unfold R.v4024, N.v4024.
  unfold R.v3021, N.v3021.
  rewrite ?node_4023.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4025 (s : N.State) (i : N.Inputs) :
  R.v4025 (state s) (inputs i) = Zmod.unsigned (N.v4025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4025 s i)) at 1.
  unfold R.v4025, N.v4025.
  rewrite ?node_4024.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1750_nr_5F1759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1750_nr_5F1759 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4026 (s : N.State) (i : N.Inputs) :
  R.v4026 (state s) (inputs i) = Zmod.unsigned (N.v4026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4026 s i)) at 1.
  unfold R.v4026, N.v4026.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4027 (s : N.State) (i : N.Inputs) :
  R.v4027 (state s) (inputs i) = Zmod.unsigned (N.v4027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4027 s i)) at 1.
  unfold R.v4027, N.v4027.
  rewrite ?node_4026.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1751_nr_5F1760.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1751_nr_5F1760 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4028 (s : N.State) (i : N.Inputs) :
  R.v4028 (state s) (inputs i) = Zmod.unsigned (N.v4028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4028 s i)) at 1.
  unfold R.v4028, N.v4028.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4029 (s : N.State) (i : N.Inputs) :
  R.v4029 (state s) (inputs i) = Zmod.unsigned (N.v4029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4029 s i)) at 1.
  unfold R.v4029, N.v4029.
  rewrite ?node_4028.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1752_nr_5F1761.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1752_nr_5F1761 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4030 (s : N.State) (i : N.Inputs) :
  R.v4030 (state s) (inputs i) = Zmod.unsigned (N.v4030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4030 s i)) at 1.
  unfold R.v4030, N.v4030.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4031 (s : N.State) (i : N.Inputs) :
  R.v4031 (state s) (inputs i) = Zmod.unsigned (N.v4031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4031 s i)) at 1.
  unfold R.v4031, N.v4031.
  rewrite ?node_4030.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1753_nr_5F1762.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1753_nr_5F1762 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4032 (s : N.State) (i : N.Inputs) :
  R.v4032 (state s) (inputs i) = Zmod.unsigned (N.v4032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4032 s i)) at 1.
  unfold R.v4032, N.v4032.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4033 (s : N.State) (i : N.Inputs) :
  R.v4033 (state s) (inputs i) = Zmod.unsigned (N.v4033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4033 s i)) at 1.
  unfold R.v4033, N.v4033.
  rewrite ?node_4032.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1754_nr_5F1763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1754_nr_5F1763 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4034 (s : N.State) (i : N.Inputs) :
  R.v4034 (state s) (inputs i) = Zmod.unsigned (N.v4034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4034 s i)) at 1.
  unfold R.v4034, N.v4034.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4035 (s : N.State) (i : N.Inputs) :
  R.v4035 (state s) (inputs i) = Zmod.unsigned (N.v4035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4035 s i)) at 1.
  unfold R.v4035, N.v4035.
  rewrite ?node_4034.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1755_nr_5F1764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1755_nr_5F1764 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4036 (s : N.State) (i : N.Inputs) :
  R.v4036 (state s) (inputs i) = Zmod.unsigned (N.v4036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4036 s i)) at 1.
  unfold R.v4036, N.v4036.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4037 (s : N.State) (i : N.Inputs) :
  R.v4037 (state s) (inputs i) = Zmod.unsigned (N.v4037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4037 s i)) at 1.
  unfold R.v4037, N.v4037.
  rewrite ?node_4036.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1756_nr_5F1765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1756_nr_5F1765 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4038 (s : N.State) (i : N.Inputs) :
  R.v4038 (state s) (inputs i) = Zmod.unsigned (N.v4038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4038 s i)) at 1.
  unfold R.v4038, N.v4038.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4039 (s : N.State) (i : N.Inputs) :
  R.v4039 (state s) (inputs i) = Zmod.unsigned (N.v4039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4039 s i)) at 1.
  unfold R.v4039, N.v4039.
  rewrite ?node_4038.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1757_nr_5F1766.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1757_nr_5F1766 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4040 (s : N.State) (i : N.Inputs) :
  R.v4040 (state s) (inputs i) = Zmod.unsigned (N.v4040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4040 s i)) at 1.
  unfold R.v4040, N.v4040.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4041 (s : N.State) (i : N.Inputs) :
  R.v4041 (state s) (inputs i) = Zmod.unsigned (N.v4041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4041 s i)) at 1.
  unfold R.v4041, N.v4041.
  rewrite ?node_4040.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1758_nr_5F1767.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1758_nr_5F1767 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4042 (s : N.State) (i : N.Inputs) :
  R.v4042 (state s) (inputs i) = Zmod.unsigned (N.v4042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4042 s i)) at 1.
  unfold R.v4042, N.v4042.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4043 (s : N.State) (i : N.Inputs) :
  R.v4043 (state s) (inputs i) = Zmod.unsigned (N.v4043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4043 s i)) at 1.
  unfold R.v4043, N.v4043.
  rewrite ?node_4042.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1759_nr_5F1768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1759_nr_5F1768 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4044 (s : N.State) (i : N.Inputs) :
  R.v4044 (state s) (inputs i) = Zmod.unsigned (N.v4044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4044 s i)) at 1.
  unfold R.v4044, N.v4044.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4045 (s : N.State) (i : N.Inputs) :
  R.v4045 (state s) (inputs i) = Zmod.unsigned (N.v4045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4045 s i)) at 1.
  unfold R.v4045, N.v4045.
  rewrite ?node_4044.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1760_nr_5F1769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1760_nr_5F1769 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4046 (s : N.State) (i : N.Inputs) :
  R.v4046 (state s) (inputs i) = Zmod.unsigned (N.v4046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4046 s i)) at 1.
  unfold R.v4046, N.v4046.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4047 (s : N.State) (i : N.Inputs) :
  R.v4047 (state s) (inputs i) = Zmod.unsigned (N.v4047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4047 s i)) at 1.
  unfold R.v4047, N.v4047.
  rewrite ?node_4046.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1761_nr_5F1770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1761_nr_5F1770 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4048 (s : N.State) (i : N.Inputs) :
  R.v4048 (state s) (inputs i) = Zmod.unsigned (N.v4048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4048 s i)) at 1.
  unfold R.v4048, N.v4048.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4049 (s : N.State) (i : N.Inputs) :
  R.v4049 (state s) (inputs i) = Zmod.unsigned (N.v4049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4049 s i)) at 1.
  unfold R.v4049, N.v4049.
  rewrite ?node_4048.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1762_nr_5F1771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1762_nr_5F1771 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4050 (s : N.State) (i : N.Inputs) :
  R.v4050 (state s) (inputs i) = Zmod.unsigned (N.v4050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4050 s i)) at 1.
  unfold R.v4050, N.v4050.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4051 (s : N.State) (i : N.Inputs) :
  R.v4051 (state s) (inputs i) = Zmod.unsigned (N.v4051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4051 s i)) at 1.
  unfold R.v4051, N.v4051.
  rewrite ?node_4050.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1763_nr_5F1772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1763_nr_5F1772 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4052 (s : N.State) (i : N.Inputs) :
  R.v4052 (state s) (inputs i) = Zmod.unsigned (N.v4052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4052 s i)) at 1.
  unfold R.v4052, N.v4052.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4053 (s : N.State) (i : N.Inputs) :
  R.v4053 (state s) (inputs i) = Zmod.unsigned (N.v4053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4053 s i)) at 1.
  unfold R.v4053, N.v4053.
  rewrite ?node_4052.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1764_nr_5F1773.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1764_nr_5F1773 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4054 (s : N.State) (i : N.Inputs) :
  R.v4054 (state s) (inputs i) = Zmod.unsigned (N.v4054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4054 s i)) at 1.
  unfold R.v4054, N.v4054.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4055 (s : N.State) (i : N.Inputs) :
  R.v4055 (state s) (inputs i) = Zmod.unsigned (N.v4055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4055 s i)) at 1.
  unfold R.v4055, N.v4055.
  rewrite ?node_4054.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1765_nr_5F1774.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1765_nr_5F1774 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4056 (s : N.State) (i : N.Inputs) :
  R.v4056 (state s) (inputs i) = Zmod.unsigned (N.v4056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4056 s i)) at 1.
  unfold R.v4056, N.v4056.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4057 (s : N.State) (i : N.Inputs) :
  R.v4057 (state s) (inputs i) = Zmod.unsigned (N.v4057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4057 s i)) at 1.
  unfold R.v4057, N.v4057.
  rewrite ?node_4056.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1766_nr_5F1775.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1766_nr_5F1775 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4058 (s : N.State) (i : N.Inputs) :
  R.v4058 (state s) (inputs i) = Zmod.unsigned (N.v4058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4058 s i)) at 1.
  unfold R.v4058, N.v4058.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4059 (s : N.State) (i : N.Inputs) :
  R.v4059 (state s) (inputs i) = Zmod.unsigned (N.v4059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4059 s i)) at 1.
  unfold R.v4059, N.v4059.
  rewrite ?node_4058.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1767_nr_5F1776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1767_nr_5F1776 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4060 (s : N.State) (i : N.Inputs) :
  R.v4060 (state s) (inputs i) = Zmod.unsigned (N.v4060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4060 s i)) at 1.
  unfold R.v4060, N.v4060.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4061 (s : N.State) (i : N.Inputs) :
  R.v4061 (state s) (inputs i) = Zmod.unsigned (N.v4061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4061 s i)) at 1.
  unfold R.v4061, N.v4061.
  rewrite ?node_4060.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1768_nr_5F1777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1768_nr_5F1777 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4062 (s : N.State) (i : N.Inputs) :
  R.v4062 (state s) (inputs i) = Zmod.unsigned (N.v4062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4062 s i)) at 1.
  unfold R.v4062, N.v4062.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4063 (s : N.State) (i : N.Inputs) :
  R.v4063 (state s) (inputs i) = Zmod.unsigned (N.v4063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4063 s i)) at 1.
  unfold R.v4063, N.v4063.
  rewrite ?node_4062.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1769_nr_5F1778.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1769_nr_5F1778 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4064 (s : N.State) (i : N.Inputs) :
  R.v4064 (state s) (inputs i) = Zmod.unsigned (N.v4064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4064 s i)) at 1.
  unfold R.v4064, N.v4064.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4065 (s : N.State) (i : N.Inputs) :
  R.v4065 (state s) (inputs i) = Zmod.unsigned (N.v4065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4065 s i)) at 1.
  unfold R.v4065, N.v4065.
  rewrite ?node_4064.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1770_nr_5F1779.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1770_nr_5F1779 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4066 (s : N.State) (i : N.Inputs) :
  R.v4066 (state s) (inputs i) = Zmod.unsigned (N.v4066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4066 s i)) at 1.
  unfold R.v4066, N.v4066.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4067 (s : N.State) (i : N.Inputs) :
  R.v4067 (state s) (inputs i) = Zmod.unsigned (N.v4067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4067 s i)) at 1.
  unfold R.v4067, N.v4067.
  rewrite ?node_4066.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1771_nr_5F1780.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1771_nr_5F1780 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4068 (s : N.State) (i : N.Inputs) :
  R.v4068 (state s) (inputs i) = Zmod.unsigned (N.v4068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4068 s i)) at 1.
  unfold R.v4068, N.v4068.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4069 (s : N.State) (i : N.Inputs) :
  R.v4069 (state s) (inputs i) = Zmod.unsigned (N.v4069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4069 s i)) at 1.
  unfold R.v4069, N.v4069.
  rewrite ?node_4068.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1772_nr_5F1781.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1772_nr_5F1781 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4070 (s : N.State) (i : N.Inputs) :
  R.v4070 (state s) (inputs i) = Zmod.unsigned (N.v4070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4070 s i)) at 1.
  unfold R.v4070, N.v4070.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4071 (s : N.State) (i : N.Inputs) :
  R.v4071 (state s) (inputs i) = Zmod.unsigned (N.v4071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4071 s i)) at 1.
  unfold R.v4071, N.v4071.
  rewrite ?node_4070.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1773_nr_5F1783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1773_nr_5F1783 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4072 (s : N.State) (i : N.Inputs) :
  R.v4072 (state s) (inputs i) = Zmod.unsigned (N.v4072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4072 s i)) at 1.
  unfold R.v4072, N.v4072.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4073 (s : N.State) (i : N.Inputs) :
  R.v4073 (state s) (inputs i) = Zmod.unsigned (N.v4073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4073 s i)) at 1.
  unfold R.v4073, N.v4073.
  rewrite ?node_4072.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1774_nr_5F1784.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1774_nr_5F1784 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4074 (s : N.State) (i : N.Inputs) :
  R.v4074 (state s) (inputs i) = Zmod.unsigned (N.v4074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4074 s i)) at 1.
  unfold R.v4074, N.v4074.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4075 (s : N.State) (i : N.Inputs) :
  R.v4075 (state s) (inputs i) = Zmod.unsigned (N.v4075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4075 s i)) at 1.
  unfold R.v4075, N.v4075.
  rewrite ?node_4074.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1775_nr_5F1785.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1775_nr_5F1785 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4076 (s : N.State) (i : N.Inputs) :
  R.v4076 (state s) (inputs i) = Zmod.unsigned (N.v4076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4076 s i)) at 1.
  unfold R.v4076, N.v4076.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4077 (s : N.State) (i : N.Inputs) :
  R.v4077 (state s) (inputs i) = Zmod.unsigned (N.v4077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4077 s i)) at 1.
  unfold R.v4077, N.v4077.
  rewrite ?node_4076.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1776_nr_5F1786.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1776_nr_5F1786 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4078 (s : N.State) (i : N.Inputs) :
  R.v4078 (state s) (inputs i) = Zmod.unsigned (N.v4078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4078 s i)) at 1.
  unfold R.v4078, N.v4078.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4079 (s : N.State) (i : N.Inputs) :
  R.v4079 (state s) (inputs i) = Zmod.unsigned (N.v4079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4079 s i)) at 1.
  unfold R.v4079, N.v4079.
  rewrite ?node_4078.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1777_nr_5F1787.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1777_nr_5F1787 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4080 (s : N.State) (i : N.Inputs) :
  R.v4080 (state s) (inputs i) = Zmod.unsigned (N.v4080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4080 s i)) at 1.
  unfold R.v4080, N.v4080.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4081 (s : N.State) (i : N.Inputs) :
  R.v4081 (state s) (inputs i) = Zmod.unsigned (N.v4081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4081 s i)) at 1.
  unfold R.v4081, N.v4081.
  rewrite ?node_4080.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1778_nr_5F1788.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1778_nr_5F1788 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4082 (s : N.State) (i : N.Inputs) :
  R.v4082 (state s) (inputs i) = Zmod.unsigned (N.v4082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4082 s i)) at 1.
  unfold R.v4082, N.v4082.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4083 (s : N.State) (i : N.Inputs) :
  R.v4083 (state s) (inputs i) = Zmod.unsigned (N.v4083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4083 s i)) at 1.
  unfold R.v4083, N.v4083.
  rewrite ?node_4082.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1779_nr_5F1789.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1779_nr_5F1789 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4084 (s : N.State) (i : N.Inputs) :
  R.v4084 (state s) (inputs i) = Zmod.unsigned (N.v4084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4084 s i)) at 1.
  unfold R.v4084, N.v4084.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4085 (s : N.State) (i : N.Inputs) :
  R.v4085 (state s) (inputs i) = Zmod.unsigned (N.v4085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4085 s i)) at 1.
  unfold R.v4085, N.v4085.
  rewrite ?node_4084.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1780_nr_5F1790.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1780_nr_5F1790 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4086 (s : N.State) (i : N.Inputs) :
  R.v4086 (state s) (inputs i) = Zmod.unsigned (N.v4086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4086 s i)) at 1.
  unfold R.v4086, N.v4086.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4087 (s : N.State) (i : N.Inputs) :
  R.v4087 (state s) (inputs i) = Zmod.unsigned (N.v4087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4087 s i)) at 1.
  unfold R.v4087, N.v4087.
  rewrite ?node_4086.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1781_nr_5F1791.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1781_nr_5F1791 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4088 (s : N.State) (i : N.Inputs) :
  R.v4088 (state s) (inputs i) = Zmod.unsigned (N.v4088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4088 s i)) at 1.
  unfold R.v4088, N.v4088.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4089 (s : N.State) (i : N.Inputs) :
  R.v4089 (state s) (inputs i) = Zmod.unsigned (N.v4089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4089 s i)) at 1.
  unfold R.v4089, N.v4089.
  rewrite ?node_4088.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1782_nr_5F1792.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1782_nr_5F1792 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4090 (s : N.State) (i : N.Inputs) :
  R.v4090 (state s) (inputs i) = Zmod.unsigned (N.v4090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4090 s i)) at 1.
  unfold R.v4090, N.v4090.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4091 (s : N.State) (i : N.Inputs) :
  R.v4091 (state s) (inputs i) = Zmod.unsigned (N.v4091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4091 s i)) at 1.
  unfold R.v4091, N.v4091.
  rewrite ?node_4090.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1783_nr_5F1793.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1783_nr_5F1793 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4092 (s : N.State) (i : N.Inputs) :
  R.v4092 (state s) (inputs i) = Zmod.unsigned (N.v4092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4092 s i)) at 1.
  unfold R.v4092, N.v4092.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4093 (s : N.State) (i : N.Inputs) :
  R.v4093 (state s) (inputs i) = Zmod.unsigned (N.v4093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4093 s i)) at 1.
  unfold R.v4093, N.v4093.
  rewrite ?node_4092.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1784_nr_5F1794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1784_nr_5F1794 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4094 (s : N.State) (i : N.Inputs) :
  R.v4094 (state s) (inputs i) = Zmod.unsigned (N.v4094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4094 s i)) at 1.
  unfold R.v4094, N.v4094.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4095 (s : N.State) (i : N.Inputs) :
  R.v4095 (state s) (inputs i) = Zmod.unsigned (N.v4095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4095 s i)) at 1.
  unfold R.v4095, N.v4095.
  rewrite ?node_4094.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1785_nr_5F1795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1785_nr_5F1795 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4096 (s : N.State) (i : N.Inputs) :
  R.v4096 (state s) (inputs i) = Zmod.unsigned (N.v4096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4096 s i)) at 1.
  unfold R.v4096, N.v4096.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4097 (s : N.State) (i : N.Inputs) :
  R.v4097 (state s) (inputs i) = Zmod.unsigned (N.v4097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4097 s i)) at 1.
  unfold R.v4097, N.v4097.
  rewrite ?node_4096.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1786_nr_5F1796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1786_nr_5F1796 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4098 (s : N.State) (i : N.Inputs) :
  R.v4098 (state s) (inputs i) = Zmod.unsigned (N.v4098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4098 s i)) at 1.
  unfold R.v4098, N.v4098.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4099 (s : N.State) (i : N.Inputs) :
  R.v4099 (state s) (inputs i) = Zmod.unsigned (N.v4099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4099 s i)) at 1.
  unfold R.v4099, N.v4099.
  rewrite ?node_4098.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1787_nr_5F1797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1787_nr_5F1797 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4100 (s : N.State) (i : N.Inputs) :
  R.v4100 (state s) (inputs i) = Zmod.unsigned (N.v4100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4100 s i)) at 1.
  unfold R.v4100, N.v4100.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4101 (s : N.State) (i : N.Inputs) :
  R.v4101 (state s) (inputs i) = Zmod.unsigned (N.v4101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4101 s i)) at 1.
  unfold R.v4101, N.v4101.
  rewrite ?node_4100.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1788_nr_5F1798.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1788_nr_5F1798 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4102 (s : N.State) (i : N.Inputs) :
  R.v4102 (state s) (inputs i) = Zmod.unsigned (N.v4102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4102 s i)) at 1.
  unfold R.v4102, N.v4102.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4103 (s : N.State) (i : N.Inputs) :
  R.v4103 (state s) (inputs i) = Zmod.unsigned (N.v4103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4103 s i)) at 1.
  unfold R.v4103, N.v4103.
  rewrite ?node_4102.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1789_nr_5F1799.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1789_nr_5F1799 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4104 (s : N.State) (i : N.Inputs) :
  R.v4104 (state s) (inputs i) = Zmod.unsigned (N.v4104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4104 s i)) at 1.
  unfold R.v4104, N.v4104.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4105 (s : N.State) (i : N.Inputs) :
  R.v4105 (state s) (inputs i) = Zmod.unsigned (N.v4105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4105 s i)) at 1.
  unfold R.v4105, N.v4105.
  rewrite ?node_4104.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1790_nr_5F1800.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1790_nr_5F1800 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4106 (s : N.State) (i : N.Inputs) :
  R.v4106 (state s) (inputs i) = Zmod.unsigned (N.v4106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4106 s i)) at 1.
  unfold R.v4106, N.v4106.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4107 (s : N.State) (i : N.Inputs) :
  R.v4107 (state s) (inputs i) = Zmod.unsigned (N.v4107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4107 s i)) at 1.
  unfold R.v4107, N.v4107.
  rewrite ?node_4106.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1791_nr_5F1801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1791_nr_5F1801 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4108 (s : N.State) (i : N.Inputs) :
  R.v4108 (state s) (inputs i) = Zmod.unsigned (N.v4108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4108 s i)) at 1.
  unfold R.v4108, N.v4108.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4109 (s : N.State) (i : N.Inputs) :
  R.v4109 (state s) (inputs i) = Zmod.unsigned (N.v4109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4109 s i)) at 1.
  unfold R.v4109, N.v4109.
  rewrite ?node_4108.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1792_nr_5F1802.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1792_nr_5F1802 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4110 (s : N.State) (i : N.Inputs) :
  R.v4110 (state s) (inputs i) = Zmod.unsigned (N.v4110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4110 s i)) at 1.
  unfold R.v4110, N.v4110.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4111 (s : N.State) (i : N.Inputs) :
  R.v4111 (state s) (inputs i) = Zmod.unsigned (N.v4111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4111 s i)) at 1.
  unfold R.v4111, N.v4111.
  rewrite ?node_4110.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1793_nr_5F1803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1793_nr_5F1803 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4112 (s : N.State) (i : N.Inputs) :
  R.v4112 (state s) (inputs i) = Zmod.unsigned (N.v4112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4112 s i)) at 1.
  unfold R.v4112, N.v4112.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4113 (s : N.State) (i : N.Inputs) :
  R.v4113 (state s) (inputs i) = Zmod.unsigned (N.v4113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4113 s i)) at 1.
  unfold R.v4113, N.v4113.
  rewrite ?node_4112.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1794_nr_5F1804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1794_nr_5F1804 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4114 (s : N.State) (i : N.Inputs) :
  R.v4114 (state s) (inputs i) = Zmod.unsigned (N.v4114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4114 s i)) at 1.
  unfold R.v4114, N.v4114.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4115 (s : N.State) (i : N.Inputs) :
  R.v4115 (state s) (inputs i) = Zmod.unsigned (N.v4115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4115 s i)) at 1.
  unfold R.v4115, N.v4115.
  unfold R.v3021, N.v3021.
  rewrite ?node_4114.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4116 (s : N.State) (i : N.Inputs) :
  R.v4116 (state s) (inputs i) = Zmod.unsigned (N.v4116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4116 s i)) at 1.
  unfold R.v4116, N.v4116.
  rewrite ?node_4115.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1795_nr_5F1805.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1795_nr_5F1805 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4117 (s : N.State) (i : N.Inputs) :
  R.v4117 (state s) (inputs i) = Zmod.unsigned (N.v4117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4117 s i)) at 1.
  unfold R.v4117, N.v4117.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4118 (s : N.State) (i : N.Inputs) :
  R.v4118 (state s) (inputs i) = Zmod.unsigned (N.v4118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4118 s i)) at 1.
  unfold R.v4118, N.v4118.
  rewrite ?node_4117.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1796_nr_5F1806.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1796_nr_5F1806 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4119 (s : N.State) (i : N.Inputs) :
  R.v4119 (state s) (inputs i) = Zmod.unsigned (N.v4119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4119 s i)) at 1.
  unfold R.v4119, N.v4119.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4120 (s : N.State) (i : N.Inputs) :
  R.v4120 (state s) (inputs i) = Zmod.unsigned (N.v4120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4120 s i)) at 1.
  unfold R.v4120, N.v4120.
  rewrite ?node_4119.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1797_nr_5F1807.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1797_nr_5F1807 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4121 (s : N.State) (i : N.Inputs) :
  R.v4121 (state s) (inputs i) = Zmod.unsigned (N.v4121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4121 s i)) at 1.
  unfold R.v4121, N.v4121.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4122 (s : N.State) (i : N.Inputs) :
  R.v4122 (state s) (inputs i) = Zmod.unsigned (N.v4122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4122 s i)) at 1.
  unfold R.v4122, N.v4122.
  rewrite ?node_4121.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1798_nr_5F1808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1798_nr_5F1808 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4123 (s : N.State) (i : N.Inputs) :
  R.v4123 (state s) (inputs i) = Zmod.unsigned (N.v4123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4123 s i)) at 1.
  unfold R.v4123, N.v4123.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4124 (s : N.State) (i : N.Inputs) :
  R.v4124 (state s) (inputs i) = Zmod.unsigned (N.v4124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4124 s i)) at 1.
  unfold R.v4124, N.v4124.
  rewrite ?node_4123.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1799_nr_5F1809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1799_nr_5F1809 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4125 (s : N.State) (i : N.Inputs) :
  R.v4125 (state s) (inputs i) = Zmod.unsigned (N.v4125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4125 s i)) at 1.
  unfold R.v4125, N.v4125.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4126 (s : N.State) (i : N.Inputs) :
  R.v4126 (state s) (inputs i) = Zmod.unsigned (N.v4126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4126 s i)) at 1.
  unfold R.v4126, N.v4126.
  rewrite ?node_4125.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1800_nr_5F1810.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1800_nr_5F1810 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4127 (s : N.State) (i : N.Inputs) :
  R.v4127 (state s) (inputs i) = Zmod.unsigned (N.v4127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4127 s i)) at 1.
  unfold R.v4127, N.v4127.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4128 (s : N.State) (i : N.Inputs) :
  R.v4128 (state s) (inputs i) = Zmod.unsigned (N.v4128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4128 s i)) at 1.
  unfold R.v4128, N.v4128.
  rewrite ?node_4127.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1801_nr_5F1811.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1801_nr_5F1811 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4129 (s : N.State) (i : N.Inputs) :
  R.v4129 (state s) (inputs i) = Zmod.unsigned (N.v4129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4129 s i)) at 1.
  unfold R.v4129, N.v4129.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4130 (s : N.State) (i : N.Inputs) :
  R.v4130 (state s) (inputs i) = Zmod.unsigned (N.v4130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4130 s i)) at 1.
  unfold R.v4130, N.v4130.
  rewrite ?node_4129.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1802_nr_5F1812.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1802_nr_5F1812 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4131 (s : N.State) (i : N.Inputs) :
  R.v4131 (state s) (inputs i) = Zmod.unsigned (N.v4131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4131 s i)) at 1.
  unfold R.v4131, N.v4131.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4132 (s : N.State) (i : N.Inputs) :
  R.v4132 (state s) (inputs i) = Zmod.unsigned (N.v4132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4132 s i)) at 1.
  unfold R.v4132, N.v4132.
  rewrite ?node_4131.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1803_nr_5F1813.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1803_nr_5F1813 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4133 (s : N.State) (i : N.Inputs) :
  R.v4133 (state s) (inputs i) = Zmod.unsigned (N.v4133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4133 s i)) at 1.
  unfold R.v4133, N.v4133.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4134 (s : N.State) (i : N.Inputs) :
  R.v4134 (state s) (inputs i) = Zmod.unsigned (N.v4134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4134 s i)) at 1.
  unfold R.v4134, N.v4134.
  rewrite ?node_4133.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1804_nr_5F1814.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1804_nr_5F1814 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4135 (s : N.State) (i : N.Inputs) :
  R.v4135 (state s) (inputs i) = Zmod.unsigned (N.v4135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4135 s i)) at 1.
  unfold R.v4135, N.v4135.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4136 (s : N.State) (i : N.Inputs) :
  R.v4136 (state s) (inputs i) = Zmod.unsigned (N.v4136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4136 s i)) at 1.
  unfold R.v4136, N.v4136.
  rewrite ?node_4135.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1805_nr_5F1815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1805_nr_5F1815 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4137 (s : N.State) (i : N.Inputs) :
  R.v4137 (state s) (inputs i) = Zmod.unsigned (N.v4137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4137 s i)) at 1.
  unfold R.v4137, N.v4137.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4138 (s : N.State) (i : N.Inputs) :
  R.v4138 (state s) (inputs i) = Zmod.unsigned (N.v4138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4138 s i)) at 1.
  unfold R.v4138, N.v4138.
  rewrite ?node_4137.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1806_nr_5F1816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1806_nr_5F1816 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4139 (s : N.State) (i : N.Inputs) :
  R.v4139 (state s) (inputs i) = Zmod.unsigned (N.v4139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4139 s i)) at 1.
  unfold R.v4139, N.v4139.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4140 (s : N.State) (i : N.Inputs) :
  R.v4140 (state s) (inputs i) = Zmod.unsigned (N.v4140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4140 s i)) at 1.
  unfold R.v4140, N.v4140.
  rewrite ?node_4139.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1807_nr_5F1817.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1807_nr_5F1817 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4141 (s : N.State) (i : N.Inputs) :
  R.v4141 (state s) (inputs i) = Zmod.unsigned (N.v4141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4141 s i)) at 1.
  unfold R.v4141, N.v4141.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4142 (s : N.State) (i : N.Inputs) :
  R.v4142 (state s) (inputs i) = Zmod.unsigned (N.v4142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4142 s i)) at 1.
  unfold R.v4142, N.v4142.
  rewrite ?node_4141.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1808_nr_5F1818.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1808_nr_5F1818 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4143 (s : N.State) (i : N.Inputs) :
  R.v4143 (state s) (inputs i) = Zmod.unsigned (N.v4143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4143 s i)) at 1.
  unfold R.v4143, N.v4143.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4144 (s : N.State) (i : N.Inputs) :
  R.v4144 (state s) (inputs i) = Zmod.unsigned (N.v4144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4144 s i)) at 1.
  unfold R.v4144, N.v4144.
  rewrite ?node_4143.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1809_nr_5F1819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1809_nr_5F1819 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4145 (s : N.State) (i : N.Inputs) :
  R.v4145 (state s) (inputs i) = Zmod.unsigned (N.v4145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4145 s i)) at 1.
  unfold R.v4145, N.v4145.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4146 (s : N.State) (i : N.Inputs) :
  R.v4146 (state s) (inputs i) = Zmod.unsigned (N.v4146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4146 s i)) at 1.
  unfold R.v4146, N.v4146.
  rewrite ?node_4145.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1810_nr_5F1820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1810_nr_5F1820 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4147 (s : N.State) (i : N.Inputs) :
  R.v4147 (state s) (inputs i) = Zmod.unsigned (N.v4147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4147 s i)) at 1.
  unfold R.v4147, N.v4147.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4148 (s : N.State) (i : N.Inputs) :
  R.v4148 (state s) (inputs i) = Zmod.unsigned (N.v4148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4148 s i)) at 1.
  unfold R.v4148, N.v4148.
  rewrite ?node_4147.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1811_nr_5F1821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1811_nr_5F1821 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4149 (s : N.State) (i : N.Inputs) :
  R.v4149 (state s) (inputs i) = Zmod.unsigned (N.v4149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4149 s i)) at 1.
  unfold R.v4149, N.v4149.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4150 (s : N.State) (i : N.Inputs) :
  R.v4150 (state s) (inputs i) = Zmod.unsigned (N.v4150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4150 s i)) at 1.
  unfold R.v4150, N.v4150.
  rewrite ?node_4149.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1812_nr_5F1822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1812_nr_5F1822 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4151 (s : N.State) (i : N.Inputs) :
  R.v4151 (state s) (inputs i) = Zmod.unsigned (N.v4151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4151 s i)) at 1.
  unfold R.v4151, N.v4151.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4152 (s : N.State) (i : N.Inputs) :
  R.v4152 (state s) (inputs i) = Zmod.unsigned (N.v4152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4152 s i)) at 1.
  unfold R.v4152, N.v4152.
  rewrite ?node_4151.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1813_nr_5F1823.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1813_nr_5F1823 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4153 (s : N.State) (i : N.Inputs) :
  R.v4153 (state s) (inputs i) = Zmod.unsigned (N.v4153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4153 s i)) at 1.
  unfold R.v4153, N.v4153.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4154 (s : N.State) (i : N.Inputs) :
  R.v4154 (state s) (inputs i) = Zmod.unsigned (N.v4154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4154 s i)) at 1.
  unfold R.v4154, N.v4154.
  rewrite ?node_4153.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1814_nr_5F1824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1814_nr_5F1824 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4155 (s : N.State) (i : N.Inputs) :
  R.v4155 (state s) (inputs i) = Zmod.unsigned (N.v4155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4155 s i)) at 1.
  unfold R.v4155, N.v4155.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4156 (s : N.State) (i : N.Inputs) :
  R.v4156 (state s) (inputs i) = Zmod.unsigned (N.v4156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4156 s i)) at 1.
  unfold R.v4156, N.v4156.
  rewrite ?node_4155.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1815_nr_5F1825.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1815_nr_5F1825 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4157 (s : N.State) (i : N.Inputs) :
  R.v4157 (state s) (inputs i) = Zmod.unsigned (N.v4157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4157 s i)) at 1.
  unfold R.v4157, N.v4157.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4158 (s : N.State) (i : N.Inputs) :
  R.v4158 (state s) (inputs i) = Zmod.unsigned (N.v4158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4158 s i)) at 1.
  unfold R.v4158, N.v4158.
  rewrite ?node_4157.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1816_nr_5F1826.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1816_nr_5F1826 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4159 (s : N.State) (i : N.Inputs) :
  R.v4159 (state s) (inputs i) = Zmod.unsigned (N.v4159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4159 s i)) at 1.
  unfold R.v4159, N.v4159.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4160 (s : N.State) (i : N.Inputs) :
  R.v4160 (state s) (inputs i) = Zmod.unsigned (N.v4160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4160 s i)) at 1.
  unfold R.v4160, N.v4160.
  rewrite ?node_4159.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1817_nr_5F1828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1817_nr_5F1828 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4161 (s : N.State) (i : N.Inputs) :
  R.v4161 (state s) (inputs i) = Zmod.unsigned (N.v4161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4161 s i)) at 1.
  unfold R.v4161, N.v4161.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4162 (s : N.State) (i : N.Inputs) :
  R.v4162 (state s) (inputs i) = Zmod.unsigned (N.v4162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4162 s i)) at 1.
  unfold R.v4162, N.v4162.
  rewrite ?node_4161.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1818_nr_5F1829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1818_nr_5F1829 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4163 (s : N.State) (i : N.Inputs) :
  R.v4163 (state s) (inputs i) = Zmod.unsigned (N.v4163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4163 s i)) at 1.
  unfold R.v4163, N.v4163.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4164 (s : N.State) (i : N.Inputs) :
  R.v4164 (state s) (inputs i) = Zmod.unsigned (N.v4164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4164 s i)) at 1.
  unfold R.v4164, N.v4164.
  rewrite ?node_4163.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1819_nr_5F1830.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1819_nr_5F1830 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4165 (s : N.State) (i : N.Inputs) :
  R.v4165 (state s) (inputs i) = Zmod.unsigned (N.v4165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4165 s i)) at 1.
  unfold R.v4165, N.v4165.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4166 (s : N.State) (i : N.Inputs) :
  R.v4166 (state s) (inputs i) = Zmod.unsigned (N.v4166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4166 s i)) at 1.
  unfold R.v4166, N.v4166.
  rewrite ?node_4165.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1820_nr_5F1831.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1820_nr_5F1831 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4167 (s : N.State) (i : N.Inputs) :
  R.v4167 (state s) (inputs i) = Zmod.unsigned (N.v4167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4167 s i)) at 1.
  unfold R.v4167, N.v4167.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4168 (s : N.State) (i : N.Inputs) :
  R.v4168 (state s) (inputs i) = Zmod.unsigned (N.v4168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4168 s i)) at 1.
  unfold R.v4168, N.v4168.
  rewrite ?node_4167.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1821_nr_5F1832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1821_nr_5F1832 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4169 (s : N.State) (i : N.Inputs) :
  R.v4169 (state s) (inputs i) = Zmod.unsigned (N.v4169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4169 s i)) at 1.
  unfold R.v4169, N.v4169.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4170 (s : N.State) (i : N.Inputs) :
  R.v4170 (state s) (inputs i) = Zmod.unsigned (N.v4170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4170 s i)) at 1.
  unfold R.v4170, N.v4170.
  rewrite ?node_4169.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1822_nr_5F1833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1822_nr_5F1833 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4171 (s : N.State) (i : N.Inputs) :
  R.v4171 (state s) (inputs i) = Zmod.unsigned (N.v4171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4171 s i)) at 1.
  unfold R.v4171, N.v4171.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4172 (s : N.State) (i : N.Inputs) :
  R.v4172 (state s) (inputs i) = Zmod.unsigned (N.v4172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4172 s i)) at 1.
  unfold R.v4172, N.v4172.
  rewrite ?node_4171.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1823_nr_5F1834.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1823_nr_5F1834 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4173 (s : N.State) (i : N.Inputs) :
  R.v4173 (state s) (inputs i) = Zmod.unsigned (N.v4173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4173 s i)) at 1.
  unfold R.v4173, N.v4173.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4174 (s : N.State) (i : N.Inputs) :
  R.v4174 (state s) (inputs i) = Zmod.unsigned (N.v4174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4174 s i)) at 1.
  unfold R.v4174, N.v4174.
  rewrite ?node_4173.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1824_nr_5F1835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1824_nr_5F1835 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4175 (s : N.State) (i : N.Inputs) :
  R.v4175 (state s) (inputs i) = Zmod.unsigned (N.v4175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4175 s i)) at 1.
  unfold R.v4175, N.v4175.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4176 (s : N.State) (i : N.Inputs) :
  R.v4176 (state s) (inputs i) = Zmod.unsigned (N.v4176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4176 s i)) at 1.
  unfold R.v4176, N.v4176.
  rewrite ?node_4175.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1825_nr_5F1836.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1825_nr_5F1836 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4177 (s : N.State) (i : N.Inputs) :
  R.v4177 (state s) (inputs i) = Zmod.unsigned (N.v4177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4177 s i)) at 1.
  unfold R.v4177, N.v4177.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4178 (s : N.State) (i : N.Inputs) :
  R.v4178 (state s) (inputs i) = Zmod.unsigned (N.v4178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4178 s i)) at 1.
  unfold R.v4178, N.v4178.
  rewrite ?node_4177.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1826_nr_5F1837.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1826_nr_5F1837 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4179 (s : N.State) (i : N.Inputs) :
  R.v4179 (state s) (inputs i) = Zmod.unsigned (N.v4179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4179 s i)) at 1.
  unfold R.v4179, N.v4179.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4180 (s : N.State) (i : N.Inputs) :
  R.v4180 (state s) (inputs i) = Zmod.unsigned (N.v4180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4180 s i)) at 1.
  unfold R.v4180, N.v4180.
  rewrite ?node_4179.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1827_nr_5F1838.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1827_nr_5F1838 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4181 (s : N.State) (i : N.Inputs) :
  R.v4181 (state s) (inputs i) = Zmod.unsigned (N.v4181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4181 s i)) at 1.
  unfold R.v4181, N.v4181.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4182 (s : N.State) (i : N.Inputs) :
  R.v4182 (state s) (inputs i) = Zmod.unsigned (N.v4182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4182 s i)) at 1.
  unfold R.v4182, N.v4182.
  rewrite ?node_4181.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1828_nr_5F1839.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1828_nr_5F1839 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4183 (s : N.State) (i : N.Inputs) :
  R.v4183 (state s) (inputs i) = Zmod.unsigned (N.v4183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4183 s i)) at 1.
  unfold R.v4183, N.v4183.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4184 (s : N.State) (i : N.Inputs) :
  R.v4184 (state s) (inputs i) = Zmod.unsigned (N.v4184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4184 s i)) at 1.
  unfold R.v4184, N.v4184.
  rewrite ?node_4183.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1829_nr_5F1840.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1829_nr_5F1840 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4185 (s : N.State) (i : N.Inputs) :
  R.v4185 (state s) (inputs i) = Zmod.unsigned (N.v4185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4185 s i)) at 1.
  unfold R.v4185, N.v4185.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4186 (s : N.State) (i : N.Inputs) :
  R.v4186 (state s) (inputs i) = Zmod.unsigned (N.v4186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4186 s i)) at 1.
  unfold R.v4186, N.v4186.
  rewrite ?node_4185.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1830_nr_5F1841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1830_nr_5F1841 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4187 (s : N.State) (i : N.Inputs) :
  R.v4187 (state s) (inputs i) = Zmod.unsigned (N.v4187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4187 s i)) at 1.
  unfold R.v4187, N.v4187.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4188 (s : N.State) (i : N.Inputs) :
  R.v4188 (state s) (inputs i) = Zmod.unsigned (N.v4188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4188 s i)) at 1.
  unfold R.v4188, N.v4188.
  rewrite ?node_4187.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1831_nr_5F1842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1831_nr_5F1842 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4189 (s : N.State) (i : N.Inputs) :
  R.v4189 (state s) (inputs i) = Zmod.unsigned (N.v4189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4189 s i)) at 1.
  unfold R.v4189, N.v4189.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4190 (s : N.State) (i : N.Inputs) :
  R.v4190 (state s) (inputs i) = Zmod.unsigned (N.v4190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4190 s i)) at 1.
  unfold R.v4190, N.v4190.
  rewrite ?node_4189.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1832_nr_5F1843.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1832_nr_5F1843 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4191 (s : N.State) (i : N.Inputs) :
  R.v4191 (state s) (inputs i) = Zmod.unsigned (N.v4191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4191 s i)) at 1.
  unfold R.v4191, N.v4191.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4192 (s : N.State) (i : N.Inputs) :
  R.v4192 (state s) (inputs i) = Zmod.unsigned (N.v4192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4192 s i)) at 1.
  unfold R.v4192, N.v4192.
  rewrite ?node_4191.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1833_nr_5F1844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1833_nr_5F1844 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4193 (s : N.State) (i : N.Inputs) :
  R.v4193 (state s) (inputs i) = Zmod.unsigned (N.v4193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4193 s i)) at 1.
  unfold R.v4193, N.v4193.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4194 (s : N.State) (i : N.Inputs) :
  R.v4194 (state s) (inputs i) = Zmod.unsigned (N.v4194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4194 s i)) at 1.
  unfold R.v4194, N.v4194.
  rewrite ?node_4193.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1834_nr_5F1845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1834_nr_5F1845 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4195 (s : N.State) (i : N.Inputs) :
  R.v4195 (state s) (inputs i) = Zmod.unsigned (N.v4195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4195 s i)) at 1.
  unfold R.v4195, N.v4195.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4196 (s : N.State) (i : N.Inputs) :
  R.v4196 (state s) (inputs i) = Zmod.unsigned (N.v4196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4196 s i)) at 1.
  unfold R.v4196, N.v4196.
  rewrite ?node_4195.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1835_nr_5F1846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1835_nr_5F1846 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4197 (s : N.State) (i : N.Inputs) :
  R.v4197 (state s) (inputs i) = Zmod.unsigned (N.v4197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4197 s i)) at 1.
  unfold R.v4197, N.v4197.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4198 (s : N.State) (i : N.Inputs) :
  R.v4198 (state s) (inputs i) = Zmod.unsigned (N.v4198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4198 s i)) at 1.
  unfold R.v4198, N.v4198.
  rewrite ?node_4197.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1836_nr_5F1847.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1836_nr_5F1847 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4199 (s : N.State) (i : N.Inputs) :
  R.v4199 (state s) (inputs i) = Zmod.unsigned (N.v4199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4199 s i)) at 1.
  unfold R.v4199, N.v4199.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4200 (s : N.State) (i : N.Inputs) :
  R.v4200 (state s) (inputs i) = Zmod.unsigned (N.v4200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4200 s i)) at 1.
  unfold R.v4200, N.v4200.
  rewrite ?node_4199.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1837_nr_5F1848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1837_nr_5F1848 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4201 (s : N.State) (i : N.Inputs) :
  R.v4201 (state s) (inputs i) = Zmod.unsigned (N.v4201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4201 s i)) at 1.
  unfold R.v4201, N.v4201.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4202 (s : N.State) (i : N.Inputs) :
  R.v4202 (state s) (inputs i) = Zmod.unsigned (N.v4202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4202 s i)) at 1.
  unfold R.v4202, N.v4202.
  unfold R.v3021, N.v3021.
  rewrite ?node_4201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4203 (s : N.State) (i : N.Inputs) :
  R.v4203 (state s) (inputs i) = Zmod.unsigned (N.v4203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4203 s i)) at 1.
  unfold R.v4203, N.v4203.
  rewrite ?node_4202.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1838_nr_5F1849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1838_nr_5F1849 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4204 (s : N.State) (i : N.Inputs) :
  R.v4204 (state s) (inputs i) = Zmod.unsigned (N.v4204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4204 s i)) at 1.
  unfold R.v4204, N.v4204.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4205 (s : N.State) (i : N.Inputs) :
  R.v4205 (state s) (inputs i) = Zmod.unsigned (N.v4205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4205 s i)) at 1.
  unfold R.v4205, N.v4205.
  rewrite ?node_4204.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1839_nr_5F1850.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1839_nr_5F1850 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4206 (s : N.State) (i : N.Inputs) :
  R.v4206 (state s) (inputs i) = Zmod.unsigned (N.v4206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4206 s i)) at 1.
  unfold R.v4206, N.v4206.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4207 (s : N.State) (i : N.Inputs) :
  R.v4207 (state s) (inputs i) = Zmod.unsigned (N.v4207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4207 s i)) at 1.
  unfold R.v4207, N.v4207.
  rewrite ?node_4206.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1840_nr_5F1851.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1840_nr_5F1851 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4208 (s : N.State) (i : N.Inputs) :
  R.v4208 (state s) (inputs i) = Zmod.unsigned (N.v4208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4208 s i)) at 1.
  unfold R.v4208, N.v4208.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4209 (s : N.State) (i : N.Inputs) :
  R.v4209 (state s) (inputs i) = Zmod.unsigned (N.v4209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4209 s i)) at 1.
  unfold R.v4209, N.v4209.
  rewrite ?node_4208.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1841_nr_5F1852.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1841_nr_5F1852 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4210 (s : N.State) (i : N.Inputs) :
  R.v4210 (state s) (inputs i) = Zmod.unsigned (N.v4210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4210 s i)) at 1.
  unfold R.v4210, N.v4210.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4211 (s : N.State) (i : N.Inputs) :
  R.v4211 (state s) (inputs i) = Zmod.unsigned (N.v4211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4211 s i)) at 1.
  unfold R.v4211, N.v4211.
  rewrite ?node_4210.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1842_nr_5F1853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1842_nr_5F1853 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4212 (s : N.State) (i : N.Inputs) :
  R.v4212 (state s) (inputs i) = Zmod.unsigned (N.v4212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4212 s i)) at 1.
  unfold R.v4212, N.v4212.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4213 (s : N.State) (i : N.Inputs) :
  R.v4213 (state s) (inputs i) = Zmod.unsigned (N.v4213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4213 s i)) at 1.
  unfold R.v4213, N.v4213.
  rewrite ?node_4212.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1843_nr_5F1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1843_nr_5F1854 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4214 (s : N.State) (i : N.Inputs) :
  R.v4214 (state s) (inputs i) = Zmod.unsigned (N.v4214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4214 s i)) at 1.
  unfold R.v4214, N.v4214.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4215 (s : N.State) (i : N.Inputs) :
  R.v4215 (state s) (inputs i) = Zmod.unsigned (N.v4215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4215 s i)) at 1.
  unfold R.v4215, N.v4215.
  rewrite ?node_4214.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1844_nr_5F1855.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1844_nr_5F1855 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4216 (s : N.State) (i : N.Inputs) :
  R.v4216 (state s) (inputs i) = Zmod.unsigned (N.v4216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4216 s i)) at 1.
  unfold R.v4216, N.v4216.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4217 (s : N.State) (i : N.Inputs) :
  R.v4217 (state s) (inputs i) = Zmod.unsigned (N.v4217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4217 s i)) at 1.
  unfold R.v4217, N.v4217.
  rewrite ?node_4216.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1845_nr_5F1856.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1845_nr_5F1856 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4218 (s : N.State) (i : N.Inputs) :
  R.v4218 (state s) (inputs i) = Zmod.unsigned (N.v4218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4218 s i)) at 1.
  unfold R.v4218, N.v4218.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4219 (s : N.State) (i : N.Inputs) :
  R.v4219 (state s) (inputs i) = Zmod.unsigned (N.v4219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4219 s i)) at 1.
  unfold R.v4219, N.v4219.
  rewrite ?node_4218.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1846_nr_5F1857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1846_nr_5F1857 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4220 (s : N.State) (i : N.Inputs) :
  R.v4220 (state s) (inputs i) = Zmod.unsigned (N.v4220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4220 s i)) at 1.
  unfold R.v4220, N.v4220.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4221 (s : N.State) (i : N.Inputs) :
  R.v4221 (state s) (inputs i) = Zmod.unsigned (N.v4221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4221 s i)) at 1.
  unfold R.v4221, N.v4221.
  rewrite ?node_4220.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1847_nr_5F1858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1847_nr_5F1858 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4222 (s : N.State) (i : N.Inputs) :
  R.v4222 (state s) (inputs i) = Zmod.unsigned (N.v4222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4222 s i)) at 1.
  unfold R.v4222, N.v4222.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4223 (s : N.State) (i : N.Inputs) :
  R.v4223 (state s) (inputs i) = Zmod.unsigned (N.v4223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4223 s i)) at 1.
  unfold R.v4223, N.v4223.
  rewrite ?node_4222.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1848_nr_5F1859.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1848_nr_5F1859 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4224 (s : N.State) (i : N.Inputs) :
  R.v4224 (state s) (inputs i) = Zmod.unsigned (N.v4224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4224 s i)) at 1.
  unfold R.v4224, N.v4224.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4225 (s : N.State) (i : N.Inputs) :
  R.v4225 (state s) (inputs i) = Zmod.unsigned (N.v4225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4225 s i)) at 1.
  unfold R.v4225, N.v4225.
  rewrite ?node_4224.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1849_nr_5F1860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1849_nr_5F1860 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4226 (s : N.State) (i : N.Inputs) :
  R.v4226 (state s) (inputs i) = Zmod.unsigned (N.v4226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4226 s i)) at 1.
  unfold R.v4226, N.v4226.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4227 (s : N.State) (i : N.Inputs) :
  R.v4227 (state s) (inputs i) = Zmod.unsigned (N.v4227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4227 s i)) at 1.
  unfold R.v4227, N.v4227.
  rewrite ?node_4226.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1850_nr_5F1861.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1850_nr_5F1861 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4228 (s : N.State) (i : N.Inputs) :
  R.v4228 (state s) (inputs i) = Zmod.unsigned (N.v4228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4228 s i)) at 1.
  unfold R.v4228, N.v4228.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4229 (s : N.State) (i : N.Inputs) :
  R.v4229 (state s) (inputs i) = Zmod.unsigned (N.v4229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4229 s i)) at 1.
  unfold R.v4229, N.v4229.
  rewrite ?node_4228.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1851_nr_5F1862.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1851_nr_5F1862 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4230 (s : N.State) (i : N.Inputs) :
  R.v4230 (state s) (inputs i) = Zmod.unsigned (N.v4230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4230 s i)) at 1.
  unfold R.v4230, N.v4230.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4231 (s : N.State) (i : N.Inputs) :
  R.v4231 (state s) (inputs i) = Zmod.unsigned (N.v4231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4231 s i)) at 1.
  unfold R.v4231, N.v4231.
  rewrite ?node_4230.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1852_nr_5F1863.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1852_nr_5F1863 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4232 (s : N.State) (i : N.Inputs) :
  R.v4232 (state s) (inputs i) = Zmod.unsigned (N.v4232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4232 s i)) at 1.
  unfold R.v4232, N.v4232.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4233 (s : N.State) (i : N.Inputs) :
  R.v4233 (state s) (inputs i) = Zmod.unsigned (N.v4233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4233 s i)) at 1.
  unfold R.v4233, N.v4233.
  rewrite ?node_4232.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1853_nr_5F1864.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1853_nr_5F1864 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4234 (s : N.State) (i : N.Inputs) :
  R.v4234 (state s) (inputs i) = Zmod.unsigned (N.v4234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4234 s i)) at 1.
  unfold R.v4234, N.v4234.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4235 (s : N.State) (i : N.Inputs) :
  R.v4235 (state s) (inputs i) = Zmod.unsigned (N.v4235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4235 s i)) at 1.
  unfold R.v4235, N.v4235.
  rewrite ?node_4234.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1854_nr_5F1865.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1854_nr_5F1865 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4236 (s : N.State) (i : N.Inputs) :
  R.v4236 (state s) (inputs i) = Zmod.unsigned (N.v4236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4236 s i)) at 1.
  unfold R.v4236, N.v4236.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4237 (s : N.State) (i : N.Inputs) :
  R.v4237 (state s) (inputs i) = Zmod.unsigned (N.v4237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4237 s i)) at 1.
  unfold R.v4237, N.v4237.
  rewrite ?node_4236.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1855_nr_5F1866.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1855_nr_5F1866 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4238 (s : N.State) (i : N.Inputs) :
  R.v4238 (state s) (inputs i) = Zmod.unsigned (N.v4238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4238 s i)) at 1.
  unfold R.v4238, N.v4238.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4239 (s : N.State) (i : N.Inputs) :
  R.v4239 (state s) (inputs i) = Zmod.unsigned (N.v4239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4239 s i)) at 1.
  unfold R.v4239, N.v4239.
  rewrite ?node_4238.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1856_nr_5F1867.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1856_nr_5F1867 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4240 (s : N.State) (i : N.Inputs) :
  R.v4240 (state s) (inputs i) = Zmod.unsigned (N.v4240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4240 s i)) at 1.
  unfold R.v4240, N.v4240.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4241 (s : N.State) (i : N.Inputs) :
  R.v4241 (state s) (inputs i) = Zmod.unsigned (N.v4241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4241 s i)) at 1.
  unfold R.v4241, N.v4241.
  rewrite ?node_4240.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1857_nr_5F1868.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1857_nr_5F1868 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4242 (s : N.State) (i : N.Inputs) :
  R.v4242 (state s) (inputs i) = Zmod.unsigned (N.v4242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4242 s i)) at 1.
  unfold R.v4242, N.v4242.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4243 (s : N.State) (i : N.Inputs) :
  R.v4243 (state s) (inputs i) = Zmod.unsigned (N.v4243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4243 s i)) at 1.
  unfold R.v4243, N.v4243.
  rewrite ?node_4242.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1858_nr_5F1869.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1858_nr_5F1869 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4244 (s : N.State) (i : N.Inputs) :
  R.v4244 (state s) (inputs i) = Zmod.unsigned (N.v4244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4244 s i)) at 1.
  unfold R.v4244, N.v4244.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4245 (s : N.State) (i : N.Inputs) :
  R.v4245 (state s) (inputs i) = Zmod.unsigned (N.v4245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4245 s i)) at 1.
  unfold R.v4245, N.v4245.
  rewrite ?node_4244.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1859_nr_5F1871.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1859_nr_5F1871 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4246 (s : N.State) (i : N.Inputs) :
  R.v4246 (state s) (inputs i) = Zmod.unsigned (N.v4246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4246 s i)) at 1.
  unfold R.v4246, N.v4246.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4247 (s : N.State) (i : N.Inputs) :
  R.v4247 (state s) (inputs i) = Zmod.unsigned (N.v4247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4247 s i)) at 1.
  unfold R.v4247, N.v4247.
  rewrite ?node_4246.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1860_nr_5F1872.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1860_nr_5F1872 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4248 (s : N.State) (i : N.Inputs) :
  R.v4248 (state s) (inputs i) = Zmod.unsigned (N.v4248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4248 s i)) at 1.
  unfold R.v4248, N.v4248.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4249 (s : N.State) (i : N.Inputs) :
  R.v4249 (state s) (inputs i) = Zmod.unsigned (N.v4249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4249 s i)) at 1.
  unfold R.v4249, N.v4249.
  rewrite ?node_4248.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1861_nr_5F1873.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1861_nr_5F1873 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4250 (s : N.State) (i : N.Inputs) :
  R.v4250 (state s) (inputs i) = Zmod.unsigned (N.v4250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4250 s i)) at 1.
  unfold R.v4250, N.v4250.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4251 (s : N.State) (i : N.Inputs) :
  R.v4251 (state s) (inputs i) = Zmod.unsigned (N.v4251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4251 s i)) at 1.
  unfold R.v4251, N.v4251.
  rewrite ?node_4250.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1862_nr_5F1874.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1862_nr_5F1874 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4252 (s : N.State) (i : N.Inputs) :
  R.v4252 (state s) (inputs i) = Zmod.unsigned (N.v4252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4252 s i)) at 1.
  unfold R.v4252, N.v4252.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4253 (s : N.State) (i : N.Inputs) :
  R.v4253 (state s) (inputs i) = Zmod.unsigned (N.v4253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4253 s i)) at 1.
  unfold R.v4253, N.v4253.
  rewrite ?node_4252.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1863_nr_5F1875.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1863_nr_5F1875 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4254 (s : N.State) (i : N.Inputs) :
  R.v4254 (state s) (inputs i) = Zmod.unsigned (N.v4254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4254 s i)) at 1.
  unfold R.v4254, N.v4254.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4255 (s : N.State) (i : N.Inputs) :
  R.v4255 (state s) (inputs i) = Zmod.unsigned (N.v4255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4255 s i)) at 1.
  unfold R.v4255, N.v4255.
  rewrite ?node_4254.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1864_nr_5F1876.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1864_nr_5F1876 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4256 (s : N.State) (i : N.Inputs) :
  R.v4256 (state s) (inputs i) = Zmod.unsigned (N.v4256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4256 s i)) at 1.
  unfold R.v4256, N.v4256.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4257 (s : N.State) (i : N.Inputs) :
  R.v4257 (state s) (inputs i) = Zmod.unsigned (N.v4257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4257 s i)) at 1.
  unfold R.v4257, N.v4257.
  rewrite ?node_4256.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1865_nr_5F1877.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1865_nr_5F1877 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4258 (s : N.State) (i : N.Inputs) :
  R.v4258 (state s) (inputs i) = Zmod.unsigned (N.v4258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4258 s i)) at 1.
  unfold R.v4258, N.v4258.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4259 (s : N.State) (i : N.Inputs) :
  R.v4259 (state s) (inputs i) = Zmod.unsigned (N.v4259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4259 s i)) at 1.
  unfold R.v4259, N.v4259.
  rewrite ?node_4258.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1866_nr_5F1878.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1866_nr_5F1878 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4260 (s : N.State) (i : N.Inputs) :
  R.v4260 (state s) (inputs i) = Zmod.unsigned (N.v4260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4260 s i)) at 1.
  unfold R.v4260, N.v4260.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4261 (s : N.State) (i : N.Inputs) :
  R.v4261 (state s) (inputs i) = Zmod.unsigned (N.v4261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4261 s i)) at 1.
  unfold R.v4261, N.v4261.
  rewrite ?node_4260.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1867_nr_5F1879.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1867_nr_5F1879 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4262 (s : N.State) (i : N.Inputs) :
  R.v4262 (state s) (inputs i) = Zmod.unsigned (N.v4262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4262 s i)) at 1.
  unfold R.v4262, N.v4262.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4263 (s : N.State) (i : N.Inputs) :
  R.v4263 (state s) (inputs i) = Zmod.unsigned (N.v4263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4263 s i)) at 1.
  unfold R.v4263, N.v4263.
  rewrite ?node_4262.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1868_nr_5F1880.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1868_nr_5F1880 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4264 (s : N.State) (i : N.Inputs) :
  R.v4264 (state s) (inputs i) = Zmod.unsigned (N.v4264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4264 s i)) at 1.
  unfold R.v4264, N.v4264.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4265 (s : N.State) (i : N.Inputs) :
  R.v4265 (state s) (inputs i) = Zmod.unsigned (N.v4265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4265 s i)) at 1.
  unfold R.v4265, N.v4265.
  rewrite ?node_4264.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1869_nr_5F1881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1869_nr_5F1881 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4266 (s : N.State) (i : N.Inputs) :
  R.v4266 (state s) (inputs i) = Zmod.unsigned (N.v4266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4266 s i)) at 1.
  unfold R.v4266, N.v4266.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4267 (s : N.State) (i : N.Inputs) :
  R.v4267 (state s) (inputs i) = Zmod.unsigned (N.v4267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4267 s i)) at 1.
  unfold R.v4267, N.v4267.
  rewrite ?node_4266.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1870_nr_5F1882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1870_nr_5F1882 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4268 (s : N.State) (i : N.Inputs) :
  R.v4268 (state s) (inputs i) = Zmod.unsigned (N.v4268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4268 s i)) at 1.
  unfold R.v4268, N.v4268.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4269 (s : N.State) (i : N.Inputs) :
  R.v4269 (state s) (inputs i) = Zmod.unsigned (N.v4269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4269 s i)) at 1.
  unfold R.v4269, N.v4269.
  rewrite ?node_4268.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1871_nr_5F1883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1871_nr_5F1883 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4270 (s : N.State) (i : N.Inputs) :
  R.v4270 (state s) (inputs i) = Zmod.unsigned (N.v4270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4270 s i)) at 1.
  unfold R.v4270, N.v4270.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4271 (s : N.State) (i : N.Inputs) :
  R.v4271 (state s) (inputs i) = Zmod.unsigned (N.v4271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4271 s i)) at 1.
  unfold R.v4271, N.v4271.
  rewrite ?node_4270.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1872_nr_5F1884.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1872_nr_5F1884 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4272 (s : N.State) (i : N.Inputs) :
  R.v4272 (state s) (inputs i) = Zmod.unsigned (N.v4272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4272 s i)) at 1.
  unfold R.v4272, N.v4272.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4273 (s : N.State) (i : N.Inputs) :
  R.v4273 (state s) (inputs i) = Zmod.unsigned (N.v4273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4273 s i)) at 1.
  unfold R.v4273, N.v4273.
  rewrite ?node_4272.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1873_nr_5F1885.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1873_nr_5F1885 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4274 (s : N.State) (i : N.Inputs) :
  R.v4274 (state s) (inputs i) = Zmod.unsigned (N.v4274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4274 s i)) at 1.
  unfold R.v4274, N.v4274.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4275 (s : N.State) (i : N.Inputs) :
  R.v4275 (state s) (inputs i) = Zmod.unsigned (N.v4275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4275 s i)) at 1.
  unfold R.v4275, N.v4275.
  rewrite ?node_4274.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1874_nr_5F1886.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1874_nr_5F1886 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4276 (s : N.State) (i : N.Inputs) :
  R.v4276 (state s) (inputs i) = Zmod.unsigned (N.v4276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4276 s i)) at 1.
  unfold R.v4276, N.v4276.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4277 (s : N.State) (i : N.Inputs) :
  R.v4277 (state s) (inputs i) = Zmod.unsigned (N.v4277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4277 s i)) at 1.
  unfold R.v4277, N.v4277.
  rewrite ?node_4276.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1875_nr_5F1887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1875_nr_5F1887 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4278 (s : N.State) (i : N.Inputs) :
  R.v4278 (state s) (inputs i) = Zmod.unsigned (N.v4278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4278 s i)) at 1.
  unfold R.v4278, N.v4278.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4279 (s : N.State) (i : N.Inputs) :
  R.v4279 (state s) (inputs i) = Zmod.unsigned (N.v4279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4279 s i)) at 1.
  unfold R.v4279, N.v4279.
  rewrite ?node_4278.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1876_nr_5F1888.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1876_nr_5F1888 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4280 (s : N.State) (i : N.Inputs) :
  R.v4280 (state s) (inputs i) = Zmod.unsigned (N.v4280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4280 s i)) at 1.
  unfold R.v4280, N.v4280.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4281 (s : N.State) (i : N.Inputs) :
  R.v4281 (state s) (inputs i) = Zmod.unsigned (N.v4281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4281 s i)) at 1.
  unfold R.v4281, N.v4281.
  rewrite ?node_4280.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1877_nr_5F1889.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1877_nr_5F1889 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4282 (s : N.State) (i : N.Inputs) :
  R.v4282 (state s) (inputs i) = Zmod.unsigned (N.v4282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4282 s i)) at 1.
  unfold R.v4282, N.v4282.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4283 (s : N.State) (i : N.Inputs) :
  R.v4283 (state s) (inputs i) = Zmod.unsigned (N.v4283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4283 s i)) at 1.
  unfold R.v4283, N.v4283.
  rewrite ?node_4282.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1878_nr_5F1890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1878_nr_5F1890 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4284 (s : N.State) (i : N.Inputs) :
  R.v4284 (state s) (inputs i) = Zmod.unsigned (N.v4284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4284 s i)) at 1.
  unfold R.v4284, N.v4284.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4285 (s : N.State) (i : N.Inputs) :
  R.v4285 (state s) (inputs i) = Zmod.unsigned (N.v4285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4285 s i)) at 1.
  unfold R.v4285, N.v4285.
  unfold R.v3021, N.v3021.
  rewrite ?node_4284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4286 (s : N.State) (i : N.Inputs) :
  R.v4286 (state s) (inputs i) = Zmod.unsigned (N.v4286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4286 s i)) at 1.
  unfold R.v4286, N.v4286.
  rewrite ?node_4285.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1879_nr_5F1891.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1879_nr_5F1891 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4287 (s : N.State) (i : N.Inputs) :
  R.v4287 (state s) (inputs i) = Zmod.unsigned (N.v4287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4287 s i)) at 1.
  unfold R.v4287, N.v4287.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4288 (s : N.State) (i : N.Inputs) :
  R.v4288 (state s) (inputs i) = Zmod.unsigned (N.v4288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4288 s i)) at 1.
  unfold R.v4288, N.v4288.
  rewrite ?node_4287.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1880_nr_5F1892.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1880_nr_5F1892 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4289 (s : N.State) (i : N.Inputs) :
  R.v4289 (state s) (inputs i) = Zmod.unsigned (N.v4289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4289 s i)) at 1.
  unfold R.v4289, N.v4289.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4290 (s : N.State) (i : N.Inputs) :
  R.v4290 (state s) (inputs i) = Zmod.unsigned (N.v4290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4290 s i)) at 1.
  unfold R.v4290, N.v4290.
  rewrite ?node_4289.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1881_nr_5F1893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1881_nr_5F1893 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4291 (s : N.State) (i : N.Inputs) :
  R.v4291 (state s) (inputs i) = Zmod.unsigned (N.v4291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4291 s i)) at 1.
  unfold R.v4291, N.v4291.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4292 (s : N.State) (i : N.Inputs) :
  R.v4292 (state s) (inputs i) = Zmod.unsigned (N.v4292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4292 s i)) at 1.
  unfold R.v4292, N.v4292.
  rewrite ?node_4291.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1882_nr_5F1894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1882_nr_5F1894 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4293 (s : N.State) (i : N.Inputs) :
  R.v4293 (state s) (inputs i) = Zmod.unsigned (N.v4293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4293 s i)) at 1.
  unfold R.v4293, N.v4293.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4294 (s : N.State) (i : N.Inputs) :
  R.v4294 (state s) (inputs i) = Zmod.unsigned (N.v4294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4294 s i)) at 1.
  unfold R.v4294, N.v4294.
  rewrite ?node_4293.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1883_nr_5F1895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1883_nr_5F1895 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4295 (s : N.State) (i : N.Inputs) :
  R.v4295 (state s) (inputs i) = Zmod.unsigned (N.v4295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4295 s i)) at 1.
  unfold R.v4295, N.v4295.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4296 (s : N.State) (i : N.Inputs) :
  R.v4296 (state s) (inputs i) = Zmod.unsigned (N.v4296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4296 s i)) at 1.
  unfold R.v4296, N.v4296.
  rewrite ?node_4295.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1884_nr_5F1896.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1884_nr_5F1896 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4297 (s : N.State) (i : N.Inputs) :
  R.v4297 (state s) (inputs i) = Zmod.unsigned (N.v4297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4297 s i)) at 1.
  unfold R.v4297, N.v4297.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4298 (s : N.State) (i : N.Inputs) :
  R.v4298 (state s) (inputs i) = Zmod.unsigned (N.v4298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4298 s i)) at 1.
  unfold R.v4298, N.v4298.
  rewrite ?node_4297.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1885_nr_5F1897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1885_nr_5F1897 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4299 (s : N.State) (i : N.Inputs) :
  R.v4299 (state s) (inputs i) = Zmod.unsigned (N.v4299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4299 s i)) at 1.
  unfold R.v4299, N.v4299.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4300 (s : N.State) (i : N.Inputs) :
  R.v4300 (state s) (inputs i) = Zmod.unsigned (N.v4300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4300 s i)) at 1.
  unfold R.v4300, N.v4300.
  rewrite ?node_4299.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1886_nr_5F1898.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1886_nr_5F1898 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4301 (s : N.State) (i : N.Inputs) :
  R.v4301 (state s) (inputs i) = Zmod.unsigned (N.v4301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4301 s i)) at 1.
  unfold R.v4301, N.v4301.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4302 (s : N.State) (i : N.Inputs) :
  R.v4302 (state s) (inputs i) = Zmod.unsigned (N.v4302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4302 s i)) at 1.
  unfold R.v4302, N.v4302.
  rewrite ?node_4301.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1887_nr_5F1899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1887_nr_5F1899 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4303 (s : N.State) (i : N.Inputs) :
  R.v4303 (state s) (inputs i) = Zmod.unsigned (N.v4303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4303 s i)) at 1.
  unfold R.v4303, N.v4303.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4304 (s : N.State) (i : N.Inputs) :
  R.v4304 (state s) (inputs i) = Zmod.unsigned (N.v4304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4304 s i)) at 1.
  unfold R.v4304, N.v4304.
  rewrite ?node_4303.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1888_nr_5F1900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1888_nr_5F1900 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4305 (s : N.State) (i : N.Inputs) :
  R.v4305 (state s) (inputs i) = Zmod.unsigned (N.v4305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4305 s i)) at 1.
  unfold R.v4305, N.v4305.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4306 (s : N.State) (i : N.Inputs) :
  R.v4306 (state s) (inputs i) = Zmod.unsigned (N.v4306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4306 s i)) at 1.
  unfold R.v4306, N.v4306.
  rewrite ?node_4305.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1889_nr_5F1901.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1889_nr_5F1901 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4307 (s : N.State) (i : N.Inputs) :
  R.v4307 (state s) (inputs i) = Zmod.unsigned (N.v4307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4307 s i)) at 1.
  unfold R.v4307, N.v4307.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4308 (s : N.State) (i : N.Inputs) :
  R.v4308 (state s) (inputs i) = Zmod.unsigned (N.v4308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4308 s i)) at 1.
  unfold R.v4308, N.v4308.
  rewrite ?node_4307.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1890_nr_5F1902.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1890_nr_5F1902 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4309 (s : N.State) (i : N.Inputs) :
  R.v4309 (state s) (inputs i) = Zmod.unsigned (N.v4309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4309 s i)) at 1.
  unfold R.v4309, N.v4309.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4310 (s : N.State) (i : N.Inputs) :
  R.v4310 (state s) (inputs i) = Zmod.unsigned (N.v4310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4310 s i)) at 1.
  unfold R.v4310, N.v4310.
  rewrite ?node_4309.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1891_nr_5F1903.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1891_nr_5F1903 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4311 (s : N.State) (i : N.Inputs) :
  R.v4311 (state s) (inputs i) = Zmod.unsigned (N.v4311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4311 s i)) at 1.
  unfold R.v4311, N.v4311.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4312 (s : N.State) (i : N.Inputs) :
  R.v4312 (state s) (inputs i) = Zmod.unsigned (N.v4312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4312 s i)) at 1.
  unfold R.v4312, N.v4312.
  rewrite ?node_4311.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1892_nr_5F1904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1892_nr_5F1904 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4313 (s : N.State) (i : N.Inputs) :
  R.v4313 (state s) (inputs i) = Zmod.unsigned (N.v4313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4313 s i)) at 1.
  unfold R.v4313, N.v4313.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4314 (s : N.State) (i : N.Inputs) :
  R.v4314 (state s) (inputs i) = Zmod.unsigned (N.v4314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4314 s i)) at 1.
  unfold R.v4314, N.v4314.
  rewrite ?node_4313.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1893_nr_5F1905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1893_nr_5F1905 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4315 (s : N.State) (i : N.Inputs) :
  R.v4315 (state s) (inputs i) = Zmod.unsigned (N.v4315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4315 s i)) at 1.
  unfold R.v4315, N.v4315.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4316 (s : N.State) (i : N.Inputs) :
  R.v4316 (state s) (inputs i) = Zmod.unsigned (N.v4316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4316 s i)) at 1.
  unfold R.v4316, N.v4316.
  rewrite ?node_4315.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1894_nr_5F1906.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1894_nr_5F1906 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4317 (s : N.State) (i : N.Inputs) :
  R.v4317 (state s) (inputs i) = Zmod.unsigned (N.v4317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4317 s i)) at 1.
  unfold R.v4317, N.v4317.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4318 (s : N.State) (i : N.Inputs) :
  R.v4318 (state s) (inputs i) = Zmod.unsigned (N.v4318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4318 s i)) at 1.
  unfold R.v4318, N.v4318.
  rewrite ?node_4317.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1895_nr_5F1907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1895_nr_5F1907 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4319 (s : N.State) (i : N.Inputs) :
  R.v4319 (state s) (inputs i) = Zmod.unsigned (N.v4319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4319 s i)) at 1.
  unfold R.v4319, N.v4319.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4320 (s : N.State) (i : N.Inputs) :
  R.v4320 (state s) (inputs i) = Zmod.unsigned (N.v4320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4320 s i)) at 1.
  unfold R.v4320, N.v4320.
  rewrite ?node_4319.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1896_nr_5F1908.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1896_nr_5F1908 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4321 (s : N.State) (i : N.Inputs) :
  R.v4321 (state s) (inputs i) = Zmod.unsigned (N.v4321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4321 s i)) at 1.
  unfold R.v4321, N.v4321.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4322 (s : N.State) (i : N.Inputs) :
  R.v4322 (state s) (inputs i) = Zmod.unsigned (N.v4322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4322 s i)) at 1.
  unfold R.v4322, N.v4322.
  rewrite ?node_4321.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1897_nr_5F1909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1897_nr_5F1909 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4323 (s : N.State) (i : N.Inputs) :
  R.v4323 (state s) (inputs i) = Zmod.unsigned (N.v4323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4323 s i)) at 1.
  unfold R.v4323, N.v4323.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4324 (s : N.State) (i : N.Inputs) :
  R.v4324 (state s) (inputs i) = Zmod.unsigned (N.v4324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4324 s i)) at 1.
  unfold R.v4324, N.v4324.
  rewrite ?node_4323.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1898_nr_5F1910.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1898_nr_5F1910 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4325 (s : N.State) (i : N.Inputs) :
  R.v4325 (state s) (inputs i) = Zmod.unsigned (N.v4325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4325 s i)) at 1.
  unfold R.v4325, N.v4325.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4326 (s : N.State) (i : N.Inputs) :
  R.v4326 (state s) (inputs i) = Zmod.unsigned (N.v4326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4326 s i)) at 1.
  unfold R.v4326, N.v4326.
  rewrite ?node_4325.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1899_nr_5F1912.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1899_nr_5F1912 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4327 (s : N.State) (i : N.Inputs) :
  R.v4327 (state s) (inputs i) = Zmod.unsigned (N.v4327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4327 s i)) at 1.
  unfold R.v4327, N.v4327.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4328 (s : N.State) (i : N.Inputs) :
  R.v4328 (state s) (inputs i) = Zmod.unsigned (N.v4328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4328 s i)) at 1.
  unfold R.v4328, N.v4328.
  rewrite ?node_4327.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1900_nr_5F1913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1900_nr_5F1913 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4329 (s : N.State) (i : N.Inputs) :
  R.v4329 (state s) (inputs i) = Zmod.unsigned (N.v4329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4329 s i)) at 1.
  unfold R.v4329, N.v4329.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4330 (s : N.State) (i : N.Inputs) :
  R.v4330 (state s) (inputs i) = Zmod.unsigned (N.v4330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4330 s i)) at 1.
  unfold R.v4330, N.v4330.
  rewrite ?node_4329.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1901_nr_5F1914.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1901_nr_5F1914 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4331 (s : N.State) (i : N.Inputs) :
  R.v4331 (state s) (inputs i) = Zmod.unsigned (N.v4331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4331 s i)) at 1.
  unfold R.v4331, N.v4331.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4332 (s : N.State) (i : N.Inputs) :
  R.v4332 (state s) (inputs i) = Zmod.unsigned (N.v4332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4332 s i)) at 1.
  unfold R.v4332, N.v4332.
  rewrite ?node_4331.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1902_nr_5F1915.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1902_nr_5F1915 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4333 (s : N.State) (i : N.Inputs) :
  R.v4333 (state s) (inputs i) = Zmod.unsigned (N.v4333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4333 s i)) at 1.
  unfold R.v4333, N.v4333.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4334 (s : N.State) (i : N.Inputs) :
  R.v4334 (state s) (inputs i) = Zmod.unsigned (N.v4334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4334 s i)) at 1.
  unfold R.v4334, N.v4334.
  rewrite ?node_4333.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1903_nr_5F1916.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1903_nr_5F1916 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4335 (s : N.State) (i : N.Inputs) :
  R.v4335 (state s) (inputs i) = Zmod.unsigned (N.v4335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4335 s i)) at 1.
  unfold R.v4335, N.v4335.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4336 (s : N.State) (i : N.Inputs) :
  R.v4336 (state s) (inputs i) = Zmod.unsigned (N.v4336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4336 s i)) at 1.
  unfold R.v4336, N.v4336.
  rewrite ?node_4335.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1904_nr_5F1917.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1904_nr_5F1917 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4337 (s : N.State) (i : N.Inputs) :
  R.v4337 (state s) (inputs i) = Zmod.unsigned (N.v4337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4337 s i)) at 1.
  unfold R.v4337, N.v4337.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4338 (s : N.State) (i : N.Inputs) :
  R.v4338 (state s) (inputs i) = Zmod.unsigned (N.v4338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4338 s i)) at 1.
  unfold R.v4338, N.v4338.
  rewrite ?node_4337.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1905_nr_5F1918.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1905_nr_5F1918 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4339 (s : N.State) (i : N.Inputs) :
  R.v4339 (state s) (inputs i) = Zmod.unsigned (N.v4339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4339 s i)) at 1.
  unfold R.v4339, N.v4339.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4340 (s : N.State) (i : N.Inputs) :
  R.v4340 (state s) (inputs i) = Zmod.unsigned (N.v4340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4340 s i)) at 1.
  unfold R.v4340, N.v4340.
  rewrite ?node_4339.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1906_nr_5F1919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1906_nr_5F1919 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4341 (s : N.State) (i : N.Inputs) :
  R.v4341 (state s) (inputs i) = Zmod.unsigned (N.v4341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4341 s i)) at 1.
  unfold R.v4341, N.v4341.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4342 (s : N.State) (i : N.Inputs) :
  R.v4342 (state s) (inputs i) = Zmod.unsigned (N.v4342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4342 s i)) at 1.
  unfold R.v4342, N.v4342.
  rewrite ?node_4341.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1907_nr_5F1920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1907_nr_5F1920 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4343 (s : N.State) (i : N.Inputs) :
  R.v4343 (state s) (inputs i) = Zmod.unsigned (N.v4343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4343 s i)) at 1.
  unfold R.v4343, N.v4343.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4344 (s : N.State) (i : N.Inputs) :
  R.v4344 (state s) (inputs i) = Zmod.unsigned (N.v4344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4344 s i)) at 1.
  unfold R.v4344, N.v4344.
  rewrite ?node_4343.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1908_nr_5F1921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1908_nr_5F1921 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4345 (s : N.State) (i : N.Inputs) :
  R.v4345 (state s) (inputs i) = Zmod.unsigned (N.v4345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4345 s i)) at 1.
  unfold R.v4345, N.v4345.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4346 (s : N.State) (i : N.Inputs) :
  R.v4346 (state s) (inputs i) = Zmod.unsigned (N.v4346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4346 s i)) at 1.
  unfold R.v4346, N.v4346.
  rewrite ?node_4345.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1909_nr_5F1922.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1909_nr_5F1922 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4347 (s : N.State) (i : N.Inputs) :
  R.v4347 (state s) (inputs i) = Zmod.unsigned (N.v4347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4347 s i)) at 1.
  unfold R.v4347, N.v4347.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4348 (s : N.State) (i : N.Inputs) :
  R.v4348 (state s) (inputs i) = Zmod.unsigned (N.v4348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4348 s i)) at 1.
  unfold R.v4348, N.v4348.
  rewrite ?node_4347.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1910_nr_5F1923.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1910_nr_5F1923 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4349 (s : N.State) (i : N.Inputs) :
  R.v4349 (state s) (inputs i) = Zmod.unsigned (N.v4349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4349 s i)) at 1.
  unfold R.v4349, N.v4349.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4350 (s : N.State) (i : N.Inputs) :
  R.v4350 (state s) (inputs i) = Zmod.unsigned (N.v4350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4350 s i)) at 1.
  unfold R.v4350, N.v4350.
  rewrite ?node_4349.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1911_nr_5F1924.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1911_nr_5F1924 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4351 (s : N.State) (i : N.Inputs) :
  R.v4351 (state s) (inputs i) = Zmod.unsigned (N.v4351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4351 s i)) at 1.
  unfold R.v4351, N.v4351.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4352 (s : N.State) (i : N.Inputs) :
  R.v4352 (state s) (inputs i) = Zmod.unsigned (N.v4352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4352 s i)) at 1.
  unfold R.v4352, N.v4352.
  rewrite ?node_4351.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1912_nr_5F1925.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1912_nr_5F1925 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4353 (s : N.State) (i : N.Inputs) :
  R.v4353 (state s) (inputs i) = Zmod.unsigned (N.v4353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4353 s i)) at 1.
  unfold R.v4353, N.v4353.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4354 (s : N.State) (i : N.Inputs) :
  R.v4354 (state s) (inputs i) = Zmod.unsigned (N.v4354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4354 s i)) at 1.
  unfold R.v4354, N.v4354.
  rewrite ?node_4353.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1913_nr_5F1926.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1913_nr_5F1926 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4355 (s : N.State) (i : N.Inputs) :
  R.v4355 (state s) (inputs i) = Zmod.unsigned (N.v4355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4355 s i)) at 1.
  unfold R.v4355, N.v4355.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4356 (s : N.State) (i : N.Inputs) :
  R.v4356 (state s) (inputs i) = Zmod.unsigned (N.v4356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4356 s i)) at 1.
  unfold R.v4356, N.v4356.
  rewrite ?node_4355.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1914_nr_5F1927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1914_nr_5F1927 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4357 (s : N.State) (i : N.Inputs) :
  R.v4357 (state s) (inputs i) = Zmod.unsigned (N.v4357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4357 s i)) at 1.
  unfold R.v4357, N.v4357.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4358 (s : N.State) (i : N.Inputs) :
  R.v4358 (state s) (inputs i) = Zmod.unsigned (N.v4358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4358 s i)) at 1.
  unfold R.v4358, N.v4358.
  rewrite ?node_4357.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1915_nr_5F1928.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1915_nr_5F1928 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4359 (s : N.State) (i : N.Inputs) :
  R.v4359 (state s) (inputs i) = Zmod.unsigned (N.v4359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4359 s i)) at 1.
  unfold R.v4359, N.v4359.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4360 (s : N.State) (i : N.Inputs) :
  R.v4360 (state s) (inputs i) = Zmod.unsigned (N.v4360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4360 s i)) at 1.
  unfold R.v4360, N.v4360.
  rewrite ?node_4359.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1916_nr_5F1929.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1916_nr_5F1929 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4361 (s : N.State) (i : N.Inputs) :
  R.v4361 (state s) (inputs i) = Zmod.unsigned (N.v4361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4361 s i)) at 1.
  unfold R.v4361, N.v4361.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4362 (s : N.State) (i : N.Inputs) :
  R.v4362 (state s) (inputs i) = Zmod.unsigned (N.v4362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4362 s i)) at 1.
  unfold R.v4362, N.v4362.
  rewrite ?node_4361.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1917_nr_5F1930.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1917_nr_5F1930 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4363 (s : N.State) (i : N.Inputs) :
  R.v4363 (state s) (inputs i) = Zmod.unsigned (N.v4363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4363 s i)) at 1.
  unfold R.v4363, N.v4363.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4364 (s : N.State) (i : N.Inputs) :
  R.v4364 (state s) (inputs i) = Zmod.unsigned (N.v4364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4364 s i)) at 1.
  unfold R.v4364, N.v4364.
  unfold R.v3021, N.v3021.
  rewrite ?node_4363.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4365 (s : N.State) (i : N.Inputs) :
  R.v4365 (state s) (inputs i) = Zmod.unsigned (N.v4365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4365 s i)) at 1.
  unfold R.v4365, N.v4365.
  rewrite ?node_4364.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1918_nr_5F1931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1918_nr_5F1931 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4366 (s : N.State) (i : N.Inputs) :
  R.v4366 (state s) (inputs i) = Zmod.unsigned (N.v4366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4366 s i)) at 1.
  unfold R.v4366, N.v4366.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4367 (s : N.State) (i : N.Inputs) :
  R.v4367 (state s) (inputs i) = Zmod.unsigned (N.v4367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4367 s i)) at 1.
  unfold R.v4367, N.v4367.
  rewrite ?node_4366.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1919_nr_5F1932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1919_nr_5F1932 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4368 (s : N.State) (i : N.Inputs) :
  R.v4368 (state s) (inputs i) = Zmod.unsigned (N.v4368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4368 s i)) at 1.
  unfold R.v4368, N.v4368.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4369 (s : N.State) (i : N.Inputs) :
  R.v4369 (state s) (inputs i) = Zmod.unsigned (N.v4369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4369 s i)) at 1.
  unfold R.v4369, N.v4369.
  rewrite ?node_4368.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1920_nr_5F1933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1920_nr_5F1933 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4370 (s : N.State) (i : N.Inputs) :
  R.v4370 (state s) (inputs i) = Zmod.unsigned (N.v4370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4370 s i)) at 1.
  unfold R.v4370, N.v4370.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4371 (s : N.State) (i : N.Inputs) :
  R.v4371 (state s) (inputs i) = Zmod.unsigned (N.v4371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4371 s i)) at 1.
  unfold R.v4371, N.v4371.
  rewrite ?node_4370.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1921_nr_5F1934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1921_nr_5F1934 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4372 (s : N.State) (i : N.Inputs) :
  R.v4372 (state s) (inputs i) = Zmod.unsigned (N.v4372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4372 s i)) at 1.
  unfold R.v4372, N.v4372.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4373 (s : N.State) (i : N.Inputs) :
  R.v4373 (state s) (inputs i) = Zmod.unsigned (N.v4373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4373 s i)) at 1.
  unfold R.v4373, N.v4373.
  rewrite ?node_4372.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1922_nr_5F1935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1922_nr_5F1935 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4374 (s : N.State) (i : N.Inputs) :
  R.v4374 (state s) (inputs i) = Zmod.unsigned (N.v4374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4374 s i)) at 1.
  unfold R.v4374, N.v4374.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4375 (s : N.State) (i : N.Inputs) :
  R.v4375 (state s) (inputs i) = Zmod.unsigned (N.v4375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4375 s i)) at 1.
  unfold R.v4375, N.v4375.
  rewrite ?node_4374.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1923_nr_5F1936.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1923_nr_5F1936 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4376 (s : N.State) (i : N.Inputs) :
  R.v4376 (state s) (inputs i) = Zmod.unsigned (N.v4376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4376 s i)) at 1.
  unfold R.v4376, N.v4376.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4377 (s : N.State) (i : N.Inputs) :
  R.v4377 (state s) (inputs i) = Zmod.unsigned (N.v4377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4377 s i)) at 1.
  unfold R.v4377, N.v4377.
  rewrite ?node_4376.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1924_nr_5F1937.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1924_nr_5F1937 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4378 (s : N.State) (i : N.Inputs) :
  R.v4378 (state s) (inputs i) = Zmod.unsigned (N.v4378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4378 s i)) at 1.
  unfold R.v4378, N.v4378.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4379 (s : N.State) (i : N.Inputs) :
  R.v4379 (state s) (inputs i) = Zmod.unsigned (N.v4379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4379 s i)) at 1.
  unfold R.v4379, N.v4379.
  rewrite ?node_4378.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1925_nr_5F1938.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1925_nr_5F1938 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4380 (s : N.State) (i : N.Inputs) :
  R.v4380 (state s) (inputs i) = Zmod.unsigned (N.v4380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4380 s i)) at 1.
  unfold R.v4380, N.v4380.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4381 (s : N.State) (i : N.Inputs) :
  R.v4381 (state s) (inputs i) = Zmod.unsigned (N.v4381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4381 s i)) at 1.
  unfold R.v4381, N.v4381.
  rewrite ?node_4380.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1926_nr_5F1939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1926_nr_5F1939 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4382 (s : N.State) (i : N.Inputs) :
  R.v4382 (state s) (inputs i) = Zmod.unsigned (N.v4382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4382 s i)) at 1.
  unfold R.v4382, N.v4382.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4383 (s : N.State) (i : N.Inputs) :
  R.v4383 (state s) (inputs i) = Zmod.unsigned (N.v4383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4383 s i)) at 1.
  unfold R.v4383, N.v4383.
  rewrite ?node_4382.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1927_nr_5F1940.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1927_nr_5F1940 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4384 (s : N.State) (i : N.Inputs) :
  R.v4384 (state s) (inputs i) = Zmod.unsigned (N.v4384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4384 s i)) at 1.
  unfold R.v4384, N.v4384.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4385 (s : N.State) (i : N.Inputs) :
  R.v4385 (state s) (inputs i) = Zmod.unsigned (N.v4385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4385 s i)) at 1.
  unfold R.v4385, N.v4385.
  rewrite ?node_4384.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1928_nr_5F1941.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1928_nr_5F1941 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4386 (s : N.State) (i : N.Inputs) :
  R.v4386 (state s) (inputs i) = Zmod.unsigned (N.v4386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4386 s i)) at 1.
  unfold R.v4386, N.v4386.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4387 (s : N.State) (i : N.Inputs) :
  R.v4387 (state s) (inputs i) = Zmod.unsigned (N.v4387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4387 s i)) at 1.
  unfold R.v4387, N.v4387.
  rewrite ?node_4386.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1929_nr_5F1942.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1929_nr_5F1942 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4388 (s : N.State) (i : N.Inputs) :
  R.v4388 (state s) (inputs i) = Zmod.unsigned (N.v4388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4388 s i)) at 1.
  unfold R.v4388, N.v4388.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4389 (s : N.State) (i : N.Inputs) :
  R.v4389 (state s) (inputs i) = Zmod.unsigned (N.v4389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4389 s i)) at 1.
  unfold R.v4389, N.v4389.
  rewrite ?node_4388.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1930_nr_5F1943.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1930_nr_5F1943 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4390 (s : N.State) (i : N.Inputs) :
  R.v4390 (state s) (inputs i) = Zmod.unsigned (N.v4390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4390 s i)) at 1.
  unfold R.v4390, N.v4390.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4391 (s : N.State) (i : N.Inputs) :
  R.v4391 (state s) (inputs i) = Zmod.unsigned (N.v4391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4391 s i)) at 1.
  unfold R.v4391, N.v4391.
  rewrite ?node_4390.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1931_nr_5F1944.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1931_nr_5F1944 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4392 (s : N.State) (i : N.Inputs) :
  R.v4392 (state s) (inputs i) = Zmod.unsigned (N.v4392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4392 s i)) at 1.
  unfold R.v4392, N.v4392.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4393 (s : N.State) (i : N.Inputs) :
  R.v4393 (state s) (inputs i) = Zmod.unsigned (N.v4393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4393 s i)) at 1.
  unfold R.v4393, N.v4393.
  rewrite ?node_4392.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1932_nr_5F1945.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1932_nr_5F1945 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4394 (s : N.State) (i : N.Inputs) :
  R.v4394 (state s) (inputs i) = Zmod.unsigned (N.v4394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4394 s i)) at 1.
  unfold R.v4394, N.v4394.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4395 (s : N.State) (i : N.Inputs) :
  R.v4395 (state s) (inputs i) = Zmod.unsigned (N.v4395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4395 s i)) at 1.
  unfold R.v4395, N.v4395.
  rewrite ?node_4394.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1933_nr_5F1946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1933_nr_5F1946 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4396 (s : N.State) (i : N.Inputs) :
  R.v4396 (state s) (inputs i) = Zmod.unsigned (N.v4396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4396 s i)) at 1.
  unfold R.v4396, N.v4396.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4397 (s : N.State) (i : N.Inputs) :
  R.v4397 (state s) (inputs i) = Zmod.unsigned (N.v4397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4397 s i)) at 1.
  unfold R.v4397, N.v4397.
  rewrite ?node_4396.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1934_nr_5F1947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1934_nr_5F1947 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4398 (s : N.State) (i : N.Inputs) :
  R.v4398 (state s) (inputs i) = Zmod.unsigned (N.v4398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4398 s i)) at 1.
  unfold R.v4398, N.v4398.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4399 (s : N.State) (i : N.Inputs) :
  R.v4399 (state s) (inputs i) = Zmod.unsigned (N.v4399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4399 s i)) at 1.
  unfold R.v4399, N.v4399.
  rewrite ?node_4398.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1935_nr_5F1948.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1935_nr_5F1948 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4400 (s : N.State) (i : N.Inputs) :
  R.v4400 (state s) (inputs i) = Zmod.unsigned (N.v4400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4400 s i)) at 1.
  unfold R.v4400, N.v4400.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4401 (s : N.State) (i : N.Inputs) :
  R.v4401 (state s) (inputs i) = Zmod.unsigned (N.v4401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4401 s i)) at 1.
  unfold R.v4401, N.v4401.
  rewrite ?node_4400.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1936_nr_5F1949.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1936_nr_5F1949 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4402 (s : N.State) (i : N.Inputs) :
  R.v4402 (state s) (inputs i) = Zmod.unsigned (N.v4402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4402 s i)) at 1.
  unfold R.v4402, N.v4402.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4403 (s : N.State) (i : N.Inputs) :
  R.v4403 (state s) (inputs i) = Zmod.unsigned (N.v4403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4403 s i)) at 1.
  unfold R.v4403, N.v4403.
  rewrite ?node_4402.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1937_nr_5F1951.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1937_nr_5F1951 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4404 (s : N.State) (i : N.Inputs) :
  R.v4404 (state s) (inputs i) = Zmod.unsigned (N.v4404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4404 s i)) at 1.
  unfold R.v4404, N.v4404.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4405 (s : N.State) (i : N.Inputs) :
  R.v4405 (state s) (inputs i) = Zmod.unsigned (N.v4405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4405 s i)) at 1.
  unfold R.v4405, N.v4405.
  rewrite ?node_4404.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1938_nr_5F1952.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1938_nr_5F1952 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4406 (s : N.State) (i : N.Inputs) :
  R.v4406 (state s) (inputs i) = Zmod.unsigned (N.v4406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4406 s i)) at 1.
  unfold R.v4406, N.v4406.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4407 (s : N.State) (i : N.Inputs) :
  R.v4407 (state s) (inputs i) = Zmod.unsigned (N.v4407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4407 s i)) at 1.
  unfold R.v4407, N.v4407.
  rewrite ?node_4406.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1939_nr_5F1953.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1939_nr_5F1953 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4408 (s : N.State) (i : N.Inputs) :
  R.v4408 (state s) (inputs i) = Zmod.unsigned (N.v4408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4408 s i)) at 1.
  unfold R.v4408, N.v4408.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4409 (s : N.State) (i : N.Inputs) :
  R.v4409 (state s) (inputs i) = Zmod.unsigned (N.v4409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4409 s i)) at 1.
  unfold R.v4409, N.v4409.
  rewrite ?node_4408.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1940_nr_5F1954.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1940_nr_5F1954 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4410 (s : N.State) (i : N.Inputs) :
  R.v4410 (state s) (inputs i) = Zmod.unsigned (N.v4410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4410 s i)) at 1.
  unfold R.v4410, N.v4410.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4411 (s : N.State) (i : N.Inputs) :
  R.v4411 (state s) (inputs i) = Zmod.unsigned (N.v4411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4411 s i)) at 1.
  unfold R.v4411, N.v4411.
  rewrite ?node_4410.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1941_nr_5F1955.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1941_nr_5F1955 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4412 (s : N.State) (i : N.Inputs) :
  R.v4412 (state s) (inputs i) = Zmod.unsigned (N.v4412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4412 s i)) at 1.
  unfold R.v4412, N.v4412.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4413 (s : N.State) (i : N.Inputs) :
  R.v4413 (state s) (inputs i) = Zmod.unsigned (N.v4413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4413 s i)) at 1.
  unfold R.v4413, N.v4413.
  rewrite ?node_4412.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1942_nr_5F1956.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1942_nr_5F1956 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4414 (s : N.State) (i : N.Inputs) :
  R.v4414 (state s) (inputs i) = Zmod.unsigned (N.v4414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4414 s i)) at 1.
  unfold R.v4414, N.v4414.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4415 (s : N.State) (i : N.Inputs) :
  R.v4415 (state s) (inputs i) = Zmod.unsigned (N.v4415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4415 s i)) at 1.
  unfold R.v4415, N.v4415.
  rewrite ?node_4414.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1943_nr_5F1957.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1943_nr_5F1957 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4416 (s : N.State) (i : N.Inputs) :
  R.v4416 (state s) (inputs i) = Zmod.unsigned (N.v4416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4416 s i)) at 1.
  unfold R.v4416, N.v4416.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4417 (s : N.State) (i : N.Inputs) :
  R.v4417 (state s) (inputs i) = Zmod.unsigned (N.v4417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4417 s i)) at 1.
  unfold R.v4417, N.v4417.
  rewrite ?node_4416.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1944_nr_5F1958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1944_nr_5F1958 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4418 (s : N.State) (i : N.Inputs) :
  R.v4418 (state s) (inputs i) = Zmod.unsigned (N.v4418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4418 s i)) at 1.
  unfold R.v4418, N.v4418.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4419 (s : N.State) (i : N.Inputs) :
  R.v4419 (state s) (inputs i) = Zmod.unsigned (N.v4419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4419 s i)) at 1.
  unfold R.v4419, N.v4419.
  rewrite ?node_4418.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1945_nr_5F1959.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1945_nr_5F1959 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4420 (s : N.State) (i : N.Inputs) :
  R.v4420 (state s) (inputs i) = Zmod.unsigned (N.v4420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4420 s i)) at 1.
  unfold R.v4420, N.v4420.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4421 (s : N.State) (i : N.Inputs) :
  R.v4421 (state s) (inputs i) = Zmod.unsigned (N.v4421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4421 s i)) at 1.
  unfold R.v4421, N.v4421.
  rewrite ?node_4420.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1946_nr_5F1960.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1946_nr_5F1960 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4422 (s : N.State) (i : N.Inputs) :
  R.v4422 (state s) (inputs i) = Zmod.unsigned (N.v4422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4422 s i)) at 1.
  unfold R.v4422, N.v4422.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4423 (s : N.State) (i : N.Inputs) :
  R.v4423 (state s) (inputs i) = Zmod.unsigned (N.v4423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4423 s i)) at 1.
  unfold R.v4423, N.v4423.
  rewrite ?node_4422.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1947_nr_5F1961.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1947_nr_5F1961 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4424 (s : N.State) (i : N.Inputs) :
  R.v4424 (state s) (inputs i) = Zmod.unsigned (N.v4424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4424 s i)) at 1.
  unfold R.v4424, N.v4424.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4425 (s : N.State) (i : N.Inputs) :
  R.v4425 (state s) (inputs i) = Zmod.unsigned (N.v4425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4425 s i)) at 1.
  unfold R.v4425, N.v4425.
  rewrite ?node_4424.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1948_nr_5F1962.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1948_nr_5F1962 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4426 (s : N.State) (i : N.Inputs) :
  R.v4426 (state s) (inputs i) = Zmod.unsigned (N.v4426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4426 s i)) at 1.
  unfold R.v4426, N.v4426.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4427 (s : N.State) (i : N.Inputs) :
  R.v4427 (state s) (inputs i) = Zmod.unsigned (N.v4427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4427 s i)) at 1.
  unfold R.v4427, N.v4427.
  rewrite ?node_4426.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1949_nr_5F1963.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1949_nr_5F1963 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4428 (s : N.State) (i : N.Inputs) :
  R.v4428 (state s) (inputs i) = Zmod.unsigned (N.v4428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4428 s i)) at 1.
  unfold R.v4428, N.v4428.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4429 (s : N.State) (i : N.Inputs) :
  R.v4429 (state s) (inputs i) = Zmod.unsigned (N.v4429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4429 s i)) at 1.
  unfold R.v4429, N.v4429.
  rewrite ?node_4428.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1950_nr_5F1964.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1950_nr_5F1964 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4430 (s : N.State) (i : N.Inputs) :
  R.v4430 (state s) (inputs i) = Zmod.unsigned (N.v4430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4430 s i)) at 1.
  unfold R.v4430, N.v4430.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4431 (s : N.State) (i : N.Inputs) :
  R.v4431 (state s) (inputs i) = Zmod.unsigned (N.v4431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4431 s i)) at 1.
  unfold R.v4431, N.v4431.
  rewrite ?node_4430.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1951_nr_5F1965.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1951_nr_5F1965 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4432 (s : N.State) (i : N.Inputs) :
  R.v4432 (state s) (inputs i) = Zmod.unsigned (N.v4432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4432 s i)) at 1.
  unfold R.v4432, N.v4432.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4433 (s : N.State) (i : N.Inputs) :
  R.v4433 (state s) (inputs i) = Zmod.unsigned (N.v4433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4433 s i)) at 1.
  unfold R.v4433, N.v4433.
  rewrite ?node_4432.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1952_nr_5F1966.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1952_nr_5F1966 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4434 (s : N.State) (i : N.Inputs) :
  R.v4434 (state s) (inputs i) = Zmod.unsigned (N.v4434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4434 s i)) at 1.
  unfold R.v4434, N.v4434.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4435 (s : N.State) (i : N.Inputs) :
  R.v4435 (state s) (inputs i) = Zmod.unsigned (N.v4435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4435 s i)) at 1.
  unfold R.v4435, N.v4435.
  rewrite ?node_4434.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1953_nr_5F1967.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1953_nr_5F1967 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4436 (s : N.State) (i : N.Inputs) :
  R.v4436 (state s) (inputs i) = Zmod.unsigned (N.v4436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4436 s i)) at 1.
  unfold R.v4436, N.v4436.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4437 (s : N.State) (i : N.Inputs) :
  R.v4437 (state s) (inputs i) = Zmod.unsigned (N.v4437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4437 s i)) at 1.
  unfold R.v4437, N.v4437.
  rewrite ?node_4436.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1954_nr_5F1968.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1954_nr_5F1968 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4438 (s : N.State) (i : N.Inputs) :
  R.v4438 (state s) (inputs i) = Zmod.unsigned (N.v4438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4438 s i)) at 1.
  unfold R.v4438, N.v4438.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4439 (s : N.State) (i : N.Inputs) :
  R.v4439 (state s) (inputs i) = Zmod.unsigned (N.v4439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4439 s i)) at 1.
  unfold R.v4439, N.v4439.
  unfold R.v3021, N.v3021.
  rewrite ?node_4438.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4440 (s : N.State) (i : N.Inputs) :
  R.v4440 (state s) (inputs i) = Zmod.unsigned (N.v4440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4440 s i)) at 1.
  unfold R.v4440, N.v4440.
  rewrite ?node_4439.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1955_nr_5F1969.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1955_nr_5F1969 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4441 (s : N.State) (i : N.Inputs) :
  R.v4441 (state s) (inputs i) = Zmod.unsigned (N.v4441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4441 s i)) at 1.
  unfold R.v4441, N.v4441.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4442 (s : N.State) (i : N.Inputs) :
  R.v4442 (state s) (inputs i) = Zmod.unsigned (N.v4442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4442 s i)) at 1.
  unfold R.v4442, N.v4442.
  rewrite ?node_4441.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1956_nr_5F1970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1956_nr_5F1970 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4443 (s : N.State) (i : N.Inputs) :
  R.v4443 (state s) (inputs i) = Zmod.unsigned (N.v4443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4443 s i)) at 1.
  unfold R.v4443, N.v4443.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4444 (s : N.State) (i : N.Inputs) :
  R.v4444 (state s) (inputs i) = Zmod.unsigned (N.v4444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4444 s i)) at 1.
  unfold R.v4444, N.v4444.
  rewrite ?node_4443.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1957_nr_5F1971.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1957_nr_5F1971 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4445 (s : N.State) (i : N.Inputs) :
  R.v4445 (state s) (inputs i) = Zmod.unsigned (N.v4445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4445 s i)) at 1.
  unfold R.v4445, N.v4445.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4446 (s : N.State) (i : N.Inputs) :
  R.v4446 (state s) (inputs i) = Zmod.unsigned (N.v4446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4446 s i)) at 1.
  unfold R.v4446, N.v4446.
  rewrite ?node_4445.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1958_nr_5F1972.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1958_nr_5F1972 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4447 (s : N.State) (i : N.Inputs) :
  R.v4447 (state s) (inputs i) = Zmod.unsigned (N.v4447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4447 s i)) at 1.
  unfold R.v4447, N.v4447.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4448 (s : N.State) (i : N.Inputs) :
  R.v4448 (state s) (inputs i) = Zmod.unsigned (N.v4448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4448 s i)) at 1.
  unfold R.v4448, N.v4448.
  rewrite ?node_4447.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1959_nr_5F1973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1959_nr_5F1973 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4449 (s : N.State) (i : N.Inputs) :
  R.v4449 (state s) (inputs i) = Zmod.unsigned (N.v4449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4449 s i)) at 1.
  unfold R.v4449, N.v4449.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4450 (s : N.State) (i : N.Inputs) :
  R.v4450 (state s) (inputs i) = Zmod.unsigned (N.v4450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4450 s i)) at 1.
  unfold R.v4450, N.v4450.
  rewrite ?node_4449.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1960_nr_5F1974.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1960_nr_5F1974 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4451 (s : N.State) (i : N.Inputs) :
  R.v4451 (state s) (inputs i) = Zmod.unsigned (N.v4451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4451 s i)) at 1.
  unfold R.v4451, N.v4451.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4452 (s : N.State) (i : N.Inputs) :
  R.v4452 (state s) (inputs i) = Zmod.unsigned (N.v4452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4452 s i)) at 1.
  unfold R.v4452, N.v4452.
  rewrite ?node_4451.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1961_nr_5F1975.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1961_nr_5F1975 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4453 (s : N.State) (i : N.Inputs) :
  R.v4453 (state s) (inputs i) = Zmod.unsigned (N.v4453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4453 s i)) at 1.
  unfold R.v4453, N.v4453.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4454 (s : N.State) (i : N.Inputs) :
  R.v4454 (state s) (inputs i) = Zmod.unsigned (N.v4454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4454 s i)) at 1.
  unfold R.v4454, N.v4454.
  rewrite ?node_4453.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1962_nr_5F1976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1962_nr_5F1976 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4455 (s : N.State) (i : N.Inputs) :
  R.v4455 (state s) (inputs i) = Zmod.unsigned (N.v4455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4455 s i)) at 1.
  unfold R.v4455, N.v4455.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4456 (s : N.State) (i : N.Inputs) :
  R.v4456 (state s) (inputs i) = Zmod.unsigned (N.v4456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4456 s i)) at 1.
  unfold R.v4456, N.v4456.
  rewrite ?node_4455.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1963_nr_5F1977.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1963_nr_5F1977 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4457 (s : N.State) (i : N.Inputs) :
  R.v4457 (state s) (inputs i) = Zmod.unsigned (N.v4457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4457 s i)) at 1.
  unfold R.v4457, N.v4457.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4458 (s : N.State) (i : N.Inputs) :
  R.v4458 (state s) (inputs i) = Zmod.unsigned (N.v4458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4458 s i)) at 1.
  unfold R.v4458, N.v4458.
  rewrite ?node_4457.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1964_nr_5F1978.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1964_nr_5F1978 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4459 (s : N.State) (i : N.Inputs) :
  R.v4459 (state s) (inputs i) = Zmod.unsigned (N.v4459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4459 s i)) at 1.
  unfold R.v4459, N.v4459.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4460 (s : N.State) (i : N.Inputs) :
  R.v4460 (state s) (inputs i) = Zmod.unsigned (N.v4460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4460 s i)) at 1.
  unfold R.v4460, N.v4460.
  rewrite ?node_4459.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1965_nr_5F1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1965_nr_5F1979 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4461 (s : N.State) (i : N.Inputs) :
  R.v4461 (state s) (inputs i) = Zmod.unsigned (N.v4461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4461 s i)) at 1.
  unfold R.v4461, N.v4461.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4462 (s : N.State) (i : N.Inputs) :
  R.v4462 (state s) (inputs i) = Zmod.unsigned (N.v4462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4462 s i)) at 1.
  unfold R.v4462, N.v4462.
  rewrite ?node_4461.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1966_nr_5F1980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1966_nr_5F1980 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4463 (s : N.State) (i : N.Inputs) :
  R.v4463 (state s) (inputs i) = Zmod.unsigned (N.v4463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4463 s i)) at 1.
  unfold R.v4463, N.v4463.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4464 (s : N.State) (i : N.Inputs) :
  R.v4464 (state s) (inputs i) = Zmod.unsigned (N.v4464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4464 s i)) at 1.
  unfold R.v4464, N.v4464.
  rewrite ?node_4463.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1967_nr_5F1981.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1967_nr_5F1981 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4465 (s : N.State) (i : N.Inputs) :
  R.v4465 (state s) (inputs i) = Zmod.unsigned (N.v4465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4465 s i)) at 1.
  unfold R.v4465, N.v4465.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4466 (s : N.State) (i : N.Inputs) :
  R.v4466 (state s) (inputs i) = Zmod.unsigned (N.v4466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4466 s i)) at 1.
  unfold R.v4466, N.v4466.
  rewrite ?node_4465.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1968_nr_5F1982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1968_nr_5F1982 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4467 (s : N.State) (i : N.Inputs) :
  R.v4467 (state s) (inputs i) = Zmod.unsigned (N.v4467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4467 s i)) at 1.
  unfold R.v4467, N.v4467.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4468 (s : N.State) (i : N.Inputs) :
  R.v4468 (state s) (inputs i) = Zmod.unsigned (N.v4468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4468 s i)) at 1.
  unfold R.v4468, N.v4468.
  rewrite ?node_4467.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1969_nr_5F1983.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1969_nr_5F1983 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4469 (s : N.State) (i : N.Inputs) :
  R.v4469 (state s) (inputs i) = Zmod.unsigned (N.v4469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4469 s i)) at 1.
  unfold R.v4469, N.v4469.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4470 (s : N.State) (i : N.Inputs) :
  R.v4470 (state s) (inputs i) = Zmod.unsigned (N.v4470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4470 s i)) at 1.
  unfold R.v4470, N.v4470.
  rewrite ?node_4469.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1970_nr_5F1984.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1970_nr_5F1984 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4471 (s : N.State) (i : N.Inputs) :
  R.v4471 (state s) (inputs i) = Zmod.unsigned (N.v4471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4471 s i)) at 1.
  unfold R.v4471, N.v4471.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4472 (s : N.State) (i : N.Inputs) :
  R.v4472 (state s) (inputs i) = Zmod.unsigned (N.v4472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4472 s i)) at 1.
  unfold R.v4472, N.v4472.
  rewrite ?node_4471.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1971_nr_5F1985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1971_nr_5F1985 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4473 (s : N.State) (i : N.Inputs) :
  R.v4473 (state s) (inputs i) = Zmod.unsigned (N.v4473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4473 s i)) at 1.
  unfold R.v4473, N.v4473.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4474 (s : N.State) (i : N.Inputs) :
  R.v4474 (state s) (inputs i) = Zmod.unsigned (N.v4474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4474 s i)) at 1.
  unfold R.v4474, N.v4474.
  rewrite ?node_4473.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1972_nr_5F1986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1972_nr_5F1986 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4475 (s : N.State) (i : N.Inputs) :
  R.v4475 (state s) (inputs i) = Zmod.unsigned (N.v4475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4475 s i)) at 1.
  unfold R.v4475, N.v4475.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4476 (s : N.State) (i : N.Inputs) :
  R.v4476 (state s) (inputs i) = Zmod.unsigned (N.v4476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4476 s i)) at 1.
  unfold R.v4476, N.v4476.
  rewrite ?node_4475.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1973_nr_5F1988.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1973_nr_5F1988 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4477 (s : N.State) (i : N.Inputs) :
  R.v4477 (state s) (inputs i) = Zmod.unsigned (N.v4477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4477 s i)) at 1.
  unfold R.v4477, N.v4477.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4478 (s : N.State) (i : N.Inputs) :
  R.v4478 (state s) (inputs i) = Zmod.unsigned (N.v4478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4478 s i)) at 1.
  unfold R.v4478, N.v4478.
  rewrite ?node_4477.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1974_nr_5F1989.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1974_nr_5F1989 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4479 (s : N.State) (i : N.Inputs) :
  R.v4479 (state s) (inputs i) = Zmod.unsigned (N.v4479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4479 s i)) at 1.
  unfold R.v4479, N.v4479.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4480 (s : N.State) (i : N.Inputs) :
  R.v4480 (state s) (inputs i) = Zmod.unsigned (N.v4480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4480 s i)) at 1.
  unfold R.v4480, N.v4480.
  rewrite ?node_4479.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1975_nr_5F1990.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1975_nr_5F1990 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4481 (s : N.State) (i : N.Inputs) :
  R.v4481 (state s) (inputs i) = Zmod.unsigned (N.v4481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4481 s i)) at 1.
  unfold R.v4481, N.v4481.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4482 (s : N.State) (i : N.Inputs) :
  R.v4482 (state s) (inputs i) = Zmod.unsigned (N.v4482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4482 s i)) at 1.
  unfold R.v4482, N.v4482.
  rewrite ?node_4481.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1976_nr_5F1991.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1976_nr_5F1991 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4483 (s : N.State) (i : N.Inputs) :
  R.v4483 (state s) (inputs i) = Zmod.unsigned (N.v4483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4483 s i)) at 1.
  unfold R.v4483, N.v4483.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4484 (s : N.State) (i : N.Inputs) :
  R.v4484 (state s) (inputs i) = Zmod.unsigned (N.v4484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4484 s i)) at 1.
  unfold R.v4484, N.v4484.
  rewrite ?node_4483.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1977_nr_5F1992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1977_nr_5F1992 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4485 (s : N.State) (i : N.Inputs) :
  R.v4485 (state s) (inputs i) = Zmod.unsigned (N.v4485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4485 s i)) at 1.
  unfold R.v4485, N.v4485.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4486 (s : N.State) (i : N.Inputs) :
  R.v4486 (state s) (inputs i) = Zmod.unsigned (N.v4486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4486 s i)) at 1.
  unfold R.v4486, N.v4486.
  rewrite ?node_4485.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1978_nr_5F1993.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1978_nr_5F1993 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4487 (s : N.State) (i : N.Inputs) :
  R.v4487 (state s) (inputs i) = Zmod.unsigned (N.v4487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4487 s i)) at 1.
  unfold R.v4487, N.v4487.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4488 (s : N.State) (i : N.Inputs) :
  R.v4488 (state s) (inputs i) = Zmod.unsigned (N.v4488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4488 s i)) at 1.
  unfold R.v4488, N.v4488.
  rewrite ?node_4487.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1979_nr_5F1994.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1979_nr_5F1994 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4489 (s : N.State) (i : N.Inputs) :
  R.v4489 (state s) (inputs i) = Zmod.unsigned (N.v4489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4489 s i)) at 1.
  unfold R.v4489, N.v4489.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4490 (s : N.State) (i : N.Inputs) :
  R.v4490 (state s) (inputs i) = Zmod.unsigned (N.v4490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4490 s i)) at 1.
  unfold R.v4490, N.v4490.
  rewrite ?node_4489.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1980_nr_5F1995.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1980_nr_5F1995 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4491 (s : N.State) (i : N.Inputs) :
  R.v4491 (state s) (inputs i) = Zmod.unsigned (N.v4491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4491 s i)) at 1.
  unfold R.v4491, N.v4491.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4492 (s : N.State) (i : N.Inputs) :
  R.v4492 (state s) (inputs i) = Zmod.unsigned (N.v4492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4492 s i)) at 1.
  unfold R.v4492, N.v4492.
  rewrite ?node_4491.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1981_nr_5F1996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1981_nr_5F1996 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4493 (s : N.State) (i : N.Inputs) :
  R.v4493 (state s) (inputs i) = Zmod.unsigned (N.v4493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4493 s i)) at 1.
  unfold R.v4493, N.v4493.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4494 (s : N.State) (i : N.Inputs) :
  R.v4494 (state s) (inputs i) = Zmod.unsigned (N.v4494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4494 s i)) at 1.
  unfold R.v4494, N.v4494.
  rewrite ?node_4493.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1982_nr_5F1997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1982_nr_5F1997 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4495 (s : N.State) (i : N.Inputs) :
  R.v4495 (state s) (inputs i) = Zmod.unsigned (N.v4495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4495 s i)) at 1.
  unfold R.v4495, N.v4495.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4496 (s : N.State) (i : N.Inputs) :
  R.v4496 (state s) (inputs i) = Zmod.unsigned (N.v4496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4496 s i)) at 1.
  unfold R.v4496, N.v4496.
  rewrite ?node_4495.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1983_nr_5F1998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1983_nr_5F1998 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4497 (s : N.State) (i : N.Inputs) :
  R.v4497 (state s) (inputs i) = Zmod.unsigned (N.v4497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4497 s i)) at 1.
  unfold R.v4497, N.v4497.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4498 (s : N.State) (i : N.Inputs) :
  R.v4498 (state s) (inputs i) = Zmod.unsigned (N.v4498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4498 s i)) at 1.
  unfold R.v4498, N.v4498.
  rewrite ?node_4497.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1984_nr_5F1999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1984_nr_5F1999 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4499 (s : N.State) (i : N.Inputs) :
  R.v4499 (state s) (inputs i) = Zmod.unsigned (N.v4499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4499 s i)) at 1.
  unfold R.v4499, N.v4499.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4500 (s : N.State) (i : N.Inputs) :
  R.v4500 (state s) (inputs i) = Zmod.unsigned (N.v4500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4500 s i)) at 1.
  unfold R.v4500, N.v4500.
  rewrite ?node_4499.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1985_nr_5F2000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1985_nr_5F2000 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4501 (s : N.State) (i : N.Inputs) :
  R.v4501 (state s) (inputs i) = Zmod.unsigned (N.v4501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4501 s i)) at 1.
  unfold R.v4501, N.v4501.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4502 (s : N.State) (i : N.Inputs) :
  R.v4502 (state s) (inputs i) = Zmod.unsigned (N.v4502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4502 s i)) at 1.
  unfold R.v4502, N.v4502.
  rewrite ?node_4501.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1986_nr_5F2001.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1986_nr_5F2001 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4503 (s : N.State) (i : N.Inputs) :
  R.v4503 (state s) (inputs i) = Zmod.unsigned (N.v4503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4503 s i)) at 1.
  unfold R.v4503, N.v4503.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4504 (s : N.State) (i : N.Inputs) :
  R.v4504 (state s) (inputs i) = Zmod.unsigned (N.v4504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4504 s i)) at 1.
  unfold R.v4504, N.v4504.
  rewrite ?node_4503.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1987_nr_5F2002.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1987_nr_5F2002 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4505 (s : N.State) (i : N.Inputs) :
  R.v4505 (state s) (inputs i) = Zmod.unsigned (N.v4505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4505 s i)) at 1.
  unfold R.v4505, N.v4505.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4506 (s : N.State) (i : N.Inputs) :
  R.v4506 (state s) (inputs i) = Zmod.unsigned (N.v4506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4506 s i)) at 1.
  unfold R.v4506, N.v4506.
  rewrite ?node_4505.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1988_nr_5F2003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1988_nr_5F2003 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4507 (s : N.State) (i : N.Inputs) :
  R.v4507 (state s) (inputs i) = Zmod.unsigned (N.v4507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4507 s i)) at 1.
  unfold R.v4507, N.v4507.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4508 (s : N.State) (i : N.Inputs) :
  R.v4508 (state s) (inputs i) = Zmod.unsigned (N.v4508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4508 s i)) at 1.
  unfold R.v4508, N.v4508.
  rewrite ?node_4507.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1989_nr_5F2004.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1989_nr_5F2004 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4509 (s : N.State) (i : N.Inputs) :
  R.v4509 (state s) (inputs i) = Zmod.unsigned (N.v4509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4509 s i)) at 1.
  unfold R.v4509, N.v4509.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4510 (s : N.State) (i : N.Inputs) :
  R.v4510 (state s) (inputs i) = Zmod.unsigned (N.v4510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4510 s i)) at 1.
  unfold R.v4510, N.v4510.
  unfold R.v3021, N.v3021.
  rewrite ?node_4509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4511 (s : N.State) (i : N.Inputs) :
  R.v4511 (state s) (inputs i) = Zmod.unsigned (N.v4511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4511 s i)) at 1.
  unfold R.v4511, N.v4511.
  rewrite ?node_4510.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1990_nr_5F2005.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1990_nr_5F2005 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4512 (s : N.State) (i : N.Inputs) :
  R.v4512 (state s) (inputs i) = Zmod.unsigned (N.v4512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4512 s i)) at 1.
  unfold R.v4512, N.v4512.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4513 (s : N.State) (i : N.Inputs) :
  R.v4513 (state s) (inputs i) = Zmod.unsigned (N.v4513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4513 s i)) at 1.
  unfold R.v4513, N.v4513.
  rewrite ?node_4512.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1991_nr_5F2006.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1991_nr_5F2006 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4514 (s : N.State) (i : N.Inputs) :
  R.v4514 (state s) (inputs i) = Zmod.unsigned (N.v4514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4514 s i)) at 1.
  unfold R.v4514, N.v4514.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4515 (s : N.State) (i : N.Inputs) :
  R.v4515 (state s) (inputs i) = Zmod.unsigned (N.v4515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4515 s i)) at 1.
  unfold R.v4515, N.v4515.
  rewrite ?node_4514.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1992_nr_5F2007.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1992_nr_5F2007 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4516 (s : N.State) (i : N.Inputs) :
  R.v4516 (state s) (inputs i) = Zmod.unsigned (N.v4516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4516 s i)) at 1.
  unfold R.v4516, N.v4516.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4517 (s : N.State) (i : N.Inputs) :
  R.v4517 (state s) (inputs i) = Zmod.unsigned (N.v4517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4517 s i)) at 1.
  unfold R.v4517, N.v4517.
  rewrite ?node_4516.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1993_nr_5F2008.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1993_nr_5F2008 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4518 (s : N.State) (i : N.Inputs) :
  R.v4518 (state s) (inputs i) = Zmod.unsigned (N.v4518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4518 s i)) at 1.
  unfold R.v4518, N.v4518.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4519 (s : N.State) (i : N.Inputs) :
  R.v4519 (state s) (inputs i) = Zmod.unsigned (N.v4519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4519 s i)) at 1.
  unfold R.v4519, N.v4519.
  rewrite ?node_4518.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1994_nr_5F2009.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1994_nr_5F2009 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4520 (s : N.State) (i : N.Inputs) :
  R.v4520 (state s) (inputs i) = Zmod.unsigned (N.v4520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4520 s i)) at 1.
  unfold R.v4520, N.v4520.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4521 (s : N.State) (i : N.Inputs) :
  R.v4521 (state s) (inputs i) = Zmod.unsigned (N.v4521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4521 s i)) at 1.
  unfold R.v4521, N.v4521.
  rewrite ?node_4520.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1995_nr_5F2010.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1995_nr_5F2010 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4522 (s : N.State) (i : N.Inputs) :
  R.v4522 (state s) (inputs i) = Zmod.unsigned (N.v4522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4522 s i)) at 1.
  unfold R.v4522, N.v4522.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4523 (s : N.State) (i : N.Inputs) :
  R.v4523 (state s) (inputs i) = Zmod.unsigned (N.v4523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4523 s i)) at 1.
  unfold R.v4523, N.v4523.
  rewrite ?node_4522.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1996_nr_5F2011.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1996_nr_5F2011 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4524 (s : N.State) (i : N.Inputs) :
  R.v4524 (state s) (inputs i) = Zmod.unsigned (N.v4524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4524 s i)) at 1.
  unfold R.v4524, N.v4524.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4525 (s : N.State) (i : N.Inputs) :
  R.v4525 (state s) (inputs i) = Zmod.unsigned (N.v4525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4525 s i)) at 1.
  unfold R.v4525, N.v4525.
  rewrite ?node_4524.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1997_nr_5F2012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1997_nr_5F2012 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4526 (s : N.State) (i : N.Inputs) :
  R.v4526 (state s) (inputs i) = Zmod.unsigned (N.v4526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4526 s i)) at 1.
  unfold R.v4526, N.v4526.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4527 (s : N.State) (i : N.Inputs) :
  R.v4527 (state s) (inputs i) = Zmod.unsigned (N.v4527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4527 s i)) at 1.
  unfold R.v4527, N.v4527.
  rewrite ?node_4526.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1998_nr_5F2013.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1998_nr_5F2013 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4528 (s : N.State) (i : N.Inputs) :
  R.v4528 (state s) (inputs i) = Zmod.unsigned (N.v4528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4528 s i)) at 1.
  unfold R.v4528, N.v4528.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4529 (s : N.State) (i : N.Inputs) :
  R.v4529 (state s) (inputs i) = Zmod.unsigned (N.v4529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4529 s i)) at 1.
  unfold R.v4529, N.v4529.
  rewrite ?node_4528.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1999_nr_5F2014.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1999_nr_5F2014 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4530 (s : N.State) (i : N.Inputs) :
  R.v4530 (state s) (inputs i) = Zmod.unsigned (N.v4530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4530 s i)) at 1.
  unfold R.v4530, N.v4530.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4531 (s : N.State) (i : N.Inputs) :
  R.v4531 (state s) (inputs i) = Zmod.unsigned (N.v4531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4531 s i)) at 1.
  unfold R.v4531, N.v4531.
  rewrite ?node_4530.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2000_nr_5F2015.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2000_nr_5F2015 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4532 (s : N.State) (i : N.Inputs) :
  R.v4532 (state s) (inputs i) = Zmod.unsigned (N.v4532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4532 s i)) at 1.
  unfold R.v4532, N.v4532.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4533 (s : N.State) (i : N.Inputs) :
  R.v4533 (state s) (inputs i) = Zmod.unsigned (N.v4533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4533 s i)) at 1.
  unfold R.v4533, N.v4533.
  rewrite ?node_4532.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2001_nr_5F2016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2001_nr_5F2016 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4534 (s : N.State) (i : N.Inputs) :
  R.v4534 (state s) (inputs i) = Zmod.unsigned (N.v4534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4534 s i)) at 1.
  unfold R.v4534, N.v4534.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4535 (s : N.State) (i : N.Inputs) :
  R.v4535 (state s) (inputs i) = Zmod.unsigned (N.v4535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4535 s i)) at 1.
  unfold R.v4535, N.v4535.
  rewrite ?node_4534.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2002_nr_5F2017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2002_nr_5F2017 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4536 (s : N.State) (i : N.Inputs) :
  R.v4536 (state s) (inputs i) = Zmod.unsigned (N.v4536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4536 s i)) at 1.
  unfold R.v4536, N.v4536.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4537 (s : N.State) (i : N.Inputs) :
  R.v4537 (state s) (inputs i) = Zmod.unsigned (N.v4537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4537 s i)) at 1.
  unfold R.v4537, N.v4537.
  rewrite ?node_4536.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2003_nr_5F2018.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2003_nr_5F2018 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4538 (s : N.State) (i : N.Inputs) :
  R.v4538 (state s) (inputs i) = Zmod.unsigned (N.v4538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4538 s i)) at 1.
  unfold R.v4538, N.v4538.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4539 (s : N.State) (i : N.Inputs) :
  R.v4539 (state s) (inputs i) = Zmod.unsigned (N.v4539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4539 s i)) at 1.
  unfold R.v4539, N.v4539.
  rewrite ?node_4538.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2004_nr_5F2019.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2004_nr_5F2019 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4540 (s : N.State) (i : N.Inputs) :
  R.v4540 (state s) (inputs i) = Zmod.unsigned (N.v4540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4540 s i)) at 1.
  unfold R.v4540, N.v4540.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4541 (s : N.State) (i : N.Inputs) :
  R.v4541 (state s) (inputs i) = Zmod.unsigned (N.v4541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4541 s i)) at 1.
  unfold R.v4541, N.v4541.
  rewrite ?node_4540.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2005_nr_5F2020.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2005_nr_5F2020 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4542 (s : N.State) (i : N.Inputs) :
  R.v4542 (state s) (inputs i) = Zmod.unsigned (N.v4542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4542 s i)) at 1.
  unfold R.v4542, N.v4542.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4543 (s : N.State) (i : N.Inputs) :
  R.v4543 (state s) (inputs i) = Zmod.unsigned (N.v4543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4543 s i)) at 1.
  unfold R.v4543, N.v4543.
  rewrite ?node_4542.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2006_nr_5F2021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2006_nr_5F2021 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4544 (s : N.State) (i : N.Inputs) :
  R.v4544 (state s) (inputs i) = Zmod.unsigned (N.v4544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4544 s i)) at 1.
  unfold R.v4544, N.v4544.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4545 (s : N.State) (i : N.Inputs) :
  R.v4545 (state s) (inputs i) = Zmod.unsigned (N.v4545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4545 s i)) at 1.
  unfold R.v4545, N.v4545.
  rewrite ?node_4544.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2007_nr_5F2023.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2007_nr_5F2023 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4546 (s : N.State) (i : N.Inputs) :
  R.v4546 (state s) (inputs i) = Zmod.unsigned (N.v4546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4546 s i)) at 1.
  unfold R.v4546, N.v4546.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4547 (s : N.State) (i : N.Inputs) :
  R.v4547 (state s) (inputs i) = Zmod.unsigned (N.v4547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4547 s i)) at 1.
  unfold R.v4547, N.v4547.
  rewrite ?node_4546.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2008_nr_5F2024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2008_nr_5F2024 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4548 (s : N.State) (i : N.Inputs) :
  R.v4548 (state s) (inputs i) = Zmod.unsigned (N.v4548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4548 s i)) at 1.
  unfold R.v4548, N.v4548.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4549 (s : N.State) (i : N.Inputs) :
  R.v4549 (state s) (inputs i) = Zmod.unsigned (N.v4549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4549 s i)) at 1.
  unfold R.v4549, N.v4549.
  rewrite ?node_4548.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2009_nr_5F2025.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2009_nr_5F2025 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4550 (s : N.State) (i : N.Inputs) :
  R.v4550 (state s) (inputs i) = Zmod.unsigned (N.v4550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4550 s i)) at 1.
  unfold R.v4550, N.v4550.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4551 (s : N.State) (i : N.Inputs) :
  R.v4551 (state s) (inputs i) = Zmod.unsigned (N.v4551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4551 s i)) at 1.
  unfold R.v4551, N.v4551.
  rewrite ?node_4550.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2010_nr_5F2026.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2010_nr_5F2026 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4552 (s : N.State) (i : N.Inputs) :
  R.v4552 (state s) (inputs i) = Zmod.unsigned (N.v4552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4552 s i)) at 1.
  unfold R.v4552, N.v4552.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4553 (s : N.State) (i : N.Inputs) :
  R.v4553 (state s) (inputs i) = Zmod.unsigned (N.v4553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4553 s i)) at 1.
  unfold R.v4553, N.v4553.
  rewrite ?node_4552.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2011_nr_5F2027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2011_nr_5F2027 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4554 (s : N.State) (i : N.Inputs) :
  R.v4554 (state s) (inputs i) = Zmod.unsigned (N.v4554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4554 s i)) at 1.
  unfold R.v4554, N.v4554.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4555 (s : N.State) (i : N.Inputs) :
  R.v4555 (state s) (inputs i) = Zmod.unsigned (N.v4555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4555 s i)) at 1.
  unfold R.v4555, N.v4555.
  rewrite ?node_4554.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2012_nr_5F2028.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2012_nr_5F2028 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4556 (s : N.State) (i : N.Inputs) :
  R.v4556 (state s) (inputs i) = Zmod.unsigned (N.v4556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4556 s i)) at 1.
  unfold R.v4556, N.v4556.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4557 (s : N.State) (i : N.Inputs) :
  R.v4557 (state s) (inputs i) = Zmod.unsigned (N.v4557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4557 s i)) at 1.
  unfold R.v4557, N.v4557.
  rewrite ?node_4556.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2013_nr_5F2029.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2013_nr_5F2029 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4558 (s : N.State) (i : N.Inputs) :
  R.v4558 (state s) (inputs i) = Zmod.unsigned (N.v4558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4558 s i)) at 1.
  unfold R.v4558, N.v4558.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4559 (s : N.State) (i : N.Inputs) :
  R.v4559 (state s) (inputs i) = Zmod.unsigned (N.v4559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4559 s i)) at 1.
  unfold R.v4559, N.v4559.
  rewrite ?node_4558.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2014_nr_5F2030.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2014_nr_5F2030 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4560 (s : N.State) (i : N.Inputs) :
  R.v4560 (state s) (inputs i) = Zmod.unsigned (N.v4560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4560 s i)) at 1.
  unfold R.v4560, N.v4560.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4561 (s : N.State) (i : N.Inputs) :
  R.v4561 (state s) (inputs i) = Zmod.unsigned (N.v4561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4561 s i)) at 1.
  unfold R.v4561, N.v4561.
  rewrite ?node_4560.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2015_nr_5F2031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2015_nr_5F2031 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4562 (s : N.State) (i : N.Inputs) :
  R.v4562 (state s) (inputs i) = Zmod.unsigned (N.v4562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4562 s i)) at 1.
  unfold R.v4562, N.v4562.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4563 (s : N.State) (i : N.Inputs) :
  R.v4563 (state s) (inputs i) = Zmod.unsigned (N.v4563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4563 s i)) at 1.
  unfold R.v4563, N.v4563.
  rewrite ?node_4562.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2016_nr_5F2032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2016_nr_5F2032 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4564 (s : N.State) (i : N.Inputs) :
  R.v4564 (state s) (inputs i) = Zmod.unsigned (N.v4564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4564 s i)) at 1.
  unfold R.v4564, N.v4564.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4565 (s : N.State) (i : N.Inputs) :
  R.v4565 (state s) (inputs i) = Zmod.unsigned (N.v4565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4565 s i)) at 1.
  unfold R.v4565, N.v4565.
  rewrite ?node_4564.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2017_nr_5F2033.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2017_nr_5F2033 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4566 (s : N.State) (i : N.Inputs) :
  R.v4566 (state s) (inputs i) = Zmod.unsigned (N.v4566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4566 s i)) at 1.
  unfold R.v4566, N.v4566.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4567 (s : N.State) (i : N.Inputs) :
  R.v4567 (state s) (inputs i) = Zmod.unsigned (N.v4567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4567 s i)) at 1.
  unfold R.v4567, N.v4567.
  rewrite ?node_4566.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2018_nr_5F2034.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2018_nr_5F2034 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4568 (s : N.State) (i : N.Inputs) :
  R.v4568 (state s) (inputs i) = Zmod.unsigned (N.v4568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4568 s i)) at 1.
  unfold R.v4568, N.v4568.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4569 (s : N.State) (i : N.Inputs) :
  R.v4569 (state s) (inputs i) = Zmod.unsigned (N.v4569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4569 s i)) at 1.
  unfold R.v4569, N.v4569.
  rewrite ?node_4568.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2019_nr_5F2035.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2019_nr_5F2035 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4570 (s : N.State) (i : N.Inputs) :
  R.v4570 (state s) (inputs i) = Zmod.unsigned (N.v4570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4570 s i)) at 1.
  unfold R.v4570, N.v4570.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4571 (s : N.State) (i : N.Inputs) :
  R.v4571 (state s) (inputs i) = Zmod.unsigned (N.v4571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4571 s i)) at 1.
  unfold R.v4571, N.v4571.
  rewrite ?node_4570.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2020_nr_5F2036.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2020_nr_5F2036 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4572 (s : N.State) (i : N.Inputs) :
  R.v4572 (state s) (inputs i) = Zmod.unsigned (N.v4572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4572 s i)) at 1.
  unfold R.v4572, N.v4572.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4573 (s : N.State) (i : N.Inputs) :
  R.v4573 (state s) (inputs i) = Zmod.unsigned (N.v4573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4573 s i)) at 1.
  unfold R.v4573, N.v4573.
  rewrite ?node_4572.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2021_nr_5F2037.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2021_nr_5F2037 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4574 (s : N.State) (i : N.Inputs) :
  R.v4574 (state s) (inputs i) = Zmod.unsigned (N.v4574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4574 s i)) at 1.
  unfold R.v4574, N.v4574.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4575 (s : N.State) (i : N.Inputs) :
  R.v4575 (state s) (inputs i) = Zmod.unsigned (N.v4575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4575 s i)) at 1.
  unfold R.v4575, N.v4575.
  rewrite ?node_4574.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2022_nr_5F2038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2022_nr_5F2038 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4576 (s : N.State) (i : N.Inputs) :
  R.v4576 (state s) (inputs i) = Zmod.unsigned (N.v4576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4576 s i)) at 1.
  unfold R.v4576, N.v4576.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4577 (s : N.State) (i : N.Inputs) :
  R.v4577 (state s) (inputs i) = Zmod.unsigned (N.v4577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4577 s i)) at 1.
  unfold R.v4577, N.v4577.
  unfold R.v3021, N.v3021.
  rewrite ?node_4576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4578 (s : N.State) (i : N.Inputs) :
  R.v4578 (state s) (inputs i) = Zmod.unsigned (N.v4578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4578 s i)) at 1.
  unfold R.v4578, N.v4578.
  rewrite ?node_4577.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2023_nr_5F2039.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2023_nr_5F2039 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4579 (s : N.State) (i : N.Inputs) :
  R.v4579 (state s) (inputs i) = Zmod.unsigned (N.v4579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4579 s i)) at 1.
  unfold R.v4579, N.v4579.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4580 (s : N.State) (i : N.Inputs) :
  R.v4580 (state s) (inputs i) = Zmod.unsigned (N.v4580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4580 s i)) at 1.
  unfold R.v4580, N.v4580.
  rewrite ?node_4579.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2024_nr_5F2040.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2024_nr_5F2040 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4581 (s : N.State) (i : N.Inputs) :
  R.v4581 (state s) (inputs i) = Zmod.unsigned (N.v4581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4581 s i)) at 1.
  unfold R.v4581, N.v4581.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4582 (s : N.State) (i : N.Inputs) :
  R.v4582 (state s) (inputs i) = Zmod.unsigned (N.v4582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4582 s i)) at 1.
  unfold R.v4582, N.v4582.
  rewrite ?node_4581.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2025_nr_5F2041.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2025_nr_5F2041 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4583 (s : N.State) (i : N.Inputs) :
  R.v4583 (state s) (inputs i) = Zmod.unsigned (N.v4583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4583 s i)) at 1.
  unfold R.v4583, N.v4583.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4584 (s : N.State) (i : N.Inputs) :
  R.v4584 (state s) (inputs i) = Zmod.unsigned (N.v4584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4584 s i)) at 1.
  unfold R.v4584, N.v4584.
  rewrite ?node_4583.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2026_nr_5F2042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2026_nr_5F2042 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4585 (s : N.State) (i : N.Inputs) :
  R.v4585 (state s) (inputs i) = Zmod.unsigned (N.v4585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4585 s i)) at 1.
  unfold R.v4585, N.v4585.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4586 (s : N.State) (i : N.Inputs) :
  R.v4586 (state s) (inputs i) = Zmod.unsigned (N.v4586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4586 s i)) at 1.
  unfold R.v4586, N.v4586.
  rewrite ?node_4585.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2027_nr_5F2043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2027_nr_5F2043 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4587 (s : N.State) (i : N.Inputs) :
  R.v4587 (state s) (inputs i) = Zmod.unsigned (N.v4587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4587 s i)) at 1.
  unfold R.v4587, N.v4587.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4588 (s : N.State) (i : N.Inputs) :
  R.v4588 (state s) (inputs i) = Zmod.unsigned (N.v4588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4588 s i)) at 1.
  unfold R.v4588, N.v4588.
  rewrite ?node_4587.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2028_nr_5F2044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2028_nr_5F2044 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4589 (s : N.State) (i : N.Inputs) :
  R.v4589 (state s) (inputs i) = Zmod.unsigned (N.v4589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4589 s i)) at 1.
  unfold R.v4589, N.v4589.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4590 (s : N.State) (i : N.Inputs) :
  R.v4590 (state s) (inputs i) = Zmod.unsigned (N.v4590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4590 s i)) at 1.
  unfold R.v4590, N.v4590.
  rewrite ?node_4589.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2029_nr_5F2045.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2029_nr_5F2045 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4591 (s : N.State) (i : N.Inputs) :
  R.v4591 (state s) (inputs i) = Zmod.unsigned (N.v4591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4591 s i)) at 1.
  unfold R.v4591, N.v4591.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4592 (s : N.State) (i : N.Inputs) :
  R.v4592 (state s) (inputs i) = Zmod.unsigned (N.v4592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4592 s i)) at 1.
  unfold R.v4592, N.v4592.
  rewrite ?node_4591.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2030_nr_5F2046.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2030_nr_5F2046 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4593 (s : N.State) (i : N.Inputs) :
  R.v4593 (state s) (inputs i) = Zmod.unsigned (N.v4593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4593 s i)) at 1.
  unfold R.v4593, N.v4593.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4594 (s : N.State) (i : N.Inputs) :
  R.v4594 (state s) (inputs i) = Zmod.unsigned (N.v4594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4594 s i)) at 1.
  unfold R.v4594, N.v4594.
  rewrite ?node_4593.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2031_nr_5F2047.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2031_nr_5F2047 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4595 (s : N.State) (i : N.Inputs) :
  R.v4595 (state s) (inputs i) = Zmod.unsigned (N.v4595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4595 s i)) at 1.
  unfold R.v4595, N.v4595.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4596 (s : N.State) (i : N.Inputs) :
  R.v4596 (state s) (inputs i) = Zmod.unsigned (N.v4596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4596 s i)) at 1.
  unfold R.v4596, N.v4596.
  rewrite ?node_4595.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2032_nr_5F2048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2032_nr_5F2048 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4597 (s : N.State) (i : N.Inputs) :
  R.v4597 (state s) (inputs i) = Zmod.unsigned (N.v4597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4597 s i)) at 1.
  unfold R.v4597, N.v4597.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4598 (s : N.State) (i : N.Inputs) :
  R.v4598 (state s) (inputs i) = Zmod.unsigned (N.v4598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4598 s i)) at 1.
  unfold R.v4598, N.v4598.
  rewrite ?node_4597.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2033_nr_5F2049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2033_nr_5F2049 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4599 (s : N.State) (i : N.Inputs) :
  R.v4599 (state s) (inputs i) = Zmod.unsigned (N.v4599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4599 s i)) at 1.
  unfold R.v4599, N.v4599.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4600 (s : N.State) (i : N.Inputs) :
  R.v4600 (state s) (inputs i) = Zmod.unsigned (N.v4600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4600 s i)) at 1.
  unfold R.v4600, N.v4600.
  rewrite ?node_4599.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2034_nr_5F2050.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2034_nr_5F2050 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4601 (s : N.State) (i : N.Inputs) :
  R.v4601 (state s) (inputs i) = Zmod.unsigned (N.v4601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4601 s i)) at 1.
  unfold R.v4601, N.v4601.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4602 (s : N.State) (i : N.Inputs) :
  R.v4602 (state s) (inputs i) = Zmod.unsigned (N.v4602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4602 s i)) at 1.
  unfold R.v4602, N.v4602.
  rewrite ?node_4601.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2035_nr_5F2051.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2035_nr_5F2051 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4603 (s : N.State) (i : N.Inputs) :
  R.v4603 (state s) (inputs i) = Zmod.unsigned (N.v4603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4603 s i)) at 1.
  unfold R.v4603, N.v4603.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4604 (s : N.State) (i : N.Inputs) :
  R.v4604 (state s) (inputs i) = Zmod.unsigned (N.v4604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4604 s i)) at 1.
  unfold R.v4604, N.v4604.
  rewrite ?node_4603.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2036_nr_5F2052.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2036_nr_5F2052 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4605 (s : N.State) (i : N.Inputs) :
  R.v4605 (state s) (inputs i) = Zmod.unsigned (N.v4605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4605 s i)) at 1.
  unfold R.v4605, N.v4605.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4606 (s : N.State) (i : N.Inputs) :
  R.v4606 (state s) (inputs i) = Zmod.unsigned (N.v4606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4606 s i)) at 1.
  unfold R.v4606, N.v4606.
  rewrite ?node_4605.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2037_nr_5F2053.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2037_nr_5F2053 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4607 (s : N.State) (i : N.Inputs) :
  R.v4607 (state s) (inputs i) = Zmod.unsigned (N.v4607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4607 s i)) at 1.
  unfold R.v4607, N.v4607.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4608 (s : N.State) (i : N.Inputs) :
  R.v4608 (state s) (inputs i) = Zmod.unsigned (N.v4608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4608 s i)) at 1.
  unfold R.v4608, N.v4608.
  rewrite ?node_4607.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2038_nr_5F2054.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2038_nr_5F2054 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4609 (s : N.State) (i : N.Inputs) :
  R.v4609 (state s) (inputs i) = Zmod.unsigned (N.v4609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4609 s i)) at 1.
  unfold R.v4609, N.v4609.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4610 (s : N.State) (i : N.Inputs) :
  R.v4610 (state s) (inputs i) = Zmod.unsigned (N.v4610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4610 s i)) at 1.
  unfold R.v4610, N.v4610.
  rewrite ?node_4609.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2039_nr_5F2056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2039_nr_5F2056 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4611 (s : N.State) (i : N.Inputs) :
  R.v4611 (state s) (inputs i) = Zmod.unsigned (N.v4611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4611 s i)) at 1.
  unfold R.v4611, N.v4611.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4612 (s : N.State) (i : N.Inputs) :
  R.v4612 (state s) (inputs i) = Zmod.unsigned (N.v4612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4612 s i)) at 1.
  unfold R.v4612, N.v4612.
  rewrite ?node_4611.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2040_nr_5F2057.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2040_nr_5F2057 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4613 (s : N.State) (i : N.Inputs) :
  R.v4613 (state s) (inputs i) = Zmod.unsigned (N.v4613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4613 s i)) at 1.
  unfold R.v4613, N.v4613.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4614 (s : N.State) (i : N.Inputs) :
  R.v4614 (state s) (inputs i) = Zmod.unsigned (N.v4614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4614 s i)) at 1.
  unfold R.v4614, N.v4614.
  rewrite ?node_4613.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2041_nr_5F2058.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2041_nr_5F2058 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4615 (s : N.State) (i : N.Inputs) :
  R.v4615 (state s) (inputs i) = Zmod.unsigned (N.v4615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4615 s i)) at 1.
  unfold R.v4615, N.v4615.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4616 (s : N.State) (i : N.Inputs) :
  R.v4616 (state s) (inputs i) = Zmod.unsigned (N.v4616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4616 s i)) at 1.
  unfold R.v4616, N.v4616.
  rewrite ?node_4615.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2042_nr_5F2059.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2042_nr_5F2059 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4617 (s : N.State) (i : N.Inputs) :
  R.v4617 (state s) (inputs i) = Zmod.unsigned (N.v4617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4617 s i)) at 1.
  unfold R.v4617, N.v4617.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4618 (s : N.State) (i : N.Inputs) :
  R.v4618 (state s) (inputs i) = Zmod.unsigned (N.v4618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4618 s i)) at 1.
  unfold R.v4618, N.v4618.
  rewrite ?node_4617.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2043_nr_5F2060.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2043_nr_5F2060 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4619 (s : N.State) (i : N.Inputs) :
  R.v4619 (state s) (inputs i) = Zmod.unsigned (N.v4619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4619 s i)) at 1.
  unfold R.v4619, N.v4619.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4620 (s : N.State) (i : N.Inputs) :
  R.v4620 (state s) (inputs i) = Zmod.unsigned (N.v4620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4620 s i)) at 1.
  unfold R.v4620, N.v4620.
  rewrite ?node_4619.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2044_nr_5F2061.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2044_nr_5F2061 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4621 (s : N.State) (i : N.Inputs) :
  R.v4621 (state s) (inputs i) = Zmod.unsigned (N.v4621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4621 s i)) at 1.
  unfold R.v4621, N.v4621.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4622 (s : N.State) (i : N.Inputs) :
  R.v4622 (state s) (inputs i) = Zmod.unsigned (N.v4622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4622 s i)) at 1.
  unfold R.v4622, N.v4622.
  rewrite ?node_4621.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2045_nr_5F2062.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2045_nr_5F2062 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4623 (s : N.State) (i : N.Inputs) :
  R.v4623 (state s) (inputs i) = Zmod.unsigned (N.v4623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4623 s i)) at 1.
  unfold R.v4623, N.v4623.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4624 (s : N.State) (i : N.Inputs) :
  R.v4624 (state s) (inputs i) = Zmod.unsigned (N.v4624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4624 s i)) at 1.
  unfold R.v4624, N.v4624.
  rewrite ?node_4623.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2046_nr_5F2063.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2046_nr_5F2063 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4625 (s : N.State) (i : N.Inputs) :
  R.v4625 (state s) (inputs i) = Zmod.unsigned (N.v4625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4625 s i)) at 1.
  unfold R.v4625, N.v4625.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4626 (s : N.State) (i : N.Inputs) :
  R.v4626 (state s) (inputs i) = Zmod.unsigned (N.v4626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4626 s i)) at 1.
  unfold R.v4626, N.v4626.
  rewrite ?node_4625.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2047_nr_5F2064.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2047_nr_5F2064 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4627 (s : N.State) (i : N.Inputs) :
  R.v4627 (state s) (inputs i) = Zmod.unsigned (N.v4627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4627 s i)) at 1.
  unfold R.v4627, N.v4627.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4628 (s : N.State) (i : N.Inputs) :
  R.v4628 (state s) (inputs i) = Zmod.unsigned (N.v4628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4628 s i)) at 1.
  unfold R.v4628, N.v4628.
  rewrite ?node_4627.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2048_nr_5F2065.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2048_nr_5F2065 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4629 (s : N.State) (i : N.Inputs) :
  R.v4629 (state s) (inputs i) = Zmod.unsigned (N.v4629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4629 s i)) at 1.
  unfold R.v4629, N.v4629.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4630 (s : N.State) (i : N.Inputs) :
  R.v4630 (state s) (inputs i) = Zmod.unsigned (N.v4630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4630 s i)) at 1.
  unfold R.v4630, N.v4630.
  rewrite ?node_4629.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2049_nr_5F2066.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2049_nr_5F2066 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4631 (s : N.State) (i : N.Inputs) :
  R.v4631 (state s) (inputs i) = Zmod.unsigned (N.v4631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4631 s i)) at 1.
  unfold R.v4631, N.v4631.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4632 (s : N.State) (i : N.Inputs) :
  R.v4632 (state s) (inputs i) = Zmod.unsigned (N.v4632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4632 s i)) at 1.
  unfold R.v4632, N.v4632.
  rewrite ?node_4631.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2050_nr_5F2067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2050_nr_5F2067 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4633 (s : N.State) (i : N.Inputs) :
  R.v4633 (state s) (inputs i) = Zmod.unsigned (N.v4633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4633 s i)) at 1.
  unfold R.v4633, N.v4633.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4634 (s : N.State) (i : N.Inputs) :
  R.v4634 (state s) (inputs i) = Zmod.unsigned (N.v4634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4634 s i)) at 1.
  unfold R.v4634, N.v4634.
  rewrite ?node_4633.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2051_nr_5F2068.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2051_nr_5F2068 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4635 (s : N.State) (i : N.Inputs) :
  R.v4635 (state s) (inputs i) = Zmod.unsigned (N.v4635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4635 s i)) at 1.
  unfold R.v4635, N.v4635.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4636 (s : N.State) (i : N.Inputs) :
  R.v4636 (state s) (inputs i) = Zmod.unsigned (N.v4636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4636 s i)) at 1.
  unfold R.v4636, N.v4636.
  rewrite ?node_4635.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2052_nr_5F2069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2052_nr_5F2069 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4637 (s : N.State) (i : N.Inputs) :
  R.v4637 (state s) (inputs i) = Zmod.unsigned (N.v4637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4637 s i)) at 1.
  unfold R.v4637, N.v4637.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4638 (s : N.State) (i : N.Inputs) :
  R.v4638 (state s) (inputs i) = Zmod.unsigned (N.v4638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4638 s i)) at 1.
  unfold R.v4638, N.v4638.
  rewrite ?node_4637.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2053_nr_5F2070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2053_nr_5F2070 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4639 (s : N.State) (i : N.Inputs) :
  R.v4639 (state s) (inputs i) = Zmod.unsigned (N.v4639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4639 s i)) at 1.
  unfold R.v4639, N.v4639.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4640 (s : N.State) (i : N.Inputs) :
  R.v4640 (state s) (inputs i) = Zmod.unsigned (N.v4640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4640 s i)) at 1.
  unfold R.v4640, N.v4640.
  unfold R.v3021, N.v3021.
  rewrite ?node_4639.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4641 (s : N.State) (i : N.Inputs) :
  R.v4641 (state s) (inputs i) = Zmod.unsigned (N.v4641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4641 s i)) at 1.
  unfold R.v4641, N.v4641.
  rewrite ?node_4640.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2054_nr_5F2071.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2054_nr_5F2071 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4642 (s : N.State) (i : N.Inputs) :
  R.v4642 (state s) (inputs i) = Zmod.unsigned (N.v4642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4642 s i)) at 1.
  unfold R.v4642, N.v4642.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4643 (s : N.State) (i : N.Inputs) :
  R.v4643 (state s) (inputs i) = Zmod.unsigned (N.v4643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4643 s i)) at 1.
  unfold R.v4643, N.v4643.
  rewrite ?node_4642.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2055_nr_5F2072.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2055_nr_5F2072 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4644 (s : N.State) (i : N.Inputs) :
  R.v4644 (state s) (inputs i) = Zmod.unsigned (N.v4644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4644 s i)) at 1.
  unfold R.v4644, N.v4644.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4645 (s : N.State) (i : N.Inputs) :
  R.v4645 (state s) (inputs i) = Zmod.unsigned (N.v4645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4645 s i)) at 1.
  unfold R.v4645, N.v4645.
  rewrite ?node_4644.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2056_nr_5F2073.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2056_nr_5F2073 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4646 (s : N.State) (i : N.Inputs) :
  R.v4646 (state s) (inputs i) = Zmod.unsigned (N.v4646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4646 s i)) at 1.
  unfold R.v4646, N.v4646.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4647 (s : N.State) (i : N.Inputs) :
  R.v4647 (state s) (inputs i) = Zmod.unsigned (N.v4647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4647 s i)) at 1.
  unfold R.v4647, N.v4647.
  rewrite ?node_4646.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2057_nr_5F2074.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2057_nr_5F2074 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4648 (s : N.State) (i : N.Inputs) :
  R.v4648 (state s) (inputs i) = Zmod.unsigned (N.v4648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4648 s i)) at 1.
  unfold R.v4648, N.v4648.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4649 (s : N.State) (i : N.Inputs) :
  R.v4649 (state s) (inputs i) = Zmod.unsigned (N.v4649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4649 s i)) at 1.
  unfold R.v4649, N.v4649.
  rewrite ?node_4648.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2058_nr_5F2075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2058_nr_5F2075 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4650 (s : N.State) (i : N.Inputs) :
  R.v4650 (state s) (inputs i) = Zmod.unsigned (N.v4650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4650 s i)) at 1.
  unfold R.v4650, N.v4650.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4651 (s : N.State) (i : N.Inputs) :
  R.v4651 (state s) (inputs i) = Zmod.unsigned (N.v4651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4651 s i)) at 1.
  unfold R.v4651, N.v4651.
  rewrite ?node_4650.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2059_nr_5F2076.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2059_nr_5F2076 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4652 (s : N.State) (i : N.Inputs) :
  R.v4652 (state s) (inputs i) = Zmod.unsigned (N.v4652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4652 s i)) at 1.
  unfold R.v4652, N.v4652.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4653 (s : N.State) (i : N.Inputs) :
  R.v4653 (state s) (inputs i) = Zmod.unsigned (N.v4653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4653 s i)) at 1.
  unfold R.v4653, N.v4653.
  rewrite ?node_4652.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2060_nr_5F2077.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2060_nr_5F2077 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4654 (s : N.State) (i : N.Inputs) :
  R.v4654 (state s) (inputs i) = Zmod.unsigned (N.v4654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4654 s i)) at 1.
  unfold R.v4654, N.v4654.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4655 (s : N.State) (i : N.Inputs) :
  R.v4655 (state s) (inputs i) = Zmod.unsigned (N.v4655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4655 s i)) at 1.
  unfold R.v4655, N.v4655.
  rewrite ?node_4654.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2061_nr_5F2078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2061_nr_5F2078 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4656 (s : N.State) (i : N.Inputs) :
  R.v4656 (state s) (inputs i) = Zmod.unsigned (N.v4656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4656 s i)) at 1.
  unfold R.v4656, N.v4656.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4657 (s : N.State) (i : N.Inputs) :
  R.v4657 (state s) (inputs i) = Zmod.unsigned (N.v4657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4657 s i)) at 1.
  unfold R.v4657, N.v4657.
  rewrite ?node_4656.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2062_nr_5F2079.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2062_nr_5F2079 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4658 (s : N.State) (i : N.Inputs) :
  R.v4658 (state s) (inputs i) = Zmod.unsigned (N.v4658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4658 s i)) at 1.
  unfold R.v4658, N.v4658.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4659 (s : N.State) (i : N.Inputs) :
  R.v4659 (state s) (inputs i) = Zmod.unsigned (N.v4659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4659 s i)) at 1.
  unfold R.v4659, N.v4659.
  rewrite ?node_4658.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2063_nr_5F2080.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2063_nr_5F2080 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4660 (s : N.State) (i : N.Inputs) :
  R.v4660 (state s) (inputs i) = Zmod.unsigned (N.v4660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4660 s i)) at 1.
  unfold R.v4660, N.v4660.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4661 (s : N.State) (i : N.Inputs) :
  R.v4661 (state s) (inputs i) = Zmod.unsigned (N.v4661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4661 s i)) at 1.
  unfold R.v4661, N.v4661.
  rewrite ?node_4660.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2064_nr_5F2081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2064_nr_5F2081 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4662 (s : N.State) (i : N.Inputs) :
  R.v4662 (state s) (inputs i) = Zmod.unsigned (N.v4662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4662 s i)) at 1.
  unfold R.v4662, N.v4662.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4663 (s : N.State) (i : N.Inputs) :
  R.v4663 (state s) (inputs i) = Zmod.unsigned (N.v4663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4663 s i)) at 1.
  unfold R.v4663, N.v4663.
  rewrite ?node_4662.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2065_nr_5F2082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2065_nr_5F2082 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4664 (s : N.State) (i : N.Inputs) :
  R.v4664 (state s) (inputs i) = Zmod.unsigned (N.v4664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4664 s i)) at 1.
  unfold R.v4664, N.v4664.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4665 (s : N.State) (i : N.Inputs) :
  R.v4665 (state s) (inputs i) = Zmod.unsigned (N.v4665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4665 s i)) at 1.
  unfold R.v4665, N.v4665.
  rewrite ?node_4664.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2066_nr_5F2083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2066_nr_5F2083 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4666 (s : N.State) (i : N.Inputs) :
  R.v4666 (state s) (inputs i) = Zmod.unsigned (N.v4666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4666 s i)) at 1.
  unfold R.v4666, N.v4666.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4667 (s : N.State) (i : N.Inputs) :
  R.v4667 (state s) (inputs i) = Zmod.unsigned (N.v4667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4667 s i)) at 1.
  unfold R.v4667, N.v4667.
  rewrite ?node_4666.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2067_nr_5F2084.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2067_nr_5F2084 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4668 (s : N.State) (i : N.Inputs) :
  R.v4668 (state s) (inputs i) = Zmod.unsigned (N.v4668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4668 s i)) at 1.
  unfold R.v4668, N.v4668.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4669 (s : N.State) (i : N.Inputs) :
  R.v4669 (state s) (inputs i) = Zmod.unsigned (N.v4669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4669 s i)) at 1.
  unfold R.v4669, N.v4669.
  rewrite ?node_4668.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2068_nr_5F2085.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2068_nr_5F2085 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4670 (s : N.State) (i : N.Inputs) :
  R.v4670 (state s) (inputs i) = Zmod.unsigned (N.v4670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4670 s i)) at 1.
  unfold R.v4670, N.v4670.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4671 (s : N.State) (i : N.Inputs) :
  R.v4671 (state s) (inputs i) = Zmod.unsigned (N.v4671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4671 s i)) at 1.
  unfold R.v4671, N.v4671.
  rewrite ?node_4670.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2069_nr_5F2087.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2069_nr_5F2087 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4672 (s : N.State) (i : N.Inputs) :
  R.v4672 (state s) (inputs i) = Zmod.unsigned (N.v4672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4672 s i)) at 1.
  unfold R.v4672, N.v4672.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4673 (s : N.State) (i : N.Inputs) :
  R.v4673 (state s) (inputs i) = Zmod.unsigned (N.v4673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4673 s i)) at 1.
  unfold R.v4673, N.v4673.
  rewrite ?node_4672.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2070_nr_5F2088.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2070_nr_5F2088 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4674 (s : N.State) (i : N.Inputs) :
  R.v4674 (state s) (inputs i) = Zmod.unsigned (N.v4674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4674 s i)) at 1.
  unfold R.v4674, N.v4674.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4675 (s : N.State) (i : N.Inputs) :
  R.v4675 (state s) (inputs i) = Zmod.unsigned (N.v4675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4675 s i)) at 1.
  unfold R.v4675, N.v4675.
  rewrite ?node_4674.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2071_nr_5F2089.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2071_nr_5F2089 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4676 (s : N.State) (i : N.Inputs) :
  R.v4676 (state s) (inputs i) = Zmod.unsigned (N.v4676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4676 s i)) at 1.
  unfold R.v4676, N.v4676.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4677 (s : N.State) (i : N.Inputs) :
  R.v4677 (state s) (inputs i) = Zmod.unsigned (N.v4677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4677 s i)) at 1.
  unfold R.v4677, N.v4677.
  rewrite ?node_4676.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2072_nr_5F2090.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2072_nr_5F2090 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4678 (s : N.State) (i : N.Inputs) :
  R.v4678 (state s) (inputs i) = Zmod.unsigned (N.v4678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4678 s i)) at 1.
  unfold R.v4678, N.v4678.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4679 (s : N.State) (i : N.Inputs) :
  R.v4679 (state s) (inputs i) = Zmod.unsigned (N.v4679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4679 s i)) at 1.
  unfold R.v4679, N.v4679.
  rewrite ?node_4678.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2073_nr_5F2091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2073_nr_5F2091 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4680 (s : N.State) (i : N.Inputs) :
  R.v4680 (state s) (inputs i) = Zmod.unsigned (N.v4680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4680 s i)) at 1.
  unfold R.v4680, N.v4680.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4681 (s : N.State) (i : N.Inputs) :
  R.v4681 (state s) (inputs i) = Zmod.unsigned (N.v4681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4681 s i)) at 1.
  unfold R.v4681, N.v4681.
  rewrite ?node_4680.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2074_nr_5F2092.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2074_nr_5F2092 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4682 (s : N.State) (i : N.Inputs) :
  R.v4682 (state s) (inputs i) = Zmod.unsigned (N.v4682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4682 s i)) at 1.
  unfold R.v4682, N.v4682.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4683 (s : N.State) (i : N.Inputs) :
  R.v4683 (state s) (inputs i) = Zmod.unsigned (N.v4683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4683 s i)) at 1.
  unfold R.v4683, N.v4683.
  rewrite ?node_4682.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2075_nr_5F2093.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2075_nr_5F2093 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4684 (s : N.State) (i : N.Inputs) :
  R.v4684 (state s) (inputs i) = Zmod.unsigned (N.v4684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4684 s i)) at 1.
  unfold R.v4684, N.v4684.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4685 (s : N.State) (i : N.Inputs) :
  R.v4685 (state s) (inputs i) = Zmod.unsigned (N.v4685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4685 s i)) at 1.
  unfold R.v4685, N.v4685.
  rewrite ?node_4684.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2076_nr_5F2094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2076_nr_5F2094 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4686 (s : N.State) (i : N.Inputs) :
  R.v4686 (state s) (inputs i) = Zmod.unsigned (N.v4686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4686 s i)) at 1.
  unfold R.v4686, N.v4686.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4687 (s : N.State) (i : N.Inputs) :
  R.v4687 (state s) (inputs i) = Zmod.unsigned (N.v4687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4687 s i)) at 1.
  unfold R.v4687, N.v4687.
  rewrite ?node_4686.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2077_nr_5F2095.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2077_nr_5F2095 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4688 (s : N.State) (i : N.Inputs) :
  R.v4688 (state s) (inputs i) = Zmod.unsigned (N.v4688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4688 s i)) at 1.
  unfold R.v4688, N.v4688.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4689 (s : N.State) (i : N.Inputs) :
  R.v4689 (state s) (inputs i) = Zmod.unsigned (N.v4689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4689 s i)) at 1.
  unfold R.v4689, N.v4689.
  rewrite ?node_4688.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2078_nr_5F2096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2078_nr_5F2096 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4690 (s : N.State) (i : N.Inputs) :
  R.v4690 (state s) (inputs i) = Zmod.unsigned (N.v4690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4690 s i)) at 1.
  unfold R.v4690, N.v4690.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4691 (s : N.State) (i : N.Inputs) :
  R.v4691 (state s) (inputs i) = Zmod.unsigned (N.v4691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4691 s i)) at 1.
  unfold R.v4691, N.v4691.
  rewrite ?node_4690.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2079_nr_5F2097.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2079_nr_5F2097 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4692 (s : N.State) (i : N.Inputs) :
  R.v4692 (state s) (inputs i) = Zmod.unsigned (N.v4692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4692 s i)) at 1.
  unfold R.v4692, N.v4692.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4693 (s : N.State) (i : N.Inputs) :
  R.v4693 (state s) (inputs i) = Zmod.unsigned (N.v4693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4693 s i)) at 1.
  unfold R.v4693, N.v4693.
  rewrite ?node_4692.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2080_nr_5F2098.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2080_nr_5F2098 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4694 (s : N.State) (i : N.Inputs) :
  R.v4694 (state s) (inputs i) = Zmod.unsigned (N.v4694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4694 s i)) at 1.
  unfold R.v4694, N.v4694.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4695 (s : N.State) (i : N.Inputs) :
  R.v4695 (state s) (inputs i) = Zmod.unsigned (N.v4695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4695 s i)) at 1.
  unfold R.v4695, N.v4695.
  rewrite ?node_4694.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2081_nr_5F2099.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2081_nr_5F2099 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4696 (s : N.State) (i : N.Inputs) :
  R.v4696 (state s) (inputs i) = Zmod.unsigned (N.v4696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4696 s i)) at 1.
  unfold R.v4696, N.v4696.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4697 (s : N.State) (i : N.Inputs) :
  R.v4697 (state s) (inputs i) = Zmod.unsigned (N.v4697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4697 s i)) at 1.
  unfold R.v4697, N.v4697.
  rewrite ?node_4696.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2082_nr_5F2100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2082_nr_5F2100 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4698 (s : N.State) (i : N.Inputs) :
  R.v4698 (state s) (inputs i) = Zmod.unsigned (N.v4698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4698 s i)) at 1.
  unfold R.v4698, N.v4698.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4699 (s : N.State) (i : N.Inputs) :
  R.v4699 (state s) (inputs i) = Zmod.unsigned (N.v4699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4699 s i)) at 1.
  unfold R.v4699, N.v4699.
  unfold R.v3021, N.v3021.
  rewrite ?node_4698.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4700 (s : N.State) (i : N.Inputs) :
  R.v4700 (state s) (inputs i) = Zmod.unsigned (N.v4700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4700 s i)) at 1.
  unfold R.v4700, N.v4700.
  rewrite ?node_4699.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2083_nr_5F2101.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2083_nr_5F2101 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4701 (s : N.State) (i : N.Inputs) :
  R.v4701 (state s) (inputs i) = Zmod.unsigned (N.v4701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4701 s i)) at 1.
  unfold R.v4701, N.v4701.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4702 (s : N.State) (i : N.Inputs) :
  R.v4702 (state s) (inputs i) = Zmod.unsigned (N.v4702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4702 s i)) at 1.
  unfold R.v4702, N.v4702.
  rewrite ?node_4701.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2084_nr_5F2102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2084_nr_5F2102 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4703 (s : N.State) (i : N.Inputs) :
  R.v4703 (state s) (inputs i) = Zmod.unsigned (N.v4703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4703 s i)) at 1.
  unfold R.v4703, N.v4703.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4704 (s : N.State) (i : N.Inputs) :
  R.v4704 (state s) (inputs i) = Zmod.unsigned (N.v4704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4704 s i)) at 1.
  unfold R.v4704, N.v4704.
  rewrite ?node_4703.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2085_nr_5F2103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2085_nr_5F2103 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4705 (s : N.State) (i : N.Inputs) :
  R.v4705 (state s) (inputs i) = Zmod.unsigned (N.v4705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4705 s i)) at 1.
  unfold R.v4705, N.v4705.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4706 (s : N.State) (i : N.Inputs) :
  R.v4706 (state s) (inputs i) = Zmod.unsigned (N.v4706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4706 s i)) at 1.
  unfold R.v4706, N.v4706.
  rewrite ?node_4705.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2086_nr_5F2104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2086_nr_5F2104 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4707 (s : N.State) (i : N.Inputs) :
  R.v4707 (state s) (inputs i) = Zmod.unsigned (N.v4707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4707 s i)) at 1.
  unfold R.v4707, N.v4707.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4708 (s : N.State) (i : N.Inputs) :
  R.v4708 (state s) (inputs i) = Zmod.unsigned (N.v4708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4708 s i)) at 1.
  unfold R.v4708, N.v4708.
  rewrite ?node_4707.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2087_nr_5F2105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2087_nr_5F2105 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4709 (s : N.State) (i : N.Inputs) :
  R.v4709 (state s) (inputs i) = Zmod.unsigned (N.v4709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4709 s i)) at 1.
  unfold R.v4709, N.v4709.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4710 (s : N.State) (i : N.Inputs) :
  R.v4710 (state s) (inputs i) = Zmod.unsigned (N.v4710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4710 s i)) at 1.
  unfold R.v4710, N.v4710.
  rewrite ?node_4709.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2088_nr_5F2106.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2088_nr_5F2106 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4711 (s : N.State) (i : N.Inputs) :
  R.v4711 (state s) (inputs i) = Zmod.unsigned (N.v4711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4711 s i)) at 1.
  unfold R.v4711, N.v4711.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4712 (s : N.State) (i : N.Inputs) :
  R.v4712 (state s) (inputs i) = Zmod.unsigned (N.v4712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4712 s i)) at 1.
  unfold R.v4712, N.v4712.
  rewrite ?node_4711.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2089_nr_5F2107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2089_nr_5F2107 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4713 (s : N.State) (i : N.Inputs) :
  R.v4713 (state s) (inputs i) = Zmod.unsigned (N.v4713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4713 s i)) at 1.
  unfold R.v4713, N.v4713.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4714 (s : N.State) (i : N.Inputs) :
  R.v4714 (state s) (inputs i) = Zmod.unsigned (N.v4714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4714 s i)) at 1.
  unfold R.v4714, N.v4714.
  rewrite ?node_4713.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2090_nr_5F2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2090_nr_5F2108 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4715 (s : N.State) (i : N.Inputs) :
  R.v4715 (state s) (inputs i) = Zmod.unsigned (N.v4715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4715 s i)) at 1.
  unfold R.v4715, N.v4715.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4716 (s : N.State) (i : N.Inputs) :
  R.v4716 (state s) (inputs i) = Zmod.unsigned (N.v4716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4716 s i)) at 1.
  unfold R.v4716, N.v4716.
  rewrite ?node_4715.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2091_nr_5F2109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2091_nr_5F2109 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4717 (s : N.State) (i : N.Inputs) :
  R.v4717 (state s) (inputs i) = Zmod.unsigned (N.v4717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4717 s i)) at 1.
  unfold R.v4717, N.v4717.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4718 (s : N.State) (i : N.Inputs) :
  R.v4718 (state s) (inputs i) = Zmod.unsigned (N.v4718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4718 s i)) at 1.
  unfold R.v4718, N.v4718.
  rewrite ?node_4717.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2092_nr_5F2110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2092_nr_5F2110 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4719 (s : N.State) (i : N.Inputs) :
  R.v4719 (state s) (inputs i) = Zmod.unsigned (N.v4719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4719 s i)) at 1.
  unfold R.v4719, N.v4719.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4720 (s : N.State) (i : N.Inputs) :
  R.v4720 (state s) (inputs i) = Zmod.unsigned (N.v4720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4720 s i)) at 1.
  unfold R.v4720, N.v4720.
  rewrite ?node_4719.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2093_nr_5F2111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2093_nr_5F2111 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4721 (s : N.State) (i : N.Inputs) :
  R.v4721 (state s) (inputs i) = Zmod.unsigned (N.v4721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4721 s i)) at 1.
  unfold R.v4721, N.v4721.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4722 (s : N.State) (i : N.Inputs) :
  R.v4722 (state s) (inputs i) = Zmod.unsigned (N.v4722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4722 s i)) at 1.
  unfold R.v4722, N.v4722.
  rewrite ?node_4721.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2094_nr_5F2112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2094_nr_5F2112 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4723 (s : N.State) (i : N.Inputs) :
  R.v4723 (state s) (inputs i) = Zmod.unsigned (N.v4723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4723 s i)) at 1.
  unfold R.v4723, N.v4723.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4724 (s : N.State) (i : N.Inputs) :
  R.v4724 (state s) (inputs i) = Zmod.unsigned (N.v4724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4724 s i)) at 1.
  unfold R.v4724, N.v4724.
  rewrite ?node_4723.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2095_nr_5F2113.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2095_nr_5F2113 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4725 (s : N.State) (i : N.Inputs) :
  R.v4725 (state s) (inputs i) = Zmod.unsigned (N.v4725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4725 s i)) at 1.
  unfold R.v4725, N.v4725.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4726 (s : N.State) (i : N.Inputs) :
  R.v4726 (state s) (inputs i) = Zmod.unsigned (N.v4726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4726 s i)) at 1.
  unfold R.v4726, N.v4726.
  rewrite ?node_4725.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2096_nr_5F2114.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2096_nr_5F2114 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4727 (s : N.State) (i : N.Inputs) :
  R.v4727 (state s) (inputs i) = Zmod.unsigned (N.v4727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4727 s i)) at 1.
  unfold R.v4727, N.v4727.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4728 (s : N.State) (i : N.Inputs) :
  R.v4728 (state s) (inputs i) = Zmod.unsigned (N.v4728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4728 s i)) at 1.
  unfold R.v4728, N.v4728.
  rewrite ?node_4727.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2097_nr_5F2116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2097_nr_5F2116 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4729 (s : N.State) (i : N.Inputs) :
  R.v4729 (state s) (inputs i) = Zmod.unsigned (N.v4729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4729 s i)) at 1.
  unfold R.v4729, N.v4729.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4730 (s : N.State) (i : N.Inputs) :
  R.v4730 (state s) (inputs i) = Zmod.unsigned (N.v4730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4730 s i)) at 1.
  unfold R.v4730, N.v4730.
  rewrite ?node_4729.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2098_nr_5F2117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2098_nr_5F2117 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4731 (s : N.State) (i : N.Inputs) :
  R.v4731 (state s) (inputs i) = Zmod.unsigned (N.v4731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4731 s i)) at 1.
  unfold R.v4731, N.v4731.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4732 (s : N.State) (i : N.Inputs) :
  R.v4732 (state s) (inputs i) = Zmod.unsigned (N.v4732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4732 s i)) at 1.
  unfold R.v4732, N.v4732.
  rewrite ?node_4731.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2099_nr_5F2118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2099_nr_5F2118 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4733 (s : N.State) (i : N.Inputs) :
  R.v4733 (state s) (inputs i) = Zmod.unsigned (N.v4733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4733 s i)) at 1.
  unfold R.v4733, N.v4733.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4734 (s : N.State) (i : N.Inputs) :
  R.v4734 (state s) (inputs i) = Zmod.unsigned (N.v4734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4734 s i)) at 1.
  unfold R.v4734, N.v4734.
  rewrite ?node_4733.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2100_nr_5F2119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2100_nr_5F2119 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4735 (s : N.State) (i : N.Inputs) :
  R.v4735 (state s) (inputs i) = Zmod.unsigned (N.v4735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4735 s i)) at 1.
  unfold R.v4735, N.v4735.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4736 (s : N.State) (i : N.Inputs) :
  R.v4736 (state s) (inputs i) = Zmod.unsigned (N.v4736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4736 s i)) at 1.
  unfold R.v4736, N.v4736.
  rewrite ?node_4735.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2101_nr_5F2120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2101_nr_5F2120 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4737 (s : N.State) (i : N.Inputs) :
  R.v4737 (state s) (inputs i) = Zmod.unsigned (N.v4737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4737 s i)) at 1.
  unfold R.v4737, N.v4737.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4738 (s : N.State) (i : N.Inputs) :
  R.v4738 (state s) (inputs i) = Zmod.unsigned (N.v4738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4738 s i)) at 1.
  unfold R.v4738, N.v4738.
  rewrite ?node_4737.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2102_nr_5F2121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2102_nr_5F2121 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4739 (s : N.State) (i : N.Inputs) :
  R.v4739 (state s) (inputs i) = Zmod.unsigned (N.v4739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4739 s i)) at 1.
  unfold R.v4739, N.v4739.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4740 (s : N.State) (i : N.Inputs) :
  R.v4740 (state s) (inputs i) = Zmod.unsigned (N.v4740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4740 s i)) at 1.
  unfold R.v4740, N.v4740.
  rewrite ?node_4739.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2103_nr_5F2122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2103_nr_5F2122 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4741 (s : N.State) (i : N.Inputs) :
  R.v4741 (state s) (inputs i) = Zmod.unsigned (N.v4741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4741 s i)) at 1.
  unfold R.v4741, N.v4741.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4742 (s : N.State) (i : N.Inputs) :
  R.v4742 (state s) (inputs i) = Zmod.unsigned (N.v4742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4742 s i)) at 1.
  unfold R.v4742, N.v4742.
  rewrite ?node_4741.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2104_nr_5F2123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2104_nr_5F2123 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4743 (s : N.State) (i : N.Inputs) :
  R.v4743 (state s) (inputs i) = Zmod.unsigned (N.v4743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4743 s i)) at 1.
  unfold R.v4743, N.v4743.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4744 (s : N.State) (i : N.Inputs) :
  R.v4744 (state s) (inputs i) = Zmod.unsigned (N.v4744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4744 s i)) at 1.
  unfold R.v4744, N.v4744.
  rewrite ?node_4743.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2105_nr_5F2124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2105_nr_5F2124 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4745 (s : N.State) (i : N.Inputs) :
  R.v4745 (state s) (inputs i) = Zmod.unsigned (N.v4745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4745 s i)) at 1.
  unfold R.v4745, N.v4745.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4746 (s : N.State) (i : N.Inputs) :
  R.v4746 (state s) (inputs i) = Zmod.unsigned (N.v4746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4746 s i)) at 1.
  unfold R.v4746, N.v4746.
  rewrite ?node_4745.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2106_nr_5F2125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2106_nr_5F2125 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4747 (s : N.State) (i : N.Inputs) :
  R.v4747 (state s) (inputs i) = Zmod.unsigned (N.v4747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4747 s i)) at 1.
  unfold R.v4747, N.v4747.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4748 (s : N.State) (i : N.Inputs) :
  R.v4748 (state s) (inputs i) = Zmod.unsigned (N.v4748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4748 s i)) at 1.
  unfold R.v4748, N.v4748.
  rewrite ?node_4747.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2107_nr_5F2126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2107_nr_5F2126 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4749 (s : N.State) (i : N.Inputs) :
  R.v4749 (state s) (inputs i) = Zmod.unsigned (N.v4749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4749 s i)) at 1.
  unfold R.v4749, N.v4749.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4750 (s : N.State) (i : N.Inputs) :
  R.v4750 (state s) (inputs i) = Zmod.unsigned (N.v4750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4750 s i)) at 1.
  unfold R.v4750, N.v4750.
  rewrite ?node_4749.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2108_nr_5F2127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2108_nr_5F2127 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4751 (s : N.State) (i : N.Inputs) :
  R.v4751 (state s) (inputs i) = Zmod.unsigned (N.v4751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4751 s i)) at 1.
  unfold R.v4751, N.v4751.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4752 (s : N.State) (i : N.Inputs) :
  R.v4752 (state s) (inputs i) = Zmod.unsigned (N.v4752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4752 s i)) at 1.
  unfold R.v4752, N.v4752.
  rewrite ?node_4751.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2109_nr_5F2128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2109_nr_5F2128 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4753 (s : N.State) (i : N.Inputs) :
  R.v4753 (state s) (inputs i) = Zmod.unsigned (N.v4753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4753 s i)) at 1.
  unfold R.v4753, N.v4753.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4754 (s : N.State) (i : N.Inputs) :
  R.v4754 (state s) (inputs i) = Zmod.unsigned (N.v4754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4754 s i)) at 1.
  unfold R.v4754, N.v4754.
  unfold R.v3021, N.v3021.
  rewrite ?node_4753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4755 (s : N.State) (i : N.Inputs) :
  R.v4755 (state s) (inputs i) = Zmod.unsigned (N.v4755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4755 s i)) at 1.
  unfold R.v4755, N.v4755.
  rewrite ?node_4754.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2110_nr_5F2129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2110_nr_5F2129 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4756 (s : N.State) (i : N.Inputs) :
  R.v4756 (state s) (inputs i) = Zmod.unsigned (N.v4756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4756 s i)) at 1.
  unfold R.v4756, N.v4756.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4757 (s : N.State) (i : N.Inputs) :
  R.v4757 (state s) (inputs i) = Zmod.unsigned (N.v4757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4757 s i)) at 1.
  unfold R.v4757, N.v4757.
  rewrite ?node_4756.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2111_nr_5F2130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2111_nr_5F2130 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4758 (s : N.State) (i : N.Inputs) :
  R.v4758 (state s) (inputs i) = Zmod.unsigned (N.v4758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4758 s i)) at 1.
  unfold R.v4758, N.v4758.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4759 (s : N.State) (i : N.Inputs) :
  R.v4759 (state s) (inputs i) = Zmod.unsigned (N.v4759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4759 s i)) at 1.
  unfold R.v4759, N.v4759.
  rewrite ?node_4758.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2112_nr_5F2131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2112_nr_5F2131 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4760 (s : N.State) (i : N.Inputs) :
  R.v4760 (state s) (inputs i) = Zmod.unsigned (N.v4760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4760 s i)) at 1.
  unfold R.v4760, N.v4760.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4761 (s : N.State) (i : N.Inputs) :
  R.v4761 (state s) (inputs i) = Zmod.unsigned (N.v4761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4761 s i)) at 1.
  unfold R.v4761, N.v4761.
  rewrite ?node_4760.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2113_nr_5F2132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2113_nr_5F2132 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4762 (s : N.State) (i : N.Inputs) :
  R.v4762 (state s) (inputs i) = Zmod.unsigned (N.v4762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4762 s i)) at 1.
  unfold R.v4762, N.v4762.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4763 (s : N.State) (i : N.Inputs) :
  R.v4763 (state s) (inputs i) = Zmod.unsigned (N.v4763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4763 s i)) at 1.
  unfold R.v4763, N.v4763.
  rewrite ?node_4762.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2114_nr_5F2133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2114_nr_5F2133 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4764 (s : N.State) (i : N.Inputs) :
  R.v4764 (state s) (inputs i) = Zmod.unsigned (N.v4764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4764 s i)) at 1.
  unfold R.v4764, N.v4764.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4765 (s : N.State) (i : N.Inputs) :
  R.v4765 (state s) (inputs i) = Zmod.unsigned (N.v4765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4765 s i)) at 1.
  unfold R.v4765, N.v4765.
  rewrite ?node_4764.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2115_nr_5F2134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2115_nr_5F2134 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4766 (s : N.State) (i : N.Inputs) :
  R.v4766 (state s) (inputs i) = Zmod.unsigned (N.v4766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4766 s i)) at 1.
  unfold R.v4766, N.v4766.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4767 (s : N.State) (i : N.Inputs) :
  R.v4767 (state s) (inputs i) = Zmod.unsigned (N.v4767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4767 s i)) at 1.
  unfold R.v4767, N.v4767.
  rewrite ?node_4766.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2116_nr_5F2135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2116_nr_5F2135 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4768 (s : N.State) (i : N.Inputs) :
  R.v4768 (state s) (inputs i) = Zmod.unsigned (N.v4768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4768 s i)) at 1.
  unfold R.v4768, N.v4768.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4769 (s : N.State) (i : N.Inputs) :
  R.v4769 (state s) (inputs i) = Zmod.unsigned (N.v4769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4769 s i)) at 1.
  unfold R.v4769, N.v4769.
  rewrite ?node_4768.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2117_nr_5F2136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2117_nr_5F2136 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4770 (s : N.State) (i : N.Inputs) :
  R.v4770 (state s) (inputs i) = Zmod.unsigned (N.v4770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4770 s i)) at 1.
  unfold R.v4770, N.v4770.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4771 (s : N.State) (i : N.Inputs) :
  R.v4771 (state s) (inputs i) = Zmod.unsigned (N.v4771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4771 s i)) at 1.
  unfold R.v4771, N.v4771.
  rewrite ?node_4770.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2118_nr_5F2137.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2118_nr_5F2137 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4772 (s : N.State) (i : N.Inputs) :
  R.v4772 (state s) (inputs i) = Zmod.unsigned (N.v4772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4772 s i)) at 1.
  unfold R.v4772, N.v4772.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4773 (s : N.State) (i : N.Inputs) :
  R.v4773 (state s) (inputs i) = Zmod.unsigned (N.v4773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4773 s i)) at 1.
  unfold R.v4773, N.v4773.
  rewrite ?node_4772.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2119_nr_5F2138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2119_nr_5F2138 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4774 (s : N.State) (i : N.Inputs) :
  R.v4774 (state s) (inputs i) = Zmod.unsigned (N.v4774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4774 s i)) at 1.
  unfold R.v4774, N.v4774.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4775 (s : N.State) (i : N.Inputs) :
  R.v4775 (state s) (inputs i) = Zmod.unsigned (N.v4775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4775 s i)) at 1.
  unfold R.v4775, N.v4775.
  rewrite ?node_4774.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2120_nr_5F2139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2120_nr_5F2139 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4776 (s : N.State) (i : N.Inputs) :
  R.v4776 (state s) (inputs i) = Zmod.unsigned (N.v4776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4776 s i)) at 1.
  unfold R.v4776, N.v4776.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4777 (s : N.State) (i : N.Inputs) :
  R.v4777 (state s) (inputs i) = Zmod.unsigned (N.v4777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4777 s i)) at 1.
  unfold R.v4777, N.v4777.
  rewrite ?node_4776.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2121_nr_5F2140.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2121_nr_5F2140 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4778 (s : N.State) (i : N.Inputs) :
  R.v4778 (state s) (inputs i) = Zmod.unsigned (N.v4778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4778 s i)) at 1.
  unfold R.v4778, N.v4778.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4779 (s : N.State) (i : N.Inputs) :
  R.v4779 (state s) (inputs i) = Zmod.unsigned (N.v4779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4779 s i)) at 1.
  unfold R.v4779, N.v4779.
  rewrite ?node_4778.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2122_nr_5F2141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2122_nr_5F2141 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4780 (s : N.State) (i : N.Inputs) :
  R.v4780 (state s) (inputs i) = Zmod.unsigned (N.v4780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4780 s i)) at 1.
  unfold R.v4780, N.v4780.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4781 (s : N.State) (i : N.Inputs) :
  R.v4781 (state s) (inputs i) = Zmod.unsigned (N.v4781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4781 s i)) at 1.
  unfold R.v4781, N.v4781.
  rewrite ?node_4780.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2123_nr_5F2143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2123_nr_5F2143 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4782 (s : N.State) (i : N.Inputs) :
  R.v4782 (state s) (inputs i) = Zmod.unsigned (N.v4782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4782 s i)) at 1.
  unfold R.v4782, N.v4782.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4783 (s : N.State) (i : N.Inputs) :
  R.v4783 (state s) (inputs i) = Zmod.unsigned (N.v4783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4783 s i)) at 1.
  unfold R.v4783, N.v4783.
  rewrite ?node_4782.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2124_nr_5F2144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2124_nr_5F2144 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4784 (s : N.State) (i : N.Inputs) :
  R.v4784 (state s) (inputs i) = Zmod.unsigned (N.v4784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4784 s i)) at 1.
  unfold R.v4784, N.v4784.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4785 (s : N.State) (i : N.Inputs) :
  R.v4785 (state s) (inputs i) = Zmod.unsigned (N.v4785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4785 s i)) at 1.
  unfold R.v4785, N.v4785.
  rewrite ?node_4784.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2125_nr_5F2145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2125_nr_5F2145 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4786 (s : N.State) (i : N.Inputs) :
  R.v4786 (state s) (inputs i) = Zmod.unsigned (N.v4786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4786 s i)) at 1.
  unfold R.v4786, N.v4786.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4787 (s : N.State) (i : N.Inputs) :
  R.v4787 (state s) (inputs i) = Zmod.unsigned (N.v4787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4787 s i)) at 1.
  unfold R.v4787, N.v4787.
  rewrite ?node_4786.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2126_nr_5F2146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2126_nr_5F2146 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4788 (s : N.State) (i : N.Inputs) :
  R.v4788 (state s) (inputs i) = Zmod.unsigned (N.v4788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4788 s i)) at 1.
  unfold R.v4788, N.v4788.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4789 (s : N.State) (i : N.Inputs) :
  R.v4789 (state s) (inputs i) = Zmod.unsigned (N.v4789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4789 s i)) at 1.
  unfold R.v4789, N.v4789.
  rewrite ?node_4788.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2127_nr_5F2147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2127_nr_5F2147 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4790 (s : N.State) (i : N.Inputs) :
  R.v4790 (state s) (inputs i) = Zmod.unsigned (N.v4790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4790 s i)) at 1.
  unfold R.v4790, N.v4790.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4791 (s : N.State) (i : N.Inputs) :
  R.v4791 (state s) (inputs i) = Zmod.unsigned (N.v4791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4791 s i)) at 1.
  unfold R.v4791, N.v4791.
  rewrite ?node_4790.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2128_nr_5F2148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2128_nr_5F2148 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4792 (s : N.State) (i : N.Inputs) :
  R.v4792 (state s) (inputs i) = Zmod.unsigned (N.v4792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4792 s i)) at 1.
  unfold R.v4792, N.v4792.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4793 (s : N.State) (i : N.Inputs) :
  R.v4793 (state s) (inputs i) = Zmod.unsigned (N.v4793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4793 s i)) at 1.
  unfold R.v4793, N.v4793.
  rewrite ?node_4792.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2129_nr_5F2149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2129_nr_5F2149 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4794 (s : N.State) (i : N.Inputs) :
  R.v4794 (state s) (inputs i) = Zmod.unsigned (N.v4794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4794 s i)) at 1.
  unfold R.v4794, N.v4794.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4795 (s : N.State) (i : N.Inputs) :
  R.v4795 (state s) (inputs i) = Zmod.unsigned (N.v4795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4795 s i)) at 1.
  unfold R.v4795, N.v4795.
  rewrite ?node_4794.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2130_nr_5F2150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2130_nr_5F2150 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4796 (s : N.State) (i : N.Inputs) :
  R.v4796 (state s) (inputs i) = Zmod.unsigned (N.v4796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4796 s i)) at 1.
  unfold R.v4796, N.v4796.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4797 (s : N.State) (i : N.Inputs) :
  R.v4797 (state s) (inputs i) = Zmod.unsigned (N.v4797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4797 s i)) at 1.
  unfold R.v4797, N.v4797.
  rewrite ?node_4796.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2131_nr_5F2151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2131_nr_5F2151 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4798 (s : N.State) (i : N.Inputs) :
  R.v4798 (state s) (inputs i) = Zmod.unsigned (N.v4798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4798 s i)) at 1.
  unfold R.v4798, N.v4798.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4799 (s : N.State) (i : N.Inputs) :
  R.v4799 (state s) (inputs i) = Zmod.unsigned (N.v4799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4799 s i)) at 1.
  unfold R.v4799, N.v4799.
  rewrite ?node_4798.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2132_nr_5F2152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2132_nr_5F2152 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4800 (s : N.State) (i : N.Inputs) :
  R.v4800 (state s) (inputs i) = Zmod.unsigned (N.v4800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4800 s i)) at 1.
  unfold R.v4800, N.v4800.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4801 (s : N.State) (i : N.Inputs) :
  R.v4801 (state s) (inputs i) = Zmod.unsigned (N.v4801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4801 s i)) at 1.
  unfold R.v4801, N.v4801.
  rewrite ?node_4800.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2133_nr_5F2153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2133_nr_5F2153 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4802 (s : N.State) (i : N.Inputs) :
  R.v4802 (state s) (inputs i) = Zmod.unsigned (N.v4802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4802 s i)) at 1.
  unfold R.v4802, N.v4802.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4803 (s : N.State) (i : N.Inputs) :
  R.v4803 (state s) (inputs i) = Zmod.unsigned (N.v4803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4803 s i)) at 1.
  unfold R.v4803, N.v4803.
  rewrite ?node_4802.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2134_nr_5F2154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2134_nr_5F2154 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4804 (s : N.State) (i : N.Inputs) :
  R.v4804 (state s) (inputs i) = Zmod.unsigned (N.v4804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4804 s i)) at 1.
  unfold R.v4804, N.v4804.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4805 (s : N.State) (i : N.Inputs) :
  R.v4805 (state s) (inputs i) = Zmod.unsigned (N.v4805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4805 s i)) at 1.
  unfold R.v4805, N.v4805.
  unfold R.v3021, N.v3021.
  rewrite ?node_4804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4806 (s : N.State) (i : N.Inputs) :
  R.v4806 (state s) (inputs i) = Zmod.unsigned (N.v4806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4806 s i)) at 1.
  unfold R.v4806, N.v4806.
  rewrite ?node_4805.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2135_nr_5F2155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2135_nr_5F2155 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4807 (s : N.State) (i : N.Inputs) :
  R.v4807 (state s) (inputs i) = Zmod.unsigned (N.v4807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4807 s i)) at 1.
  unfold R.v4807, N.v4807.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4808 (s : N.State) (i : N.Inputs) :
  R.v4808 (state s) (inputs i) = Zmod.unsigned (N.v4808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4808 s i)) at 1.
  unfold R.v4808, N.v4808.
  rewrite ?node_4807.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2136_nr_5F2156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2136_nr_5F2156 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4809 (s : N.State) (i : N.Inputs) :
  R.v4809 (state s) (inputs i) = Zmod.unsigned (N.v4809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4809 s i)) at 1.
  unfold R.v4809, N.v4809.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4810 (s : N.State) (i : N.Inputs) :
  R.v4810 (state s) (inputs i) = Zmod.unsigned (N.v4810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4810 s i)) at 1.
  unfold R.v4810, N.v4810.
  rewrite ?node_4809.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2137_nr_5F2157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2137_nr_5F2157 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4811 (s : N.State) (i : N.Inputs) :
  R.v4811 (state s) (inputs i) = Zmod.unsigned (N.v4811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4811 s i)) at 1.
  unfold R.v4811, N.v4811.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4812 (s : N.State) (i : N.Inputs) :
  R.v4812 (state s) (inputs i) = Zmod.unsigned (N.v4812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4812 s i)) at 1.
  unfold R.v4812, N.v4812.
  rewrite ?node_4811.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2138_nr_5F2158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2138_nr_5F2158 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4813 (s : N.State) (i : N.Inputs) :
  R.v4813 (state s) (inputs i) = Zmod.unsigned (N.v4813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4813 s i)) at 1.
  unfold R.v4813, N.v4813.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4814 (s : N.State) (i : N.Inputs) :
  R.v4814 (state s) (inputs i) = Zmod.unsigned (N.v4814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4814 s i)) at 1.
  unfold R.v4814, N.v4814.
  rewrite ?node_4813.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2139_nr_5F2159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2139_nr_5F2159 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4815 (s : N.State) (i : N.Inputs) :
  R.v4815 (state s) (inputs i) = Zmod.unsigned (N.v4815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4815 s i)) at 1.
  unfold R.v4815, N.v4815.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4816 (s : N.State) (i : N.Inputs) :
  R.v4816 (state s) (inputs i) = Zmod.unsigned (N.v4816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4816 s i)) at 1.
  unfold R.v4816, N.v4816.
  rewrite ?node_4815.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2140_nr_5F2160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2140_nr_5F2160 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4817 (s : N.State) (i : N.Inputs) :
  R.v4817 (state s) (inputs i) = Zmod.unsigned (N.v4817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4817 s i)) at 1.
  unfold R.v4817, N.v4817.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4818 (s : N.State) (i : N.Inputs) :
  R.v4818 (state s) (inputs i) = Zmod.unsigned (N.v4818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4818 s i)) at 1.
  unfold R.v4818, N.v4818.
  rewrite ?node_4817.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2141_nr_5F2161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2141_nr_5F2161 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4819 (s : N.State) (i : N.Inputs) :
  R.v4819 (state s) (inputs i) = Zmod.unsigned (N.v4819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4819 s i)) at 1.
  unfold R.v4819, N.v4819.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4820 (s : N.State) (i : N.Inputs) :
  R.v4820 (state s) (inputs i) = Zmod.unsigned (N.v4820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4820 s i)) at 1.
  unfold R.v4820, N.v4820.
  rewrite ?node_4819.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2142_nr_5F2162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2142_nr_5F2162 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4821 (s : N.State) (i : N.Inputs) :
  R.v4821 (state s) (inputs i) = Zmod.unsigned (N.v4821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4821 s i)) at 1.
  unfold R.v4821, N.v4821.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4822 (s : N.State) (i : N.Inputs) :
  R.v4822 (state s) (inputs i) = Zmod.unsigned (N.v4822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4822 s i)) at 1.
  unfold R.v4822, N.v4822.
  rewrite ?node_4821.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2143_nr_5F2163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2143_nr_5F2163 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4823 (s : N.State) (i : N.Inputs) :
  R.v4823 (state s) (inputs i) = Zmod.unsigned (N.v4823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4823 s i)) at 1.
  unfold R.v4823, N.v4823.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4824 (s : N.State) (i : N.Inputs) :
  R.v4824 (state s) (inputs i) = Zmod.unsigned (N.v4824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4824 s i)) at 1.
  unfold R.v4824, N.v4824.
  rewrite ?node_4823.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2144_nr_5F2164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2144_nr_5F2164 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4825 (s : N.State) (i : N.Inputs) :
  R.v4825 (state s) (inputs i) = Zmod.unsigned (N.v4825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4825 s i)) at 1.
  unfold R.v4825, N.v4825.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4826 (s : N.State) (i : N.Inputs) :
  R.v4826 (state s) (inputs i) = Zmod.unsigned (N.v4826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4826 s i)) at 1.
  unfold R.v4826, N.v4826.
  rewrite ?node_4825.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2145_nr_5F2165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2145_nr_5F2165 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4827 (s : N.State) (i : N.Inputs) :
  R.v4827 (state s) (inputs i) = Zmod.unsigned (N.v4827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4827 s i)) at 1.
  unfold R.v4827, N.v4827.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4828 (s : N.State) (i : N.Inputs) :
  R.v4828 (state s) (inputs i) = Zmod.unsigned (N.v4828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4828 s i)) at 1.
  unfold R.v4828, N.v4828.
  rewrite ?node_4827.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2146_nr_5F2166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2146_nr_5F2166 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4829 (s : N.State) (i : N.Inputs) :
  R.v4829 (state s) (inputs i) = Zmod.unsigned (N.v4829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4829 s i)) at 1.
  unfold R.v4829, N.v4829.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4830 (s : N.State) (i : N.Inputs) :
  R.v4830 (state s) (inputs i) = Zmod.unsigned (N.v4830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4830 s i)) at 1.
  unfold R.v4830, N.v4830.
  rewrite ?node_4829.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2147_nr_5F2168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2147_nr_5F2168 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4831 (s : N.State) (i : N.Inputs) :
  R.v4831 (state s) (inputs i) = Zmod.unsigned (N.v4831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4831 s i)) at 1.
  unfold R.v4831, N.v4831.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4832 (s : N.State) (i : N.Inputs) :
  R.v4832 (state s) (inputs i) = Zmod.unsigned (N.v4832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4832 s i)) at 1.
  unfold R.v4832, N.v4832.
  rewrite ?node_4831.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2148_nr_5F2169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2148_nr_5F2169 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4833 (s : N.State) (i : N.Inputs) :
  R.v4833 (state s) (inputs i) = Zmod.unsigned (N.v4833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4833 s i)) at 1.
  unfold R.v4833, N.v4833.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4834 (s : N.State) (i : N.Inputs) :
  R.v4834 (state s) (inputs i) = Zmod.unsigned (N.v4834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4834 s i)) at 1.
  unfold R.v4834, N.v4834.
  rewrite ?node_4833.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2149_nr_5F2170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2149_nr_5F2170 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4835 (s : N.State) (i : N.Inputs) :
  R.v4835 (state s) (inputs i) = Zmod.unsigned (N.v4835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4835 s i)) at 1.
  unfold R.v4835, N.v4835.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4836 (s : N.State) (i : N.Inputs) :
  R.v4836 (state s) (inputs i) = Zmod.unsigned (N.v4836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4836 s i)) at 1.
  unfold R.v4836, N.v4836.
  rewrite ?node_4835.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2150_nr_5F2171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2150_nr_5F2171 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4837 (s : N.State) (i : N.Inputs) :
  R.v4837 (state s) (inputs i) = Zmod.unsigned (N.v4837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4837 s i)) at 1.
  unfold R.v4837, N.v4837.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4838 (s : N.State) (i : N.Inputs) :
  R.v4838 (state s) (inputs i) = Zmod.unsigned (N.v4838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4838 s i)) at 1.
  unfold R.v4838, N.v4838.
  rewrite ?node_4837.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2151_nr_5F2172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2151_nr_5F2172 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4839 (s : N.State) (i : N.Inputs) :
  R.v4839 (state s) (inputs i) = Zmod.unsigned (N.v4839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4839 s i)) at 1.
  unfold R.v4839, N.v4839.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4840 (s : N.State) (i : N.Inputs) :
  R.v4840 (state s) (inputs i) = Zmod.unsigned (N.v4840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4840 s i)) at 1.
  unfold R.v4840, N.v4840.
  rewrite ?node_4839.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2152_nr_5F2173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2152_nr_5F2173 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4841 (s : N.State) (i : N.Inputs) :
  R.v4841 (state s) (inputs i) = Zmod.unsigned (N.v4841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4841 s i)) at 1.
  unfold R.v4841, N.v4841.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4842 (s : N.State) (i : N.Inputs) :
  R.v4842 (state s) (inputs i) = Zmod.unsigned (N.v4842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4842 s i)) at 1.
  unfold R.v4842, N.v4842.
  rewrite ?node_4841.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2153_nr_5F2174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2153_nr_5F2174 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4843 (s : N.State) (i : N.Inputs) :
  R.v4843 (state s) (inputs i) = Zmod.unsigned (N.v4843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4843 s i)) at 1.
  unfold R.v4843, N.v4843.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4844 (s : N.State) (i : N.Inputs) :
  R.v4844 (state s) (inputs i) = Zmod.unsigned (N.v4844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4844 s i)) at 1.
  unfold R.v4844, N.v4844.
  rewrite ?node_4843.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2154_nr_5F2175.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2154_nr_5F2175 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4845 (s : N.State) (i : N.Inputs) :
  R.v4845 (state s) (inputs i) = Zmod.unsigned (N.v4845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4845 s i)) at 1.
  unfold R.v4845, N.v4845.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4846 (s : N.State) (i : N.Inputs) :
  R.v4846 (state s) (inputs i) = Zmod.unsigned (N.v4846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4846 s i)) at 1.
  unfold R.v4846, N.v4846.
  rewrite ?node_4845.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2155_nr_5F2176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2155_nr_5F2176 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4847 (s : N.State) (i : N.Inputs) :
  R.v4847 (state s) (inputs i) = Zmod.unsigned (N.v4847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4847 s i)) at 1.
  unfold R.v4847, N.v4847.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4848 (s : N.State) (i : N.Inputs) :
  R.v4848 (state s) (inputs i) = Zmod.unsigned (N.v4848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4848 s i)) at 1.
  unfold R.v4848, N.v4848.
  rewrite ?node_4847.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2156_nr_5F2177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2156_nr_5F2177 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4849 (s : N.State) (i : N.Inputs) :
  R.v4849 (state s) (inputs i) = Zmod.unsigned (N.v4849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4849 s i)) at 1.
  unfold R.v4849, N.v4849.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4850 (s : N.State) (i : N.Inputs) :
  R.v4850 (state s) (inputs i) = Zmod.unsigned (N.v4850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4850 s i)) at 1.
  unfold R.v4850, N.v4850.
  rewrite ?node_4849.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2157_nr_5F2178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2157_nr_5F2178 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4851 (s : N.State) (i : N.Inputs) :
  R.v4851 (state s) (inputs i) = Zmod.unsigned (N.v4851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4851 s i)) at 1.
  unfold R.v4851, N.v4851.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4852 (s : N.State) (i : N.Inputs) :
  R.v4852 (state s) (inputs i) = Zmod.unsigned (N.v4852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4852 s i)) at 1.
  unfold R.v4852, N.v4852.
  unfold R.v3021, N.v3021.
  rewrite ?node_4851.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4853 (s : N.State) (i : N.Inputs) :
  R.v4853 (state s) (inputs i) = Zmod.unsigned (N.v4853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4853 s i)) at 1.
  unfold R.v4853, N.v4853.
  rewrite ?node_4852.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2158_nr_5F2179.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2158_nr_5F2179 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4854 (s : N.State) (i : N.Inputs) :
  R.v4854 (state s) (inputs i) = Zmod.unsigned (N.v4854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4854 s i)) at 1.
  unfold R.v4854, N.v4854.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4855 (s : N.State) (i : N.Inputs) :
  R.v4855 (state s) (inputs i) = Zmod.unsigned (N.v4855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4855 s i)) at 1.
  unfold R.v4855, N.v4855.
  rewrite ?node_4854.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2159_nr_5F2180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2159_nr_5F2180 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4856 (s : N.State) (i : N.Inputs) :
  R.v4856 (state s) (inputs i) = Zmod.unsigned (N.v4856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4856 s i)) at 1.
  unfold R.v4856, N.v4856.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4857 (s : N.State) (i : N.Inputs) :
  R.v4857 (state s) (inputs i) = Zmod.unsigned (N.v4857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4857 s i)) at 1.
  unfold R.v4857, N.v4857.
  rewrite ?node_4856.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2160_nr_5F2181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2160_nr_5F2181 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4858 (s : N.State) (i : N.Inputs) :
  R.v4858 (state s) (inputs i) = Zmod.unsigned (N.v4858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4858 s i)) at 1.
  unfold R.v4858, N.v4858.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4859 (s : N.State) (i : N.Inputs) :
  R.v4859 (state s) (inputs i) = Zmod.unsigned (N.v4859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4859 s i)) at 1.
  unfold R.v4859, N.v4859.
  rewrite ?node_4858.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2161_nr_5F2182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2161_nr_5F2182 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4860 (s : N.State) (i : N.Inputs) :
  R.v4860 (state s) (inputs i) = Zmod.unsigned (N.v4860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4860 s i)) at 1.
  unfold R.v4860, N.v4860.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4861 (s : N.State) (i : N.Inputs) :
  R.v4861 (state s) (inputs i) = Zmod.unsigned (N.v4861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4861 s i)) at 1.
  unfold R.v4861, N.v4861.
  rewrite ?node_4860.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2162_nr_5F2183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2162_nr_5F2183 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4862 (s : N.State) (i : N.Inputs) :
  R.v4862 (state s) (inputs i) = Zmod.unsigned (N.v4862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4862 s i)) at 1.
  unfold R.v4862, N.v4862.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4863 (s : N.State) (i : N.Inputs) :
  R.v4863 (state s) (inputs i) = Zmod.unsigned (N.v4863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4863 s i)) at 1.
  unfold R.v4863, N.v4863.
  rewrite ?node_4862.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2163_nr_5F2184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2163_nr_5F2184 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4864 (s : N.State) (i : N.Inputs) :
  R.v4864 (state s) (inputs i) = Zmod.unsigned (N.v4864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4864 s i)) at 1.
  unfold R.v4864, N.v4864.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4865 (s : N.State) (i : N.Inputs) :
  R.v4865 (state s) (inputs i) = Zmod.unsigned (N.v4865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4865 s i)) at 1.
  unfold R.v4865, N.v4865.
  rewrite ?node_4864.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2164_nr_5F2185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2164_nr_5F2185 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4866 (s : N.State) (i : N.Inputs) :
  R.v4866 (state s) (inputs i) = Zmod.unsigned (N.v4866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4866 s i)) at 1.
  unfold R.v4866, N.v4866.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4867 (s : N.State) (i : N.Inputs) :
  R.v4867 (state s) (inputs i) = Zmod.unsigned (N.v4867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4867 s i)) at 1.
  unfold R.v4867, N.v4867.
  rewrite ?node_4866.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2165_nr_5F2186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2165_nr_5F2186 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4868 (s : N.State) (i : N.Inputs) :
  R.v4868 (state s) (inputs i) = Zmod.unsigned (N.v4868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4868 s i)) at 1.
  unfold R.v4868, N.v4868.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4869 (s : N.State) (i : N.Inputs) :
  R.v4869 (state s) (inputs i) = Zmod.unsigned (N.v4869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4869 s i)) at 1.
  unfold R.v4869, N.v4869.
  rewrite ?node_4868.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2166_nr_5F2187.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2166_nr_5F2187 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4870 (s : N.State) (i : N.Inputs) :
  R.v4870 (state s) (inputs i) = Zmod.unsigned (N.v4870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4870 s i)) at 1.
  unfold R.v4870, N.v4870.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4871 (s : N.State) (i : N.Inputs) :
  R.v4871 (state s) (inputs i) = Zmod.unsigned (N.v4871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4871 s i)) at 1.
  unfold R.v4871, N.v4871.
  rewrite ?node_4870.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2167_nr_5F2188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2167_nr_5F2188 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4872 (s : N.State) (i : N.Inputs) :
  R.v4872 (state s) (inputs i) = Zmod.unsigned (N.v4872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4872 s i)) at 1.
  unfold R.v4872, N.v4872.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4873 (s : N.State) (i : N.Inputs) :
  R.v4873 (state s) (inputs i) = Zmod.unsigned (N.v4873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4873 s i)) at 1.
  unfold R.v4873, N.v4873.
  rewrite ?node_4872.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2168_nr_5F2189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2168_nr_5F2189 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4874 (s : N.State) (i : N.Inputs) :
  R.v4874 (state s) (inputs i) = Zmod.unsigned (N.v4874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4874 s i)) at 1.
  unfold R.v4874, N.v4874.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4875 (s : N.State) (i : N.Inputs) :
  R.v4875 (state s) (inputs i) = Zmod.unsigned (N.v4875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4875 s i)) at 1.
  unfold R.v4875, N.v4875.
  rewrite ?node_4874.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2169_nr_5F2191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2169_nr_5F2191 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4876 (s : N.State) (i : N.Inputs) :
  R.v4876 (state s) (inputs i) = Zmod.unsigned (N.v4876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4876 s i)) at 1.
  unfold R.v4876, N.v4876.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4877 (s : N.State) (i : N.Inputs) :
  R.v4877 (state s) (inputs i) = Zmod.unsigned (N.v4877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4877 s i)) at 1.
  unfold R.v4877, N.v4877.
  rewrite ?node_4876.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2170_nr_5F2192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2170_nr_5F2192 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4878 (s : N.State) (i : N.Inputs) :
  R.v4878 (state s) (inputs i) = Zmod.unsigned (N.v4878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4878 s i)) at 1.
  unfold R.v4878, N.v4878.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4879 (s : N.State) (i : N.Inputs) :
  R.v4879 (state s) (inputs i) = Zmod.unsigned (N.v4879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4879 s i)) at 1.
  unfold R.v4879, N.v4879.
  rewrite ?node_4878.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2171_nr_5F2193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2171_nr_5F2193 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4880 (s : N.State) (i : N.Inputs) :
  R.v4880 (state s) (inputs i) = Zmod.unsigned (N.v4880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4880 s i)) at 1.
  unfold R.v4880, N.v4880.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4881 (s : N.State) (i : N.Inputs) :
  R.v4881 (state s) (inputs i) = Zmod.unsigned (N.v4881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4881 s i)) at 1.
  unfold R.v4881, N.v4881.
  rewrite ?node_4880.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2172_nr_5F2194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2172_nr_5F2194 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4882 (s : N.State) (i : N.Inputs) :
  R.v4882 (state s) (inputs i) = Zmod.unsigned (N.v4882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4882 s i)) at 1.
  unfold R.v4882, N.v4882.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4883 (s : N.State) (i : N.Inputs) :
  R.v4883 (state s) (inputs i) = Zmod.unsigned (N.v4883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4883 s i)) at 1.
  unfold R.v4883, N.v4883.
  rewrite ?node_4882.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2173_nr_5F2195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2173_nr_5F2195 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4884 (s : N.State) (i : N.Inputs) :
  R.v4884 (state s) (inputs i) = Zmod.unsigned (N.v4884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4884 s i)) at 1.
  unfold R.v4884, N.v4884.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4885 (s : N.State) (i : N.Inputs) :
  R.v4885 (state s) (inputs i) = Zmod.unsigned (N.v4885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4885 s i)) at 1.
  unfold R.v4885, N.v4885.
  rewrite ?node_4884.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2174_nr_5F2196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2174_nr_5F2196 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4886 (s : N.State) (i : N.Inputs) :
  R.v4886 (state s) (inputs i) = Zmod.unsigned (N.v4886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4886 s i)) at 1.
  unfold R.v4886, N.v4886.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4887 (s : N.State) (i : N.Inputs) :
  R.v4887 (state s) (inputs i) = Zmod.unsigned (N.v4887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4887 s i)) at 1.
  unfold R.v4887, N.v4887.
  rewrite ?node_4886.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2175_nr_5F2197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2175_nr_5F2197 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4888 (s : N.State) (i : N.Inputs) :
  R.v4888 (state s) (inputs i) = Zmod.unsigned (N.v4888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4888 s i)) at 1.
  unfold R.v4888, N.v4888.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4889 (s : N.State) (i : N.Inputs) :
  R.v4889 (state s) (inputs i) = Zmod.unsigned (N.v4889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4889 s i)) at 1.
  unfold R.v4889, N.v4889.
  rewrite ?node_4888.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2176_nr_5F2198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2176_nr_5F2198 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4890 (s : N.State) (i : N.Inputs) :
  R.v4890 (state s) (inputs i) = Zmod.unsigned (N.v4890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4890 s i)) at 1.
  unfold R.v4890, N.v4890.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4891 (s : N.State) (i : N.Inputs) :
  R.v4891 (state s) (inputs i) = Zmod.unsigned (N.v4891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4891 s i)) at 1.
  unfold R.v4891, N.v4891.
  rewrite ?node_4890.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2177_nr_5F2199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2177_nr_5F2199 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4892 (s : N.State) (i : N.Inputs) :
  R.v4892 (state s) (inputs i) = Zmod.unsigned (N.v4892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4892 s i)) at 1.
  unfold R.v4892, N.v4892.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4893 (s : N.State) (i : N.Inputs) :
  R.v4893 (state s) (inputs i) = Zmod.unsigned (N.v4893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4893 s i)) at 1.
  unfold R.v4893, N.v4893.
  rewrite ?node_4892.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2178_nr_5F2200.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2178_nr_5F2200 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4894 (s : N.State) (i : N.Inputs) :
  R.v4894 (state s) (inputs i) = Zmod.unsigned (N.v4894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4894 s i)) at 1.
  unfold R.v4894, N.v4894.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4895 (s : N.State) (i : N.Inputs) :
  R.v4895 (state s) (inputs i) = Zmod.unsigned (N.v4895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4895 s i)) at 1.
  unfold R.v4895, N.v4895.
  unfold R.v3021, N.v3021.
  rewrite ?node_4894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4896 (s : N.State) (i : N.Inputs) :
  R.v4896 (state s) (inputs i) = Zmod.unsigned (N.v4896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4896 s i)) at 1.
  unfold R.v4896, N.v4896.
  rewrite ?node_4895.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2179_nr_5F2201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2179_nr_5F2201 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4897 (s : N.State) (i : N.Inputs) :
  R.v4897 (state s) (inputs i) = Zmod.unsigned (N.v4897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4897 s i)) at 1.
  unfold R.v4897, N.v4897.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4898 (s : N.State) (i : N.Inputs) :
  R.v4898 (state s) (inputs i) = Zmod.unsigned (N.v4898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4898 s i)) at 1.
  unfold R.v4898, N.v4898.
  rewrite ?node_4897.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2180_nr_5F2202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2180_nr_5F2202 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4899 (s : N.State) (i : N.Inputs) :
  R.v4899 (state s) (inputs i) = Zmod.unsigned (N.v4899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4899 s i)) at 1.
  unfold R.v4899, N.v4899.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4900 (s : N.State) (i : N.Inputs) :
  R.v4900 (state s) (inputs i) = Zmod.unsigned (N.v4900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4900 s i)) at 1.
  unfold R.v4900, N.v4900.
  rewrite ?node_4899.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2181_nr_5F2203.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2181_nr_5F2203 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4901 (s : N.State) (i : N.Inputs) :
  R.v4901 (state s) (inputs i) = Zmod.unsigned (N.v4901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4901 s i)) at 1.
  unfold R.v4901, N.v4901.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4902 (s : N.State) (i : N.Inputs) :
  R.v4902 (state s) (inputs i) = Zmod.unsigned (N.v4902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4902 s i)) at 1.
  unfold R.v4902, N.v4902.
  rewrite ?node_4901.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2182_nr_5F2204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2182_nr_5F2204 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4903 (s : N.State) (i : N.Inputs) :
  R.v4903 (state s) (inputs i) = Zmod.unsigned (N.v4903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4903 s i)) at 1.
  unfold R.v4903, N.v4903.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4904 (s : N.State) (i : N.Inputs) :
  R.v4904 (state s) (inputs i) = Zmod.unsigned (N.v4904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4904 s i)) at 1.
  unfold R.v4904, N.v4904.
  rewrite ?node_4903.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2183_nr_5F2205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2183_nr_5F2205 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4905 (s : N.State) (i : N.Inputs) :
  R.v4905 (state s) (inputs i) = Zmod.unsigned (N.v4905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4905 s i)) at 1.
  unfold R.v4905, N.v4905.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4906 (s : N.State) (i : N.Inputs) :
  R.v4906 (state s) (inputs i) = Zmod.unsigned (N.v4906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4906 s i)) at 1.
  unfold R.v4906, N.v4906.
  rewrite ?node_4905.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2184_nr_5F2206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2184_nr_5F2206 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4907 (s : N.State) (i : N.Inputs) :
  R.v4907 (state s) (inputs i) = Zmod.unsigned (N.v4907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4907 s i)) at 1.
  unfold R.v4907, N.v4907.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4908 (s : N.State) (i : N.Inputs) :
  R.v4908 (state s) (inputs i) = Zmod.unsigned (N.v4908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4908 s i)) at 1.
  unfold R.v4908, N.v4908.
  rewrite ?node_4907.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2185_nr_5F2207.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2185_nr_5F2207 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4909 (s : N.State) (i : N.Inputs) :
  R.v4909 (state s) (inputs i) = Zmod.unsigned (N.v4909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4909 s i)) at 1.
  unfold R.v4909, N.v4909.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4910 (s : N.State) (i : N.Inputs) :
  R.v4910 (state s) (inputs i) = Zmod.unsigned (N.v4910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4910 s i)) at 1.
  unfold R.v4910, N.v4910.
  rewrite ?node_4909.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2186_nr_5F2208.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2186_nr_5F2208 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4911 (s : N.State) (i : N.Inputs) :
  R.v4911 (state s) (inputs i) = Zmod.unsigned (N.v4911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4911 s i)) at 1.
  unfold R.v4911, N.v4911.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4912 (s : N.State) (i : N.Inputs) :
  R.v4912 (state s) (inputs i) = Zmod.unsigned (N.v4912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4912 s i)) at 1.
  unfold R.v4912, N.v4912.
  rewrite ?node_4911.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2187_nr_5F2209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2187_nr_5F2209 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4913 (s : N.State) (i : N.Inputs) :
  R.v4913 (state s) (inputs i) = Zmod.unsigned (N.v4913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4913 s i)) at 1.
  unfold R.v4913, N.v4913.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4914 (s : N.State) (i : N.Inputs) :
  R.v4914 (state s) (inputs i) = Zmod.unsigned (N.v4914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4914 s i)) at 1.
  unfold R.v4914, N.v4914.
  rewrite ?node_4913.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2188_nr_5F2210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2188_nr_5F2210 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4915 (s : N.State) (i : N.Inputs) :
  R.v4915 (state s) (inputs i) = Zmod.unsigned (N.v4915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4915 s i)) at 1.
  unfold R.v4915, N.v4915.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4916 (s : N.State) (i : N.Inputs) :
  R.v4916 (state s) (inputs i) = Zmod.unsigned (N.v4916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4916 s i)) at 1.
  unfold R.v4916, N.v4916.
  rewrite ?node_4915.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2189_nr_5F2212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2189_nr_5F2212 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4917 (s : N.State) (i : N.Inputs) :
  R.v4917 (state s) (inputs i) = Zmod.unsigned (N.v4917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4917 s i)) at 1.
  unfold R.v4917, N.v4917.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4918 (s : N.State) (i : N.Inputs) :
  R.v4918 (state s) (inputs i) = Zmod.unsigned (N.v4918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4918 s i)) at 1.
  unfold R.v4918, N.v4918.
  rewrite ?node_4917.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2190_nr_5F2213.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2190_nr_5F2213 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4919 (s : N.State) (i : N.Inputs) :
  R.v4919 (state s) (inputs i) = Zmod.unsigned (N.v4919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4919 s i)) at 1.
  unfold R.v4919, N.v4919.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4920 (s : N.State) (i : N.Inputs) :
  R.v4920 (state s) (inputs i) = Zmod.unsigned (N.v4920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4920 s i)) at 1.
  unfold R.v4920, N.v4920.
  rewrite ?node_4919.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2191_nr_5F2214.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2191_nr_5F2214 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4921 (s : N.State) (i : N.Inputs) :
  R.v4921 (state s) (inputs i) = Zmod.unsigned (N.v4921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4921 s i)) at 1.
  unfold R.v4921, N.v4921.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4922 (s : N.State) (i : N.Inputs) :
  R.v4922 (state s) (inputs i) = Zmod.unsigned (N.v4922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4922 s i)) at 1.
  unfold R.v4922, N.v4922.
  rewrite ?node_4921.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2192_nr_5F2215.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2192_nr_5F2215 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4923 (s : N.State) (i : N.Inputs) :
  R.v4923 (state s) (inputs i) = Zmod.unsigned (N.v4923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4923 s i)) at 1.
  unfold R.v4923, N.v4923.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4924 (s : N.State) (i : N.Inputs) :
  R.v4924 (state s) (inputs i) = Zmod.unsigned (N.v4924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4924 s i)) at 1.
  unfold R.v4924, N.v4924.
  rewrite ?node_4923.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2193_nr_5F2216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2193_nr_5F2216 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4925 (s : N.State) (i : N.Inputs) :
  R.v4925 (state s) (inputs i) = Zmod.unsigned (N.v4925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4925 s i)) at 1.
  unfold R.v4925, N.v4925.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4926 (s : N.State) (i : N.Inputs) :
  R.v4926 (state s) (inputs i) = Zmod.unsigned (N.v4926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4926 s i)) at 1.
  unfold R.v4926, N.v4926.
  rewrite ?node_4925.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2194_nr_5F2217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2194_nr_5F2217 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4927 (s : N.State) (i : N.Inputs) :
  R.v4927 (state s) (inputs i) = Zmod.unsigned (N.v4927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4927 s i)) at 1.
  unfold R.v4927, N.v4927.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4928 (s : N.State) (i : N.Inputs) :
  R.v4928 (state s) (inputs i) = Zmod.unsigned (N.v4928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4928 s i)) at 1.
  unfold R.v4928, N.v4928.
  rewrite ?node_4927.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2195_nr_5F2218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2195_nr_5F2218 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4929 (s : N.State) (i : N.Inputs) :
  R.v4929 (state s) (inputs i) = Zmod.unsigned (N.v4929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4929 s i)) at 1.
  unfold R.v4929, N.v4929.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4930 (s : N.State) (i : N.Inputs) :
  R.v4930 (state s) (inputs i) = Zmod.unsigned (N.v4930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4930 s i)) at 1.
  unfold R.v4930, N.v4930.
  rewrite ?node_4929.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2196_nr_5F2219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2196_nr_5F2219 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4931 (s : N.State) (i : N.Inputs) :
  R.v4931 (state s) (inputs i) = Zmod.unsigned (N.v4931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4931 s i)) at 1.
  unfold R.v4931, N.v4931.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4932 (s : N.State) (i : N.Inputs) :
  R.v4932 (state s) (inputs i) = Zmod.unsigned (N.v4932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4932 s i)) at 1.
  unfold R.v4932, N.v4932.
  rewrite ?node_4931.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2197_nr_5F2220.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2197_nr_5F2220 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4933 (s : N.State) (i : N.Inputs) :
  R.v4933 (state s) (inputs i) = Zmod.unsigned (N.v4933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4933 s i)) at 1.
  unfold R.v4933, N.v4933.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4934 (s : N.State) (i : N.Inputs) :
  R.v4934 (state s) (inputs i) = Zmod.unsigned (N.v4934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4934 s i)) at 1.
  unfold R.v4934, N.v4934.
  unfold R.v3021, N.v3021.
  rewrite ?node_4933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4935 (s : N.State) (i : N.Inputs) :
  R.v4935 (state s) (inputs i) = Zmod.unsigned (N.v4935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4935 s i)) at 1.
  unfold R.v4935, N.v4935.
  rewrite ?node_4934.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2198_nr_5F2221.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2198_nr_5F2221 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4936 (s : N.State) (i : N.Inputs) :
  R.v4936 (state s) (inputs i) = Zmod.unsigned (N.v4936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4936 s i)) at 1.
  unfold R.v4936, N.v4936.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4937 (s : N.State) (i : N.Inputs) :
  R.v4937 (state s) (inputs i) = Zmod.unsigned (N.v4937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4937 s i)) at 1.
  unfold R.v4937, N.v4937.
  rewrite ?node_4936.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2199_nr_5F2222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2199_nr_5F2222 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4938 (s : N.State) (i : N.Inputs) :
  R.v4938 (state s) (inputs i) = Zmod.unsigned (N.v4938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4938 s i)) at 1.
  unfold R.v4938, N.v4938.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4939 (s : N.State) (i : N.Inputs) :
  R.v4939 (state s) (inputs i) = Zmod.unsigned (N.v4939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4939 s i)) at 1.
  unfold R.v4939, N.v4939.
  rewrite ?node_4938.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2200_nr_5F2223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2200_nr_5F2223 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4940 (s : N.State) (i : N.Inputs) :
  R.v4940 (state s) (inputs i) = Zmod.unsigned (N.v4940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4940 s i)) at 1.
  unfold R.v4940, N.v4940.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4941 (s : N.State) (i : N.Inputs) :
  R.v4941 (state s) (inputs i) = Zmod.unsigned (N.v4941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4941 s i)) at 1.
  unfold R.v4941, N.v4941.
  rewrite ?node_4940.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2201_nr_5F2224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2201_nr_5F2224 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4942 (s : N.State) (i : N.Inputs) :
  R.v4942 (state s) (inputs i) = Zmod.unsigned (N.v4942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4942 s i)) at 1.
  unfold R.v4942, N.v4942.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4943 (s : N.State) (i : N.Inputs) :
  R.v4943 (state s) (inputs i) = Zmod.unsigned (N.v4943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4943 s i)) at 1.
  unfold R.v4943, N.v4943.
  rewrite ?node_4942.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2202_nr_5F2225.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2202_nr_5F2225 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4944 (s : N.State) (i : N.Inputs) :
  R.v4944 (state s) (inputs i) = Zmod.unsigned (N.v4944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4944 s i)) at 1.
  unfold R.v4944, N.v4944.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4945 (s : N.State) (i : N.Inputs) :
  R.v4945 (state s) (inputs i) = Zmod.unsigned (N.v4945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4945 s i)) at 1.
  unfold R.v4945, N.v4945.
  rewrite ?node_4944.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2203_nr_5F2226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2203_nr_5F2226 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4946 (s : N.State) (i : N.Inputs) :
  R.v4946 (state s) (inputs i) = Zmod.unsigned (N.v4946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4946 s i)) at 1.
  unfold R.v4946, N.v4946.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4947 (s : N.State) (i : N.Inputs) :
  R.v4947 (state s) (inputs i) = Zmod.unsigned (N.v4947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4947 s i)) at 1.
  unfold R.v4947, N.v4947.
  rewrite ?node_4946.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2204_nr_5F2227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2204_nr_5F2227 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4948 (s : N.State) (i : N.Inputs) :
  R.v4948 (state s) (inputs i) = Zmod.unsigned (N.v4948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4948 s i)) at 1.
  unfold R.v4948, N.v4948.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4949 (s : N.State) (i : N.Inputs) :
  R.v4949 (state s) (inputs i) = Zmod.unsigned (N.v4949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4949 s i)) at 1.
  unfold R.v4949, N.v4949.
  rewrite ?node_4948.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2205_nr_5F2228.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2205_nr_5F2228 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4950 (s : N.State) (i : N.Inputs) :
  R.v4950 (state s) (inputs i) = Zmod.unsigned (N.v4950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4950 s i)) at 1.
  unfold R.v4950, N.v4950.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4951 (s : N.State) (i : N.Inputs) :
  R.v4951 (state s) (inputs i) = Zmod.unsigned (N.v4951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4951 s i)) at 1.
  unfold R.v4951, N.v4951.
  rewrite ?node_4950.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2206_nr_5F2229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2206_nr_5F2229 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4952 (s : N.State) (i : N.Inputs) :
  R.v4952 (state s) (inputs i) = Zmod.unsigned (N.v4952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4952 s i)) at 1.
  unfold R.v4952, N.v4952.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4953 (s : N.State) (i : N.Inputs) :
  R.v4953 (state s) (inputs i) = Zmod.unsigned (N.v4953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4953 s i)) at 1.
  unfold R.v4953, N.v4953.
  rewrite ?node_4952.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2207_nr_5F2231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2207_nr_5F2231 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4954 (s : N.State) (i : N.Inputs) :
  R.v4954 (state s) (inputs i) = Zmod.unsigned (N.v4954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4954 s i)) at 1.
  unfold R.v4954, N.v4954.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4955 (s : N.State) (i : N.Inputs) :
  R.v4955 (state s) (inputs i) = Zmod.unsigned (N.v4955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4955 s i)) at 1.
  unfold R.v4955, N.v4955.
  rewrite ?node_4954.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2208_nr_5F2232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2208_nr_5F2232 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4956 (s : N.State) (i : N.Inputs) :
  R.v4956 (state s) (inputs i) = Zmod.unsigned (N.v4956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4956 s i)) at 1.
  unfold R.v4956, N.v4956.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4957 (s : N.State) (i : N.Inputs) :
  R.v4957 (state s) (inputs i) = Zmod.unsigned (N.v4957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4957 s i)) at 1.
  unfold R.v4957, N.v4957.
  rewrite ?node_4956.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2209_nr_5F2233.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2209_nr_5F2233 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4958 (s : N.State) (i : N.Inputs) :
  R.v4958 (state s) (inputs i) = Zmod.unsigned (N.v4958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4958 s i)) at 1.
  unfold R.v4958, N.v4958.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4959 (s : N.State) (i : N.Inputs) :
  R.v4959 (state s) (inputs i) = Zmod.unsigned (N.v4959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4959 s i)) at 1.
  unfold R.v4959, N.v4959.
  rewrite ?node_4958.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2210_nr_5F2234.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2210_nr_5F2234 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4960 (s : N.State) (i : N.Inputs) :
  R.v4960 (state s) (inputs i) = Zmod.unsigned (N.v4960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4960 s i)) at 1.
  unfold R.v4960, N.v4960.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4961 (s : N.State) (i : N.Inputs) :
  R.v4961 (state s) (inputs i) = Zmod.unsigned (N.v4961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4961 s i)) at 1.
  unfold R.v4961, N.v4961.
  rewrite ?node_4960.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2211_nr_5F2235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2211_nr_5F2235 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4962 (s : N.State) (i : N.Inputs) :
  R.v4962 (state s) (inputs i) = Zmod.unsigned (N.v4962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4962 s i)) at 1.
  unfold R.v4962, N.v4962.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4963 (s : N.State) (i : N.Inputs) :
  R.v4963 (state s) (inputs i) = Zmod.unsigned (N.v4963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4963 s i)) at 1.
  unfold R.v4963, N.v4963.
  rewrite ?node_4962.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2212_nr_5F2236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2212_nr_5F2236 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4964 (s : N.State) (i : N.Inputs) :
  R.v4964 (state s) (inputs i) = Zmod.unsigned (N.v4964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4964 s i)) at 1.
  unfold R.v4964, N.v4964.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4965 (s : N.State) (i : N.Inputs) :
  R.v4965 (state s) (inputs i) = Zmod.unsigned (N.v4965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4965 s i)) at 1.
  unfold R.v4965, N.v4965.
  rewrite ?node_4964.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2213_nr_5F2237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2213_nr_5F2237 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4966 (s : N.State) (i : N.Inputs) :
  R.v4966 (state s) (inputs i) = Zmod.unsigned (N.v4966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4966 s i)) at 1.
  unfold R.v4966, N.v4966.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4967 (s : N.State) (i : N.Inputs) :
  R.v4967 (state s) (inputs i) = Zmod.unsigned (N.v4967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4967 s i)) at 1.
  unfold R.v4967, N.v4967.
  rewrite ?node_4966.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2214_nr_5F2238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2214_nr_5F2238 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4968 (s : N.State) (i : N.Inputs) :
  R.v4968 (state s) (inputs i) = Zmod.unsigned (N.v4968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4968 s i)) at 1.
  unfold R.v4968, N.v4968.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4969 (s : N.State) (i : N.Inputs) :
  R.v4969 (state s) (inputs i) = Zmod.unsigned (N.v4969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4969 s i)) at 1.
  unfold R.v4969, N.v4969.
  unfold R.v3021, N.v3021.
  rewrite ?node_4968.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4970 (s : N.State) (i : N.Inputs) :
  R.v4970 (state s) (inputs i) = Zmod.unsigned (N.v4970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4970 s i)) at 1.
  unfold R.v4970, N.v4970.
  rewrite ?node_4969.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2215_nr_5F2239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2215_nr_5F2239 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4971 (s : N.State) (i : N.Inputs) :
  R.v4971 (state s) (inputs i) = Zmod.unsigned (N.v4971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4971 s i)) at 1.
  unfold R.v4971, N.v4971.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4972 (s : N.State) (i : N.Inputs) :
  R.v4972 (state s) (inputs i) = Zmod.unsigned (N.v4972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4972 s i)) at 1.
  unfold R.v4972, N.v4972.
  rewrite ?node_4971.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2216_nr_5F2240.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2216_nr_5F2240 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4973 (s : N.State) (i : N.Inputs) :
  R.v4973 (state s) (inputs i) = Zmod.unsigned (N.v4973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4973 s i)) at 1.
  unfold R.v4973, N.v4973.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4974 (s : N.State) (i : N.Inputs) :
  R.v4974 (state s) (inputs i) = Zmod.unsigned (N.v4974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4974 s i)) at 1.
  unfold R.v4974, N.v4974.
  rewrite ?node_4973.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2217_nr_5F2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2217_nr_5F2241 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4975 (s : N.State) (i : N.Inputs) :
  R.v4975 (state s) (inputs i) = Zmod.unsigned (N.v4975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4975 s i)) at 1.
  unfold R.v4975, N.v4975.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4976 (s : N.State) (i : N.Inputs) :
  R.v4976 (state s) (inputs i) = Zmod.unsigned (N.v4976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4976 s i)) at 1.
  unfold R.v4976, N.v4976.
  rewrite ?node_4975.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2218_nr_5F2242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2218_nr_5F2242 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4977 (s : N.State) (i : N.Inputs) :
  R.v4977 (state s) (inputs i) = Zmod.unsigned (N.v4977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4977 s i)) at 1.
  unfold R.v4977, N.v4977.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4978 (s : N.State) (i : N.Inputs) :
  R.v4978 (state s) (inputs i) = Zmod.unsigned (N.v4978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4978 s i)) at 1.
  unfold R.v4978, N.v4978.
  rewrite ?node_4977.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2219_nr_5F2243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2219_nr_5F2243 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4979 (s : N.State) (i : N.Inputs) :
  R.v4979 (state s) (inputs i) = Zmod.unsigned (N.v4979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4979 s i)) at 1.
  unfold R.v4979, N.v4979.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4980 (s : N.State) (i : N.Inputs) :
  R.v4980 (state s) (inputs i) = Zmod.unsigned (N.v4980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4980 s i)) at 1.
  unfold R.v4980, N.v4980.
  rewrite ?node_4979.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2220_nr_5F2244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2220_nr_5F2244 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4981 (s : N.State) (i : N.Inputs) :
  R.v4981 (state s) (inputs i) = Zmod.unsigned (N.v4981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4981 s i)) at 1.
  unfold R.v4981, N.v4981.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4982 (s : N.State) (i : N.Inputs) :
  R.v4982 (state s) (inputs i) = Zmod.unsigned (N.v4982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4982 s i)) at 1.
  unfold R.v4982, N.v4982.
  rewrite ?node_4981.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2221_nr_5F2245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2221_nr_5F2245 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4983 (s : N.State) (i : N.Inputs) :
  R.v4983 (state s) (inputs i) = Zmod.unsigned (N.v4983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4983 s i)) at 1.
  unfold R.v4983, N.v4983.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4984 (s : N.State) (i : N.Inputs) :
  R.v4984 (state s) (inputs i) = Zmod.unsigned (N.v4984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4984 s i)) at 1.
  unfold R.v4984, N.v4984.
  rewrite ?node_4983.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2222_nr_5F2246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2222_nr_5F2246 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4985 (s : N.State) (i : N.Inputs) :
  R.v4985 (state s) (inputs i) = Zmod.unsigned (N.v4985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4985 s i)) at 1.
  unfold R.v4985, N.v4985.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4986 (s : N.State) (i : N.Inputs) :
  R.v4986 (state s) (inputs i) = Zmod.unsigned (N.v4986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4986 s i)) at 1.
  unfold R.v4986, N.v4986.
  rewrite ?node_4985.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2223_nr_5F2248.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2223_nr_5F2248 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4987 (s : N.State) (i : N.Inputs) :
  R.v4987 (state s) (inputs i) = Zmod.unsigned (N.v4987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4987 s i)) at 1.
  unfold R.v4987, N.v4987.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4988 (s : N.State) (i : N.Inputs) :
  R.v4988 (state s) (inputs i) = Zmod.unsigned (N.v4988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4988 s i)) at 1.
  unfold R.v4988, N.v4988.
  rewrite ?node_4987.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2224_nr_5F2249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2224_nr_5F2249 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4989 (s : N.State) (i : N.Inputs) :
  R.v4989 (state s) (inputs i) = Zmod.unsigned (N.v4989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4989 s i)) at 1.
  unfold R.v4989, N.v4989.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4990 (s : N.State) (i : N.Inputs) :
  R.v4990 (state s) (inputs i) = Zmod.unsigned (N.v4990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4990 s i)) at 1.
  unfold R.v4990, N.v4990.
  rewrite ?node_4989.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2225_nr_5F2250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2225_nr_5F2250 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4991 (s : N.State) (i : N.Inputs) :
  R.v4991 (state s) (inputs i) = Zmod.unsigned (N.v4991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4991 s i)) at 1.
  unfold R.v4991, N.v4991.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4992 (s : N.State) (i : N.Inputs) :
  R.v4992 (state s) (inputs i) = Zmod.unsigned (N.v4992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4992 s i)) at 1.
  unfold R.v4992, N.v4992.
  rewrite ?node_4991.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2226_nr_5F2251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2226_nr_5F2251 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4993 (s : N.State) (i : N.Inputs) :
  R.v4993 (state s) (inputs i) = Zmod.unsigned (N.v4993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4993 s i)) at 1.
  unfold R.v4993, N.v4993.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4994 (s : N.State) (i : N.Inputs) :
  R.v4994 (state s) (inputs i) = Zmod.unsigned (N.v4994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4994 s i)) at 1.
  unfold R.v4994, N.v4994.
  rewrite ?node_4993.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2227_nr_5F2252.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2227_nr_5F2252 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4995 (s : N.State) (i : N.Inputs) :
  R.v4995 (state s) (inputs i) = Zmod.unsigned (N.v4995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4995 s i)) at 1.
  unfold R.v4995, N.v4995.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4996 (s : N.State) (i : N.Inputs) :
  R.v4996 (state s) (inputs i) = Zmod.unsigned (N.v4996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4996 s i)) at 1.
  unfold R.v4996, N.v4996.
  rewrite ?node_4995.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2228_nr_5F2253.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2228_nr_5F2253 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4997 (s : N.State) (i : N.Inputs) :
  R.v4997 (state s) (inputs i) = Zmod.unsigned (N.v4997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4997 s i)) at 1.
  unfold R.v4997, N.v4997.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4998 (s : N.State) (i : N.Inputs) :
  R.v4998 (state s) (inputs i) = Zmod.unsigned (N.v4998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4998 s i)) at 1.
  unfold R.v4998, N.v4998.
  rewrite ?node_4997.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2229_nr_5F2254.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2229_nr_5F2254 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4999 (s : N.State) (i : N.Inputs) :
  R.v4999 (state s) (inputs i) = Zmod.unsigned (N.v4999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4999 s i)) at 1.
  unfold R.v4999, N.v4999.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
