(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes051.
Lemma node_52000 (s : N.State) (i : N.Inputs) :
  R.v52000 (state s) (inputs i) = Zmod.unsigned (N.v52000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52000 s i)) at 1.
  unfold R.v52000, N.v52000.
  rewrite ?node_11810.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52001 (s : N.State) (i : N.Inputs) :
  R.v52001 (state s) (inputs i) = Zmod.unsigned (N.v52001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52001 s i)) at 1.
  unfold R.v52001, N.v52001.
  unfold R.v6, N.v6.
  rewrite ?node_11806.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52002 (s : N.State) (i : N.Inputs) :
  R.v52002 (state s) (inputs i) = Zmod.unsigned (N.v52002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52002 s i)) at 1.
  unfold R.v52002, N.v52002.
  unfold R.v6, N.v6.
  rewrite ?node_11803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52003 (s : N.State) (i : N.Inputs) :
  R.v52003 (state s) (inputs i) = Zmod.unsigned (N.v52003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52003 s i)) at 1.
  unfold R.v52003, N.v52003.
  rewrite ?node_52001.
  rewrite ?node_52002.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52004 (s : N.State) (i : N.Inputs) :
  R.v52004 (state s) (inputs i) = Zmod.unsigned (N.v52004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52004 s i)) at 1.
  unfold R.v52004, N.v52004.
  unfold R.v16484, N.v16484.
  rewrite ?node_52003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52005 (s : N.State) (i : N.Inputs) :
  R.v52005 (state s) (inputs i) = Zmod.unsigned (N.v52005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52005 s i)) at 1.
  unfold R.v52005, N.v52005.
  rewrite ?node_52000.
  rewrite ?node_52004.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52006 (s : N.State) (i : N.Inputs) :
  R.v52006 (state s) (inputs i) = Zmod.unsigned (N.v52006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52006 s i)) at 1.
  unfold R.v52006, N.v52006.
  unfold R.v6, N.v6.
  rewrite ?node_52005.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52007 (s : N.State) (i : N.Inputs) :
  R.v52007 (state s) (inputs i) = Zmod.unsigned (N.v52007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52007 s i)) at 1.
  unfold R.v52007, N.v52007.
  rewrite ?node_11811.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52008 (s : N.State) (i : N.Inputs) :
  R.v52008 (state s) (inputs i) = Zmod.unsigned (N.v52008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52008 s i)) at 1.
  unfold R.v52008, N.v52008.
  unfold R.v6, N.v6.
  rewrite ?node_11962.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52009 (s : N.State) (i : N.Inputs) :
  R.v52009 (state s) (inputs i) = Zmod.unsigned (N.v52009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52009 s i)) at 1.
  unfold R.v52009, N.v52009.
  rewrite ?node_52007.
  rewrite ?node_52008.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52010 (s : N.State) (i : N.Inputs) :
  R.v52010 (state s) (inputs i) = Zmod.unsigned (N.v52010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52010 s i)) at 1.
  unfold R.v52010, N.v52010.
  rewrite ?node_52006.
  rewrite ?node_52009.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52011 (s : N.State) (i : N.Inputs) :
  R.v52011 (state s) (inputs i) = Zmod.unsigned (N.v52011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52011 s i)) at 1.
  unfold R.v52011, N.v52011.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52012 (s : N.State) (i : N.Inputs) :
  R.v52012 (state s) (inputs i) = Zmod.unsigned (N.v52012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52012 s i)) at 1.
  unfold R.v52012, N.v52012.
  rewrite ?node_11818.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52013 (s : N.State) (i : N.Inputs) :
  R.v52013 (state s) (inputs i) = Zmod.unsigned (N.v52013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52013 s i)) at 1.
  unfold R.v52013, N.v52013.
  unfold R.v6, N.v6.
  rewrite ?node_11814.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52014 (s : N.State) (i : N.Inputs) :
  R.v52014 (state s) (inputs i) = Zmod.unsigned (N.v52014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52014 s i)) at 1.
  unfold R.v52014, N.v52014.
  unfold R.v6, N.v6.
  rewrite ?node_11811.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52015 (s : N.State) (i : N.Inputs) :
  R.v52015 (state s) (inputs i) = Zmod.unsigned (N.v52015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52015 s i)) at 1.
  unfold R.v52015, N.v52015.
  rewrite ?node_52013.
  rewrite ?node_52014.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52016 (s : N.State) (i : N.Inputs) :
  R.v52016 (state s) (inputs i) = Zmod.unsigned (N.v52016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52016 s i)) at 1.
  unfold R.v52016, N.v52016.
  unfold R.v16484, N.v16484.
  rewrite ?node_52015.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52017 (s : N.State) (i : N.Inputs) :
  R.v52017 (state s) (inputs i) = Zmod.unsigned (N.v52017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52017 s i)) at 1.
  unfold R.v52017, N.v52017.
  rewrite ?node_52012.
  rewrite ?node_52016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52018 (s : N.State) (i : N.Inputs) :
  R.v52018 (state s) (inputs i) = Zmod.unsigned (N.v52018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52018 s i)) at 1.
  unfold R.v52018, N.v52018.
  unfold R.v6, N.v6.
  rewrite ?node_52017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52019 (s : N.State) (i : N.Inputs) :
  R.v52019 (state s) (inputs i) = Zmod.unsigned (N.v52019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52019 s i)) at 1.
  unfold R.v52019, N.v52019.
  rewrite ?node_11819.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52020 (s : N.State) (i : N.Inputs) :
  R.v52020 (state s) (inputs i) = Zmod.unsigned (N.v52020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52020 s i)) at 1.
  unfold R.v52020, N.v52020.
  unfold R.v6, N.v6.
  rewrite ?node_11971.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52021 (s : N.State) (i : N.Inputs) :
  R.v52021 (state s) (inputs i) = Zmod.unsigned (N.v52021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52021 s i)) at 1.
  unfold R.v52021, N.v52021.
  rewrite ?node_52019.
  rewrite ?node_52020.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52022 (s : N.State) (i : N.Inputs) :
  R.v52022 (state s) (inputs i) = Zmod.unsigned (N.v52022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52022 s i)) at 1.
  unfold R.v52022, N.v52022.
  rewrite ?node_52018.
  rewrite ?node_52021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52023 (s : N.State) (i : N.Inputs) :
  R.v52023 (state s) (inputs i) = Zmod.unsigned (N.v52023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52023 s i)) at 1.
  unfold R.v52023, N.v52023.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52024 (s : N.State) (i : N.Inputs) :
  R.v52024 (state s) (inputs i) = Zmod.unsigned (N.v52024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52024 s i)) at 1.
  unfold R.v52024, N.v52024.
  rewrite ?node_11943.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52025 (s : N.State) (i : N.Inputs) :
  R.v52025 (state s) (inputs i) = Zmod.unsigned (N.v52025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52025 s i)) at 1.
  unfold R.v52025, N.v52025.
  rewrite ?node_11939.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52026 (s : N.State) (i : N.Inputs) :
  R.v52026 (state s) (inputs i) = Zmod.unsigned (N.v52026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52026 s i)) at 1.
  unfold R.v52026, N.v52026.
  rewrite ?node_11921.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52027 (s : N.State) (i : N.Inputs) :
  R.v52027 (state s) (inputs i) = Zmod.unsigned (N.v52027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52027 s i)) at 1.
  unfold R.v52027, N.v52027.
  unfold R.v6, N.v6.
  rewrite ?node_11901.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52028 (s : N.State) (i : N.Inputs) :
  R.v52028 (state s) (inputs i) = Zmod.unsigned (N.v52028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52028 s i)) at 1.
  unfold R.v52028, N.v52028.
  unfold R.v6, N.v6.
  rewrite ?node_11873.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52029 (s : N.State) (i : N.Inputs) :
  R.v52029 (state s) (inputs i) = Zmod.unsigned (N.v52029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52029 s i)) at 1.
  unfold R.v52029, N.v52029.
  rewrite ?node_52027.
  rewrite ?node_52028.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52030 (s : N.State) (i : N.Inputs) :
  R.v52030 (state s) (inputs i) = Zmod.unsigned (N.v52030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52030 s i)) at 1.
  unfold R.v52030, N.v52030.
  unfold R.v16484, N.v16484.
  rewrite ?node_52029.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52031 (s : N.State) (i : N.Inputs) :
  R.v52031 (state s) (inputs i) = Zmod.unsigned (N.v52031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52031 s i)) at 1.
  unfold R.v52031, N.v52031.
  rewrite ?node_52024.
  rewrite ?node_52025.
  rewrite ?node_52026.
  rewrite ?node_52030.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52032 (s : N.State) (i : N.Inputs) :
  R.v52032 (state s) (inputs i) = Zmod.unsigned (N.v52032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52032 s i)) at 1.
  unfold R.v52032, N.v52032.
  unfold R.v6, N.v6.
  rewrite ?node_52031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52033 (s : N.State) (i : N.Inputs) :
  R.v52033 (state s) (inputs i) = Zmod.unsigned (N.v52033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52033 s i)) at 1.
  unfold R.v52033, N.v52033.
  rewrite ?node_11944.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52034 (s : N.State) (i : N.Inputs) :
  R.v52034 (state s) (inputs i) = Zmod.unsigned (N.v52034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52034 s i)) at 1.
  unfold R.v52034, N.v52034.
  unfold R.v6, N.v6.
  rewrite ?node_12082.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52035 (s : N.State) (i : N.Inputs) :
  R.v52035 (state s) (inputs i) = Zmod.unsigned (N.v52035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52035 s i)) at 1.
  unfold R.v52035, N.v52035.
  unfold R.v6, N.v6.
  rewrite ?node_12110.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52036 (s : N.State) (i : N.Inputs) :
  R.v52036 (state s) (inputs i) = Zmod.unsigned (N.v52036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52036 s i)) at 1.
  unfold R.v52036, N.v52036.
  rewrite ?node_52033.
  rewrite ?node_52034.
  rewrite ?node_52035.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52037 (s : N.State) (i : N.Inputs) :
  R.v52037 (state s) (inputs i) = Zmod.unsigned (N.v52037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52037 s i)) at 1.
  unfold R.v52037, N.v52037.
  rewrite ?node_52032.
  rewrite ?node_52036.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52038 (s : N.State) (i : N.Inputs) :
  R.v52038 (state s) (inputs i) = Zmod.unsigned (N.v52038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52038 s i)) at 1.
  unfold R.v52038, N.v52038.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52039 (s : N.State) (i : N.Inputs) :
  R.v52039 (state s) (inputs i) = Zmod.unsigned (N.v52039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52039 s i)) at 1.
  unfold R.v52039, N.v52039.
  rewrite ?node_11921.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52040 (s : N.State) (i : N.Inputs) :
  R.v52040 (state s) (inputs i) = Zmod.unsigned (N.v52040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52040 s i)) at 1.
  unfold R.v52040, N.v52040.
  unfold R.v6, N.v6.
  rewrite ?node_11901.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52041 (s : N.State) (i : N.Inputs) :
  R.v52041 (state s) (inputs i) = Zmod.unsigned (N.v52041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52041 s i)) at 1.
  unfold R.v52041, N.v52041.
  unfold R.v6, N.v6.
  rewrite ?node_11873.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52042 (s : N.State) (i : N.Inputs) :
  R.v52042 (state s) (inputs i) = Zmod.unsigned (N.v52042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52042 s i)) at 1.
  unfold R.v52042, N.v52042.
  rewrite ?node_52040.
  rewrite ?node_52041.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52043 (s : N.State) (i : N.Inputs) :
  R.v52043 (state s) (inputs i) = Zmod.unsigned (N.v52043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52043 s i)) at 1.
  unfold R.v52043, N.v52043.
  unfold R.v16484, N.v16484.
  rewrite ?node_52042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52044 (s : N.State) (i : N.Inputs) :
  R.v52044 (state s) (inputs i) = Zmod.unsigned (N.v52044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52044 s i)) at 1.
  unfold R.v52044, N.v52044.
  rewrite ?node_52039.
  rewrite ?node_52043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52045 (s : N.State) (i : N.Inputs) :
  R.v52045 (state s) (inputs i) = Zmod.unsigned (N.v52045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52045 s i)) at 1.
  unfold R.v52045, N.v52045.
  unfold R.v6, N.v6.
  rewrite ?node_52044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52046 (s : N.State) (i : N.Inputs) :
  R.v52046 (state s) (inputs i) = Zmod.unsigned (N.v52046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52046 s i)) at 1.
  unfold R.v52046, N.v52046.
  rewrite ?node_11922.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52047 (s : N.State) (i : N.Inputs) :
  R.v52047 (state s) (inputs i) = Zmod.unsigned (N.v52047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52047 s i)) at 1.
  unfold R.v52047, N.v52047.
  unfold R.v6, N.v6.
  rewrite ?node_12082.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52048 (s : N.State) (i : N.Inputs) :
  R.v52048 (state s) (inputs i) = Zmod.unsigned (N.v52048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52048 s i)) at 1.
  unfold R.v52048, N.v52048.
  rewrite ?node_52046.
  rewrite ?node_52047.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52049 (s : N.State) (i : N.Inputs) :
  R.v52049 (state s) (inputs i) = Zmod.unsigned (N.v52049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52049 s i)) at 1.
  unfold R.v52049, N.v52049.
  rewrite ?node_52045.
  rewrite ?node_52048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52050 (s : N.State) (i : N.Inputs) :
  R.v52050 (state s) (inputs i) = Zmod.unsigned (N.v52050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52050 s i)) at 1.
  unfold R.v52050, N.v52050.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52051 (s : N.State) (i : N.Inputs) :
  R.v52051 (state s) (inputs i) = Zmod.unsigned (N.v52051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52051 s i)) at 1.
  unfold R.v52051, N.v52051.
  rewrite ?node_11943.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52052 (s : N.State) (i : N.Inputs) :
  R.v52052 (state s) (inputs i) = Zmod.unsigned (N.v52052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52052 s i)) at 1.
  unfold R.v52052, N.v52052.
  unfold R.v6, N.v6.
  rewrite ?node_11939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52053 (s : N.State) (i : N.Inputs) :
  R.v52053 (state s) (inputs i) = Zmod.unsigned (N.v52053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52053 s i)) at 1.
  unfold R.v52053, N.v52053.
  unfold R.v6, N.v6.
  rewrite ?node_11922.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52054 (s : N.State) (i : N.Inputs) :
  R.v52054 (state s) (inputs i) = Zmod.unsigned (N.v52054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52054 s i)) at 1.
  unfold R.v52054, N.v52054.
  rewrite ?node_52052.
  rewrite ?node_52053.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52055 (s : N.State) (i : N.Inputs) :
  R.v52055 (state s) (inputs i) = Zmod.unsigned (N.v52055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52055 s i)) at 1.
  unfold R.v52055, N.v52055.
  unfold R.v16484, N.v16484.
  rewrite ?node_52054.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52056 (s : N.State) (i : N.Inputs) :
  R.v52056 (state s) (inputs i) = Zmod.unsigned (N.v52056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52056 s i)) at 1.
  unfold R.v52056, N.v52056.
  rewrite ?node_52051.
  rewrite ?node_52055.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52057 (s : N.State) (i : N.Inputs) :
  R.v52057 (state s) (inputs i) = Zmod.unsigned (N.v52057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52057 s i)) at 1.
  unfold R.v52057, N.v52057.
  unfold R.v6, N.v6.
  rewrite ?node_52056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52058 (s : N.State) (i : N.Inputs) :
  R.v52058 (state s) (inputs i) = Zmod.unsigned (N.v52058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52058 s i)) at 1.
  unfold R.v52058, N.v52058.
  rewrite ?node_11944.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52059 (s : N.State) (i : N.Inputs) :
  R.v52059 (state s) (inputs i) = Zmod.unsigned (N.v52059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52059 s i)) at 1.
  unfold R.v52059, N.v52059.
  unfold R.v6, N.v6.
  rewrite ?node_12110.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52060 (s : N.State) (i : N.Inputs) :
  R.v52060 (state s) (inputs i) = Zmod.unsigned (N.v52060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52060 s i)) at 1.
  unfold R.v52060, N.v52060.
  rewrite ?node_52058.
  rewrite ?node_52059.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52061 (s : N.State) (i : N.Inputs) :
  R.v52061 (state s) (inputs i) = Zmod.unsigned (N.v52061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52061 s i)) at 1.
  unfold R.v52061, N.v52061.
  rewrite ?node_52057.
  rewrite ?node_52060.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52062 (s : N.State) (i : N.Inputs) :
  R.v52062 (state s) (inputs i) = Zmod.unsigned (N.v52062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52062 s i)) at 1.
  unfold R.v52062, N.v52062.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52063 (s : N.State) (i : N.Inputs) :
  R.v52063 (state s) (inputs i) = Zmod.unsigned (N.v52063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52063 s i)) at 1.
  unfold R.v52063, N.v52063.
  rewrite ?node_11962.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52064 (s : N.State) (i : N.Inputs) :
  R.v52064 (state s) (inputs i) = Zmod.unsigned (N.v52064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52064 s i)) at 1.
  unfold R.v52064, N.v52064.
  rewrite ?node_11958.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52065 (s : N.State) (i : N.Inputs) :
  R.v52065 (state s) (inputs i) = Zmod.unsigned (N.v52065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52065 s i)) at 1.
  unfold R.v52065, N.v52065.
  rewrite ?node_11954.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52066 (s : N.State) (i : N.Inputs) :
  R.v52066 (state s) (inputs i) = Zmod.unsigned (N.v52066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52066 s i)) at 1.
  unfold R.v52066, N.v52066.
  unfold R.v6, N.v6.
  rewrite ?node_11950.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52067 (s : N.State) (i : N.Inputs) :
  R.v52067 (state s) (inputs i) = Zmod.unsigned (N.v52067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52067 s i)) at 1.
  unfold R.v52067, N.v52067.
  unfold R.v6, N.v6.
  rewrite ?node_11947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52068 (s : N.State) (i : N.Inputs) :
  R.v52068 (state s) (inputs i) = Zmod.unsigned (N.v52068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52068 s i)) at 1.
  unfold R.v52068, N.v52068.
  rewrite ?node_52066.
  rewrite ?node_52067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52069 (s : N.State) (i : N.Inputs) :
  R.v52069 (state s) (inputs i) = Zmod.unsigned (N.v52069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52069 s i)) at 1.
  unfold R.v52069, N.v52069.
  unfold R.v16484, N.v16484.
  rewrite ?node_52068.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52070 (s : N.State) (i : N.Inputs) :
  R.v52070 (state s) (inputs i) = Zmod.unsigned (N.v52070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52070 s i)) at 1.
  unfold R.v52070, N.v52070.
  rewrite ?node_52063.
  rewrite ?node_52064.
  rewrite ?node_52065.
  rewrite ?node_52069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52071 (s : N.State) (i : N.Inputs) :
  R.v52071 (state s) (inputs i) = Zmod.unsigned (N.v52071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52071 s i)) at 1.
  unfold R.v52071, N.v52071.
  unfold R.v6, N.v6.
  rewrite ?node_52070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52072 (s : N.State) (i : N.Inputs) :
  R.v52072 (state s) (inputs i) = Zmod.unsigned (N.v52072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52072 s i)) at 1.
  unfold R.v52072, N.v52072.
  rewrite ?node_11963.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52073 (s : N.State) (i : N.Inputs) :
  R.v52073 (state s) (inputs i) = Zmod.unsigned (N.v52073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52073 s i)) at 1.
  unfold R.v52073, N.v52073.
  unfold R.v6, N.v6.
  rewrite ?node_12101.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52074 (s : N.State) (i : N.Inputs) :
  R.v52074 (state s) (inputs i) = Zmod.unsigned (N.v52074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52074 s i)) at 1.
  unfold R.v52074, N.v52074.
  unfold R.v6, N.v6.
  rewrite ?node_12118.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52075 (s : N.State) (i : N.Inputs) :
  R.v52075 (state s) (inputs i) = Zmod.unsigned (N.v52075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52075 s i)) at 1.
  unfold R.v52075, N.v52075.
  rewrite ?node_52072.
  rewrite ?node_52073.
  rewrite ?node_52074.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52076 (s : N.State) (i : N.Inputs) :
  R.v52076 (state s) (inputs i) = Zmod.unsigned (N.v52076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52076 s i)) at 1.
  unfold R.v52076, N.v52076.
  rewrite ?node_52071.
  rewrite ?node_52075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52077 (s : N.State) (i : N.Inputs) :
  R.v52077 (state s) (inputs i) = Zmod.unsigned (N.v52077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52077 s i)) at 1.
  unfold R.v52077, N.v52077.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52078 (s : N.State) (i : N.Inputs) :
  R.v52078 (state s) (inputs i) = Zmod.unsigned (N.v52078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52078 s i)) at 1.
  unfold R.v52078, N.v52078.
  rewrite ?node_11954.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52079 (s : N.State) (i : N.Inputs) :
  R.v52079 (state s) (inputs i) = Zmod.unsigned (N.v52079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52079 s i)) at 1.
  unfold R.v52079, N.v52079.
  unfold R.v6, N.v6.
  rewrite ?node_11950.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52080 (s : N.State) (i : N.Inputs) :
  R.v52080 (state s) (inputs i) = Zmod.unsigned (N.v52080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52080 s i)) at 1.
  unfold R.v52080, N.v52080.
  unfold R.v6, N.v6.
  rewrite ?node_11947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52081 (s : N.State) (i : N.Inputs) :
  R.v52081 (state s) (inputs i) = Zmod.unsigned (N.v52081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52081 s i)) at 1.
  unfold R.v52081, N.v52081.
  rewrite ?node_52079.
  rewrite ?node_52080.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52082 (s : N.State) (i : N.Inputs) :
  R.v52082 (state s) (inputs i) = Zmod.unsigned (N.v52082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52082 s i)) at 1.
  unfold R.v52082, N.v52082.
  unfold R.v16484, N.v16484.
  rewrite ?node_52081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52083 (s : N.State) (i : N.Inputs) :
  R.v52083 (state s) (inputs i) = Zmod.unsigned (N.v52083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52083 s i)) at 1.
  unfold R.v52083, N.v52083.
  rewrite ?node_52078.
  rewrite ?node_52082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52084 (s : N.State) (i : N.Inputs) :
  R.v52084 (state s) (inputs i) = Zmod.unsigned (N.v52084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52084 s i)) at 1.
  unfold R.v52084, N.v52084.
  unfold R.v6, N.v6.
  rewrite ?node_52083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52085 (s : N.State) (i : N.Inputs) :
  R.v52085 (state s) (inputs i) = Zmod.unsigned (N.v52085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52085 s i)) at 1.
  unfold R.v52085, N.v52085.
  rewrite ?node_11955.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52086 (s : N.State) (i : N.Inputs) :
  R.v52086 (state s) (inputs i) = Zmod.unsigned (N.v52086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52086 s i)) at 1.
  unfold R.v52086, N.v52086.
  unfold R.v6, N.v6.
  rewrite ?node_12101.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52087 (s : N.State) (i : N.Inputs) :
  R.v52087 (state s) (inputs i) = Zmod.unsigned (N.v52087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52087 s i)) at 1.
  unfold R.v52087, N.v52087.
  rewrite ?node_52085.
  rewrite ?node_52086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52088 (s : N.State) (i : N.Inputs) :
  R.v52088 (state s) (inputs i) = Zmod.unsigned (N.v52088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52088 s i)) at 1.
  unfold R.v52088, N.v52088.
  rewrite ?node_52084.
  rewrite ?node_52087.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52089 (s : N.State) (i : N.Inputs) :
  R.v52089 (state s) (inputs i) = Zmod.unsigned (N.v52089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52089 s i)) at 1.
  unfold R.v52089, N.v52089.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52090 (s : N.State) (i : N.Inputs) :
  R.v52090 (state s) (inputs i) = Zmod.unsigned (N.v52090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52090 s i)) at 1.
  unfold R.v52090, N.v52090.
  rewrite ?node_11962.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52091 (s : N.State) (i : N.Inputs) :
  R.v52091 (state s) (inputs i) = Zmod.unsigned (N.v52091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52091 s i)) at 1.
  unfold R.v52091, N.v52091.
  unfold R.v6, N.v6.
  rewrite ?node_11958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52092 (s : N.State) (i : N.Inputs) :
  R.v52092 (state s) (inputs i) = Zmod.unsigned (N.v52092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52092 s i)) at 1.
  unfold R.v52092, N.v52092.
  unfold R.v6, N.v6.
  rewrite ?node_11955.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52093 (s : N.State) (i : N.Inputs) :
  R.v52093 (state s) (inputs i) = Zmod.unsigned (N.v52093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52093 s i)) at 1.
  unfold R.v52093, N.v52093.
  rewrite ?node_52091.
  rewrite ?node_52092.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52094 (s : N.State) (i : N.Inputs) :
  R.v52094 (state s) (inputs i) = Zmod.unsigned (N.v52094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52094 s i)) at 1.
  unfold R.v52094, N.v52094.
  unfold R.v16484, N.v16484.
  rewrite ?node_52093.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52095 (s : N.State) (i : N.Inputs) :
  R.v52095 (state s) (inputs i) = Zmod.unsigned (N.v52095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52095 s i)) at 1.
  unfold R.v52095, N.v52095.
  rewrite ?node_52090.
  rewrite ?node_52094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52096 (s : N.State) (i : N.Inputs) :
  R.v52096 (state s) (inputs i) = Zmod.unsigned (N.v52096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52096 s i)) at 1.
  unfold R.v52096, N.v52096.
  unfold R.v6, N.v6.
  rewrite ?node_52095.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52097 (s : N.State) (i : N.Inputs) :
  R.v52097 (state s) (inputs i) = Zmod.unsigned (N.v52097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52097 s i)) at 1.
  unfold R.v52097, N.v52097.
  rewrite ?node_11963.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52098 (s : N.State) (i : N.Inputs) :
  R.v52098 (state s) (inputs i) = Zmod.unsigned (N.v52098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52098 s i)) at 1.
  unfold R.v52098, N.v52098.
  unfold R.v6, N.v6.
  rewrite ?node_12118.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52099 (s : N.State) (i : N.Inputs) :
  R.v52099 (state s) (inputs i) = Zmod.unsigned (N.v52099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52099 s i)) at 1.
  unfold R.v52099, N.v52099.
  rewrite ?node_52097.
  rewrite ?node_52098.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52100 (s : N.State) (i : N.Inputs) :
  R.v52100 (state s) (inputs i) = Zmod.unsigned (N.v52100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52100 s i)) at 1.
  unfold R.v52100, N.v52100.
  rewrite ?node_52096.
  rewrite ?node_52099.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52101 (s : N.State) (i : N.Inputs) :
  R.v52101 (state s) (inputs i) = Zmod.unsigned (N.v52101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52101 s i)) at 1.
  unfold R.v52101, N.v52101.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52102 (s : N.State) (i : N.Inputs) :
  R.v52102 (state s) (inputs i) = Zmod.unsigned (N.v52102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52102 s i)) at 1.
  unfold R.v52102, N.v52102.
  rewrite ?node_12082.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52103 (s : N.State) (i : N.Inputs) :
  R.v52103 (state s) (inputs i) = Zmod.unsigned (N.v52103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52103 s i)) at 1.
  unfold R.v52103, N.v52103.
  rewrite ?node_12078.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52104 (s : N.State) (i : N.Inputs) :
  R.v52104 (state s) (inputs i) = Zmod.unsigned (N.v52104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52104 s i)) at 1.
  unfold R.v52104, N.v52104.
  rewrite ?node_12066.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52105 (s : N.State) (i : N.Inputs) :
  R.v52105 (state s) (inputs i) = Zmod.unsigned (N.v52105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52105 s i)) at 1.
  unfold R.v52105, N.v52105.
  unfold R.v6, N.v6.
  rewrite ?node_12046.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52106 (s : N.State) (i : N.Inputs) :
  R.v52106 (state s) (inputs i) = Zmod.unsigned (N.v52106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52106 s i)) at 1.
  unfold R.v52106, N.v52106.
  unfold R.v6, N.v6.
  rewrite ?node_12018.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52107 (s : N.State) (i : N.Inputs) :
  R.v52107 (state s) (inputs i) = Zmod.unsigned (N.v52107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52107 s i)) at 1.
  unfold R.v52107, N.v52107.
  rewrite ?node_52105.
  rewrite ?node_52106.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52108 (s : N.State) (i : N.Inputs) :
  R.v52108 (state s) (inputs i) = Zmod.unsigned (N.v52108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52108 s i)) at 1.
  unfold R.v52108, N.v52108.
  unfold R.v16484, N.v16484.
  rewrite ?node_52107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52109 (s : N.State) (i : N.Inputs) :
  R.v52109 (state s) (inputs i) = Zmod.unsigned (N.v52109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52109 s i)) at 1.
  unfold R.v52109, N.v52109.
  rewrite ?node_52102.
  rewrite ?node_52103.
  rewrite ?node_52104.
  rewrite ?node_52108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52110 (s : N.State) (i : N.Inputs) :
  R.v52110 (state s) (inputs i) = Zmod.unsigned (N.v52110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52110 s i)) at 1.
  unfold R.v52110, N.v52110.
  unfold R.v6, N.v6.
  rewrite ?node_52109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52111 (s : N.State) (i : N.Inputs) :
  R.v52111 (state s) (inputs i) = Zmod.unsigned (N.v52111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52111 s i)) at 1.
  unfold R.v52111, N.v52111.
  rewrite ?node_12083.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52112 (s : N.State) (i : N.Inputs) :
  R.v52112 (state s) (inputs i) = Zmod.unsigned (N.v52112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52112 s i)) at 1.
  unfold R.v52112, N.v52112.
  unfold R.v6, N.v6.
  rewrite ?node_12223.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52113 (s : N.State) (i : N.Inputs) :
  R.v52113 (state s) (inputs i) = Zmod.unsigned (N.v52113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52113 s i)) at 1.
  unfold R.v52113, N.v52113.
  unfold R.v6, N.v6.
  rewrite ?node_12247.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52114 (s : N.State) (i : N.Inputs) :
  R.v52114 (state s) (inputs i) = Zmod.unsigned (N.v52114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52114 s i)) at 1.
  unfold R.v52114, N.v52114.
  rewrite ?node_52111.
  rewrite ?node_52112.
  rewrite ?node_52113.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52115 (s : N.State) (i : N.Inputs) :
  R.v52115 (state s) (inputs i) = Zmod.unsigned (N.v52115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52115 s i)) at 1.
  unfold R.v52115, N.v52115.
  rewrite ?node_52110.
  rewrite ?node_52114.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52116 (s : N.State) (i : N.Inputs) :
  R.v52116 (state s) (inputs i) = Zmod.unsigned (N.v52116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52116 s i)) at 1.
  unfold R.v52116, N.v52116.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52117 (s : N.State) (i : N.Inputs) :
  R.v52117 (state s) (inputs i) = Zmod.unsigned (N.v52117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52117 s i)) at 1.
  unfold R.v52117, N.v52117.
  rewrite ?node_12066.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52118 (s : N.State) (i : N.Inputs) :
  R.v52118 (state s) (inputs i) = Zmod.unsigned (N.v52118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52118 s i)) at 1.
  unfold R.v52118, N.v52118.
  unfold R.v6, N.v6.
  rewrite ?node_12046.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52119 (s : N.State) (i : N.Inputs) :
  R.v52119 (state s) (inputs i) = Zmod.unsigned (N.v52119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52119 s i)) at 1.
  unfold R.v52119, N.v52119.
  unfold R.v6, N.v6.
  rewrite ?node_12018.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52120 (s : N.State) (i : N.Inputs) :
  R.v52120 (state s) (inputs i) = Zmod.unsigned (N.v52120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52120 s i)) at 1.
  unfold R.v52120, N.v52120.
  rewrite ?node_52118.
  rewrite ?node_52119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52121 (s : N.State) (i : N.Inputs) :
  R.v52121 (state s) (inputs i) = Zmod.unsigned (N.v52121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52121 s i)) at 1.
  unfold R.v52121, N.v52121.
  unfold R.v16484, N.v16484.
  rewrite ?node_52120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52122 (s : N.State) (i : N.Inputs) :
  R.v52122 (state s) (inputs i) = Zmod.unsigned (N.v52122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52122 s i)) at 1.
  unfold R.v52122, N.v52122.
  rewrite ?node_52117.
  rewrite ?node_52121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52123 (s : N.State) (i : N.Inputs) :
  R.v52123 (state s) (inputs i) = Zmod.unsigned (N.v52123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52123 s i)) at 1.
  unfold R.v52123, N.v52123.
  unfold R.v6, N.v6.
  rewrite ?node_52122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52124 (s : N.State) (i : N.Inputs) :
  R.v52124 (state s) (inputs i) = Zmod.unsigned (N.v52124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52124 s i)) at 1.
  unfold R.v52124, N.v52124.
  rewrite ?node_12067.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52125 (s : N.State) (i : N.Inputs) :
  R.v52125 (state s) (inputs i) = Zmod.unsigned (N.v52125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52125 s i)) at 1.
  unfold R.v52125, N.v52125.
  unfold R.v6, N.v6.
  rewrite ?node_12223.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52126 (s : N.State) (i : N.Inputs) :
  R.v52126 (state s) (inputs i) = Zmod.unsigned (N.v52126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52126 s i)) at 1.
  unfold R.v52126, N.v52126.
  rewrite ?node_52124.
  rewrite ?node_52125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52127 (s : N.State) (i : N.Inputs) :
  R.v52127 (state s) (inputs i) = Zmod.unsigned (N.v52127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52127 s i)) at 1.
  unfold R.v52127, N.v52127.
  rewrite ?node_52123.
  rewrite ?node_52126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52128 (s : N.State) (i : N.Inputs) :
  R.v52128 (state s) (inputs i) = Zmod.unsigned (N.v52128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52128 s i)) at 1.
  unfold R.v52128, N.v52128.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52129 (s : N.State) (i : N.Inputs) :
  R.v52129 (state s) (inputs i) = Zmod.unsigned (N.v52129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52129 s i)) at 1.
  unfold R.v52129, N.v52129.
  rewrite ?node_12082.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52130 (s : N.State) (i : N.Inputs) :
  R.v52130 (state s) (inputs i) = Zmod.unsigned (N.v52130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52130 s i)) at 1.
  unfold R.v52130, N.v52130.
  unfold R.v6, N.v6.
  rewrite ?node_12078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52131 (s : N.State) (i : N.Inputs) :
  R.v52131 (state s) (inputs i) = Zmod.unsigned (N.v52131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52131 s i)) at 1.
  unfold R.v52131, N.v52131.
  unfold R.v6, N.v6.
  rewrite ?node_12067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52132 (s : N.State) (i : N.Inputs) :
  R.v52132 (state s) (inputs i) = Zmod.unsigned (N.v52132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52132 s i)) at 1.
  unfold R.v52132, N.v52132.
  rewrite ?node_52130.
  rewrite ?node_52131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52133 (s : N.State) (i : N.Inputs) :
  R.v52133 (state s) (inputs i) = Zmod.unsigned (N.v52133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52133 s i)) at 1.
  unfold R.v52133, N.v52133.
  unfold R.v16484, N.v16484.
  rewrite ?node_52132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52134 (s : N.State) (i : N.Inputs) :
  R.v52134 (state s) (inputs i) = Zmod.unsigned (N.v52134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52134 s i)) at 1.
  unfold R.v52134, N.v52134.
  rewrite ?node_52129.
  rewrite ?node_52133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52135 (s : N.State) (i : N.Inputs) :
  R.v52135 (state s) (inputs i) = Zmod.unsigned (N.v52135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52135 s i)) at 1.
  unfold R.v52135, N.v52135.
  unfold R.v6, N.v6.
  rewrite ?node_52134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52136 (s : N.State) (i : N.Inputs) :
  R.v52136 (state s) (inputs i) = Zmod.unsigned (N.v52136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52136 s i)) at 1.
  unfold R.v52136, N.v52136.
  rewrite ?node_12083.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52137 (s : N.State) (i : N.Inputs) :
  R.v52137 (state s) (inputs i) = Zmod.unsigned (N.v52137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52137 s i)) at 1.
  unfold R.v52137, N.v52137.
  unfold R.v6, N.v6.
  rewrite ?node_12247.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52138 (s : N.State) (i : N.Inputs) :
  R.v52138 (state s) (inputs i) = Zmod.unsigned (N.v52138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52138 s i)) at 1.
  unfold R.v52138, N.v52138.
  rewrite ?node_52136.
  rewrite ?node_52137.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52139 (s : N.State) (i : N.Inputs) :
  R.v52139 (state s) (inputs i) = Zmod.unsigned (N.v52139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52139 s i)) at 1.
  unfold R.v52139, N.v52139.
  rewrite ?node_52135.
  rewrite ?node_52138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52140 (s : N.State) (i : N.Inputs) :
  R.v52140 (state s) (inputs i) = Zmod.unsigned (N.v52140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52140 s i)) at 1.
  unfold R.v52140, N.v52140.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52141 (s : N.State) (i : N.Inputs) :
  R.v52141 (state s) (inputs i) = Zmod.unsigned (N.v52141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52141 s i)) at 1.
  unfold R.v52141, N.v52141.
  rewrite ?node_12101.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52142 (s : N.State) (i : N.Inputs) :
  R.v52142 (state s) (inputs i) = Zmod.unsigned (N.v52142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52142 s i)) at 1.
  unfold R.v52142, N.v52142.
  rewrite ?node_12097.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52143 (s : N.State) (i : N.Inputs) :
  R.v52143 (state s) (inputs i) = Zmod.unsigned (N.v52143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52143 s i)) at 1.
  unfold R.v52143, N.v52143.
  rewrite ?node_12093.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52144 (s : N.State) (i : N.Inputs) :
  R.v52144 (state s) (inputs i) = Zmod.unsigned (N.v52144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52144 s i)) at 1.
  unfold R.v52144, N.v52144.
  unfold R.v6, N.v6.
  rewrite ?node_12089.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52145 (s : N.State) (i : N.Inputs) :
  R.v52145 (state s) (inputs i) = Zmod.unsigned (N.v52145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52145 s i)) at 1.
  unfold R.v52145, N.v52145.
  unfold R.v6, N.v6.
  rewrite ?node_12086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52146 (s : N.State) (i : N.Inputs) :
  R.v52146 (state s) (inputs i) = Zmod.unsigned (N.v52146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52146 s i)) at 1.
  unfold R.v52146, N.v52146.
  rewrite ?node_52144.
  rewrite ?node_52145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52147 (s : N.State) (i : N.Inputs) :
  R.v52147 (state s) (inputs i) = Zmod.unsigned (N.v52147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52147 s i)) at 1.
  unfold R.v52147, N.v52147.
  unfold R.v16484, N.v16484.
  rewrite ?node_52146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52148 (s : N.State) (i : N.Inputs) :
  R.v52148 (state s) (inputs i) = Zmod.unsigned (N.v52148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52148 s i)) at 1.
  unfold R.v52148, N.v52148.
  rewrite ?node_52141.
  rewrite ?node_52142.
  rewrite ?node_52143.
  rewrite ?node_52147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52149 (s : N.State) (i : N.Inputs) :
  R.v52149 (state s) (inputs i) = Zmod.unsigned (N.v52149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52149 s i)) at 1.
  unfold R.v52149, N.v52149.
  unfold R.v6, N.v6.
  rewrite ?node_52148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52150 (s : N.State) (i : N.Inputs) :
  R.v52150 (state s) (inputs i) = Zmod.unsigned (N.v52150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52150 s i)) at 1.
  unfold R.v52150, N.v52150.
  rewrite ?node_12102.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52151 (s : N.State) (i : N.Inputs) :
  R.v52151 (state s) (inputs i) = Zmod.unsigned (N.v52151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52151 s i)) at 1.
  unfold R.v52151, N.v52151.
  unfold R.v6, N.v6.
  rewrite ?node_12242.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52152 (s : N.State) (i : N.Inputs) :
  R.v52152 (state s) (inputs i) = Zmod.unsigned (N.v52152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52152 s i)) at 1.
  unfold R.v52152, N.v52152.
  unfold R.v6, N.v6.
  rewrite ?node_12251.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52153 (s : N.State) (i : N.Inputs) :
  R.v52153 (state s) (inputs i) = Zmod.unsigned (N.v52153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52153 s i)) at 1.
  unfold R.v52153, N.v52153.
  rewrite ?node_52150.
  rewrite ?node_52151.
  rewrite ?node_52152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52154 (s : N.State) (i : N.Inputs) :
  R.v52154 (state s) (inputs i) = Zmod.unsigned (N.v52154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52154 s i)) at 1.
  unfold R.v52154, N.v52154.
  rewrite ?node_52149.
  rewrite ?node_52153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52155 (s : N.State) (i : N.Inputs) :
  R.v52155 (state s) (inputs i) = Zmod.unsigned (N.v52155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52155 s i)) at 1.
  unfold R.v52155, N.v52155.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52156 (s : N.State) (i : N.Inputs) :
  R.v52156 (state s) (inputs i) = Zmod.unsigned (N.v52156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52156 s i)) at 1.
  unfold R.v52156, N.v52156.
  rewrite ?node_12093.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52157 (s : N.State) (i : N.Inputs) :
  R.v52157 (state s) (inputs i) = Zmod.unsigned (N.v52157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52157 s i)) at 1.
  unfold R.v52157, N.v52157.
  unfold R.v6, N.v6.
  rewrite ?node_12089.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52158 (s : N.State) (i : N.Inputs) :
  R.v52158 (state s) (inputs i) = Zmod.unsigned (N.v52158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52158 s i)) at 1.
  unfold R.v52158, N.v52158.
  unfold R.v6, N.v6.
  rewrite ?node_12086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52159 (s : N.State) (i : N.Inputs) :
  R.v52159 (state s) (inputs i) = Zmod.unsigned (N.v52159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52159 s i)) at 1.
  unfold R.v52159, N.v52159.
  rewrite ?node_52157.
  rewrite ?node_52158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52160 (s : N.State) (i : N.Inputs) :
  R.v52160 (state s) (inputs i) = Zmod.unsigned (N.v52160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52160 s i)) at 1.
  unfold R.v52160, N.v52160.
  unfold R.v16484, N.v16484.
  rewrite ?node_52159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52161 (s : N.State) (i : N.Inputs) :
  R.v52161 (state s) (inputs i) = Zmod.unsigned (N.v52161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52161 s i)) at 1.
  unfold R.v52161, N.v52161.
  rewrite ?node_52156.
  rewrite ?node_52160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52162 (s : N.State) (i : N.Inputs) :
  R.v52162 (state s) (inputs i) = Zmod.unsigned (N.v52162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52162 s i)) at 1.
  unfold R.v52162, N.v52162.
  unfold R.v6, N.v6.
  rewrite ?node_52161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52163 (s : N.State) (i : N.Inputs) :
  R.v52163 (state s) (inputs i) = Zmod.unsigned (N.v52163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52163 s i)) at 1.
  unfold R.v52163, N.v52163.
  rewrite ?node_12094.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52164 (s : N.State) (i : N.Inputs) :
  R.v52164 (state s) (inputs i) = Zmod.unsigned (N.v52164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52164 s i)) at 1.
  unfold R.v52164, N.v52164.
  unfold R.v6, N.v6.
  rewrite ?node_12242.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52165 (s : N.State) (i : N.Inputs) :
  R.v52165 (state s) (inputs i) = Zmod.unsigned (N.v52165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52165 s i)) at 1.
  unfold R.v52165, N.v52165.
  rewrite ?node_52163.
  rewrite ?node_52164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52166 (s : N.State) (i : N.Inputs) :
  R.v52166 (state s) (inputs i) = Zmod.unsigned (N.v52166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52166 s i)) at 1.
  unfold R.v52166, N.v52166.
  rewrite ?node_52162.
  rewrite ?node_52165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52167 (s : N.State) (i : N.Inputs) :
  R.v52167 (state s) (inputs i) = Zmod.unsigned (N.v52167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52167 s i)) at 1.
  unfold R.v52167, N.v52167.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52168 (s : N.State) (i : N.Inputs) :
  R.v52168 (state s) (inputs i) = Zmod.unsigned (N.v52168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52168 s i)) at 1.
  unfold R.v52168, N.v52168.
  rewrite ?node_12101.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52169 (s : N.State) (i : N.Inputs) :
  R.v52169 (state s) (inputs i) = Zmod.unsigned (N.v52169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52169 s i)) at 1.
  unfold R.v52169, N.v52169.
  unfold R.v6, N.v6.
  rewrite ?node_12097.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52170 (s : N.State) (i : N.Inputs) :
  R.v52170 (state s) (inputs i) = Zmod.unsigned (N.v52170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52170 s i)) at 1.
  unfold R.v52170, N.v52170.
  unfold R.v6, N.v6.
  rewrite ?node_12094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52171 (s : N.State) (i : N.Inputs) :
  R.v52171 (state s) (inputs i) = Zmod.unsigned (N.v52171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52171 s i)) at 1.
  unfold R.v52171, N.v52171.
  rewrite ?node_52169.
  rewrite ?node_52170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52172 (s : N.State) (i : N.Inputs) :
  R.v52172 (state s) (inputs i) = Zmod.unsigned (N.v52172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52172 s i)) at 1.
  unfold R.v52172, N.v52172.
  unfold R.v16484, N.v16484.
  rewrite ?node_52171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52173 (s : N.State) (i : N.Inputs) :
  R.v52173 (state s) (inputs i) = Zmod.unsigned (N.v52173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52173 s i)) at 1.
  unfold R.v52173, N.v52173.
  rewrite ?node_52168.
  rewrite ?node_52172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52174 (s : N.State) (i : N.Inputs) :
  R.v52174 (state s) (inputs i) = Zmod.unsigned (N.v52174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52174 s i)) at 1.
  unfold R.v52174, N.v52174.
  unfold R.v6, N.v6.
  rewrite ?node_52173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52175 (s : N.State) (i : N.Inputs) :
  R.v52175 (state s) (inputs i) = Zmod.unsigned (N.v52175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52175 s i)) at 1.
  unfold R.v52175, N.v52175.
  rewrite ?node_12102.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52176 (s : N.State) (i : N.Inputs) :
  R.v52176 (state s) (inputs i) = Zmod.unsigned (N.v52176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52176 s i)) at 1.
  unfold R.v52176, N.v52176.
  unfold R.v6, N.v6.
  rewrite ?node_12251.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52177 (s : N.State) (i : N.Inputs) :
  R.v52177 (state s) (inputs i) = Zmod.unsigned (N.v52177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52177 s i)) at 1.
  unfold R.v52177, N.v52177.
  rewrite ?node_52175.
  rewrite ?node_52176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52178 (s : N.State) (i : N.Inputs) :
  R.v52178 (state s) (inputs i) = Zmod.unsigned (N.v52178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52178 s i)) at 1.
  unfold R.v52178, N.v52178.
  rewrite ?node_52174.
  rewrite ?node_52177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52179 (s : N.State) (i : N.Inputs) :
  R.v52179 (state s) (inputs i) = Zmod.unsigned (N.v52179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52179 s i)) at 1.
  unfold R.v52179, N.v52179.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52180 (s : N.State) (i : N.Inputs) :
  R.v52180 (state s) (inputs i) = Zmod.unsigned (N.v52180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52180 s i)) at 1.
  unfold R.v52180, N.v52180.
  rewrite ?node_12223.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52181 (s : N.State) (i : N.Inputs) :
  R.v52181 (state s) (inputs i) = Zmod.unsigned (N.v52181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52181 s i)) at 1.
  unfold R.v52181, N.v52181.
  rewrite ?node_12219.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52182 (s : N.State) (i : N.Inputs) :
  R.v52182 (state s) (inputs i) = Zmod.unsigned (N.v52182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52182 s i)) at 1.
  unfold R.v52182, N.v52182.
  rewrite ?node_12211.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52183 (s : N.State) (i : N.Inputs) :
  R.v52183 (state s) (inputs i) = Zmod.unsigned (N.v52183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52183 s i)) at 1.
  unfold R.v52183, N.v52183.
  unfold R.v6, N.v6.
  rewrite ?node_12191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52184 (s : N.State) (i : N.Inputs) :
  R.v52184 (state s) (inputs i) = Zmod.unsigned (N.v52184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52184 s i)) at 1.
  unfold R.v52184, N.v52184.
  unfold R.v6, N.v6.
  rewrite ?node_12160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52185 (s : N.State) (i : N.Inputs) :
  R.v52185 (state s) (inputs i) = Zmod.unsigned (N.v52185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52185 s i)) at 1.
  unfold R.v52185, N.v52185.
  rewrite ?node_52183.
  rewrite ?node_52184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52186 (s : N.State) (i : N.Inputs) :
  R.v52186 (state s) (inputs i) = Zmod.unsigned (N.v52186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52186 s i)) at 1.
  unfold R.v52186, N.v52186.
  unfold R.v16484, N.v16484.
  rewrite ?node_52185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52187 (s : N.State) (i : N.Inputs) :
  R.v52187 (state s) (inputs i) = Zmod.unsigned (N.v52187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52187 s i)) at 1.
  unfold R.v52187, N.v52187.
  rewrite ?node_52180.
  rewrite ?node_52181.
  rewrite ?node_52182.
  rewrite ?node_52186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52188 (s : N.State) (i : N.Inputs) :
  R.v52188 (state s) (inputs i) = Zmod.unsigned (N.v52188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52188 s i)) at 1.
  unfold R.v52188, N.v52188.
  unfold R.v6, N.v6.
  rewrite ?node_52187.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52189 (s : N.State) (i : N.Inputs) :
  R.v52189 (state s) (inputs i) = Zmod.unsigned (N.v52189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52189 s i)) at 1.
  unfold R.v52189, N.v52189.
  rewrite ?node_12224.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52190 (s : N.State) (i : N.Inputs) :
  R.v52190 (state s) (inputs i) = Zmod.unsigned (N.v52190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52190 s i)) at 1.
  unfold R.v52190, N.v52190.
  unfold R.v6, N.v6.
  rewrite ?node_12363.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52191 (s : N.State) (i : N.Inputs) :
  R.v52191 (state s) (inputs i) = Zmod.unsigned (N.v52191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52191 s i)) at 1.
  unfold R.v52191, N.v52191.
  unfold R.v6, N.v6.
  rewrite ?node_12385.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52192 (s : N.State) (i : N.Inputs) :
  R.v52192 (state s) (inputs i) = Zmod.unsigned (N.v52192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52192 s i)) at 1.
  unfold R.v52192, N.v52192.
  rewrite ?node_52189.
  rewrite ?node_52190.
  rewrite ?node_52191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52193 (s : N.State) (i : N.Inputs) :
  R.v52193 (state s) (inputs i) = Zmod.unsigned (N.v52193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52193 s i)) at 1.
  unfold R.v52193, N.v52193.
  rewrite ?node_52188.
  rewrite ?node_52192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52194 (s : N.State) (i : N.Inputs) :
  R.v52194 (state s) (inputs i) = Zmod.unsigned (N.v52194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52194 s i)) at 1.
  unfold R.v52194, N.v52194.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52195 (s : N.State) (i : N.Inputs) :
  R.v52195 (state s) (inputs i) = Zmod.unsigned (N.v52195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52195 s i)) at 1.
  unfold R.v52195, N.v52195.
  rewrite ?node_12211.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52196 (s : N.State) (i : N.Inputs) :
  R.v52196 (state s) (inputs i) = Zmod.unsigned (N.v52196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52196 s i)) at 1.
  unfold R.v52196, N.v52196.
  unfold R.v6, N.v6.
  rewrite ?node_12191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52197 (s : N.State) (i : N.Inputs) :
  R.v52197 (state s) (inputs i) = Zmod.unsigned (N.v52197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52197 s i)) at 1.
  unfold R.v52197, N.v52197.
  unfold R.v6, N.v6.
  rewrite ?node_12160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52198 (s : N.State) (i : N.Inputs) :
  R.v52198 (state s) (inputs i) = Zmod.unsigned (N.v52198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52198 s i)) at 1.
  unfold R.v52198, N.v52198.
  rewrite ?node_52196.
  rewrite ?node_52197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52199 (s : N.State) (i : N.Inputs) :
  R.v52199 (state s) (inputs i) = Zmod.unsigned (N.v52199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52199 s i)) at 1.
  unfold R.v52199, N.v52199.
  unfold R.v16484, N.v16484.
  rewrite ?node_52198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52200 (s : N.State) (i : N.Inputs) :
  R.v52200 (state s) (inputs i) = Zmod.unsigned (N.v52200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52200 s i)) at 1.
  unfold R.v52200, N.v52200.
  rewrite ?node_52195.
  rewrite ?node_52199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52201 (s : N.State) (i : N.Inputs) :
  R.v52201 (state s) (inputs i) = Zmod.unsigned (N.v52201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52201 s i)) at 1.
  unfold R.v52201, N.v52201.
  unfold R.v6, N.v6.
  rewrite ?node_52200.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52202 (s : N.State) (i : N.Inputs) :
  R.v52202 (state s) (inputs i) = Zmod.unsigned (N.v52202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52202 s i)) at 1.
  unfold R.v52202, N.v52202.
  rewrite ?node_12212.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52203 (s : N.State) (i : N.Inputs) :
  R.v52203 (state s) (inputs i) = Zmod.unsigned (N.v52203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52203 s i)) at 1.
  unfold R.v52203, N.v52203.
  unfold R.v6, N.v6.
  rewrite ?node_12363.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52204 (s : N.State) (i : N.Inputs) :
  R.v52204 (state s) (inputs i) = Zmod.unsigned (N.v52204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52204 s i)) at 1.
  unfold R.v52204, N.v52204.
  rewrite ?node_52202.
  rewrite ?node_52203.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52205 (s : N.State) (i : N.Inputs) :
  R.v52205 (state s) (inputs i) = Zmod.unsigned (N.v52205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52205 s i)) at 1.
  unfold R.v52205, N.v52205.
  rewrite ?node_52201.
  rewrite ?node_52204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52206 (s : N.State) (i : N.Inputs) :
  R.v52206 (state s) (inputs i) = Zmod.unsigned (N.v52206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52206 s i)) at 1.
  unfold R.v52206, N.v52206.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52207 (s : N.State) (i : N.Inputs) :
  R.v52207 (state s) (inputs i) = Zmod.unsigned (N.v52207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52207 s i)) at 1.
  unfold R.v52207, N.v52207.
  rewrite ?node_12223.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52208 (s : N.State) (i : N.Inputs) :
  R.v52208 (state s) (inputs i) = Zmod.unsigned (N.v52208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52208 s i)) at 1.
  unfold R.v52208, N.v52208.
  unfold R.v6, N.v6.
  rewrite ?node_12219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52209 (s : N.State) (i : N.Inputs) :
  R.v52209 (state s) (inputs i) = Zmod.unsigned (N.v52209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52209 s i)) at 1.
  unfold R.v52209, N.v52209.
  unfold R.v6, N.v6.
  rewrite ?node_12212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52210 (s : N.State) (i : N.Inputs) :
  R.v52210 (state s) (inputs i) = Zmod.unsigned (N.v52210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52210 s i)) at 1.
  unfold R.v52210, N.v52210.
  rewrite ?node_52208.
  rewrite ?node_52209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52211 (s : N.State) (i : N.Inputs) :
  R.v52211 (state s) (inputs i) = Zmod.unsigned (N.v52211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52211 s i)) at 1.
  unfold R.v52211, N.v52211.
  unfold R.v16484, N.v16484.
  rewrite ?node_52210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52212 (s : N.State) (i : N.Inputs) :
  R.v52212 (state s) (inputs i) = Zmod.unsigned (N.v52212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52212 s i)) at 1.
  unfold R.v52212, N.v52212.
  rewrite ?node_52207.
  rewrite ?node_52211.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52213 (s : N.State) (i : N.Inputs) :
  R.v52213 (state s) (inputs i) = Zmod.unsigned (N.v52213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52213 s i)) at 1.
  unfold R.v52213, N.v52213.
  unfold R.v6, N.v6.
  rewrite ?node_52212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52214 (s : N.State) (i : N.Inputs) :
  R.v52214 (state s) (inputs i) = Zmod.unsigned (N.v52214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52214 s i)) at 1.
  unfold R.v52214, N.v52214.
  rewrite ?node_12224.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52215 (s : N.State) (i : N.Inputs) :
  R.v52215 (state s) (inputs i) = Zmod.unsigned (N.v52215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52215 s i)) at 1.
  unfold R.v52215, N.v52215.
  unfold R.v6, N.v6.
  rewrite ?node_12385.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52216 (s : N.State) (i : N.Inputs) :
  R.v52216 (state s) (inputs i) = Zmod.unsigned (N.v52216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52216 s i)) at 1.
  unfold R.v52216, N.v52216.
  rewrite ?node_52214.
  rewrite ?node_52215.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52217 (s : N.State) (i : N.Inputs) :
  R.v52217 (state s) (inputs i) = Zmod.unsigned (N.v52217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52217 s i)) at 1.
  unfold R.v52217, N.v52217.
  rewrite ?node_52213.
  rewrite ?node_52216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52218 (s : N.State) (i : N.Inputs) :
  R.v52218 (state s) (inputs i) = Zmod.unsigned (N.v52218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52218 s i)) at 1.
  unfold R.v52218, N.v52218.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52219 (s : N.State) (i : N.Inputs) :
  R.v52219 (state s) (inputs i) = Zmod.unsigned (N.v52219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52219 s i)) at 1.
  unfold R.v52219, N.v52219.
  rewrite ?node_12242.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52220 (s : N.State) (i : N.Inputs) :
  R.v52220 (state s) (inputs i) = Zmod.unsigned (N.v52220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52220 s i)) at 1.
  unfold R.v52220, N.v52220.
  rewrite ?node_12238.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52221 (s : N.State) (i : N.Inputs) :
  R.v52221 (state s) (inputs i) = Zmod.unsigned (N.v52221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52221 s i)) at 1.
  unfold R.v52221, N.v52221.
  rewrite ?node_12234.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52222 (s : N.State) (i : N.Inputs) :
  R.v52222 (state s) (inputs i) = Zmod.unsigned (N.v52222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52222 s i)) at 1.
  unfold R.v52222, N.v52222.
  unfold R.v6, N.v6.
  rewrite ?node_12230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52223 (s : N.State) (i : N.Inputs) :
  R.v52223 (state s) (inputs i) = Zmod.unsigned (N.v52223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52223 s i)) at 1.
  unfold R.v52223, N.v52223.
  unfold R.v6, N.v6.
  rewrite ?node_12227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52224 (s : N.State) (i : N.Inputs) :
  R.v52224 (state s) (inputs i) = Zmod.unsigned (N.v52224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52224 s i)) at 1.
  unfold R.v52224, N.v52224.
  rewrite ?node_52222.
  rewrite ?node_52223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52225 (s : N.State) (i : N.Inputs) :
  R.v52225 (state s) (inputs i) = Zmod.unsigned (N.v52225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52225 s i)) at 1.
  unfold R.v52225, N.v52225.
  unfold R.v16484, N.v16484.
  rewrite ?node_52224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52226 (s : N.State) (i : N.Inputs) :
  R.v52226 (state s) (inputs i) = Zmod.unsigned (N.v52226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52226 s i)) at 1.
  unfold R.v52226, N.v52226.
  rewrite ?node_52219.
  rewrite ?node_52220.
  rewrite ?node_52221.
  rewrite ?node_52225.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52227 (s : N.State) (i : N.Inputs) :
  R.v52227 (state s) (inputs i) = Zmod.unsigned (N.v52227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52227 s i)) at 1.
  unfold R.v52227, N.v52227.
  unfold R.v6, N.v6.
  rewrite ?node_52226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52228 (s : N.State) (i : N.Inputs) :
  R.v52228 (state s) (inputs i) = Zmod.unsigned (N.v52228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52228 s i)) at 1.
  unfold R.v52228, N.v52228.
  rewrite ?node_12243.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52229 (s : N.State) (i : N.Inputs) :
  R.v52229 (state s) (inputs i) = Zmod.unsigned (N.v52229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52229 s i)) at 1.
  unfold R.v52229, N.v52229.
  unfold R.v6, N.v6.
  rewrite ?node_12380.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52230 (s : N.State) (i : N.Inputs) :
  R.v52230 (state s) (inputs i) = Zmod.unsigned (N.v52230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52230 s i)) at 1.
  unfold R.v52230, N.v52230.
  unfold R.v6, N.v6.
  rewrite ?node_12389.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52231 (s : N.State) (i : N.Inputs) :
  R.v52231 (state s) (inputs i) = Zmod.unsigned (N.v52231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52231 s i)) at 1.
  unfold R.v52231, N.v52231.
  rewrite ?node_52228.
  rewrite ?node_52229.
  rewrite ?node_52230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52232 (s : N.State) (i : N.Inputs) :
  R.v52232 (state s) (inputs i) = Zmod.unsigned (N.v52232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52232 s i)) at 1.
  unfold R.v52232, N.v52232.
  rewrite ?node_52227.
  rewrite ?node_52231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52233 (s : N.State) (i : N.Inputs) :
  R.v52233 (state s) (inputs i) = Zmod.unsigned (N.v52233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52233 s i)) at 1.
  unfold R.v52233, N.v52233.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52234 (s : N.State) (i : N.Inputs) :
  R.v52234 (state s) (inputs i) = Zmod.unsigned (N.v52234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52234 s i)) at 1.
  unfold R.v52234, N.v52234.
  rewrite ?node_12234.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52235 (s : N.State) (i : N.Inputs) :
  R.v52235 (state s) (inputs i) = Zmod.unsigned (N.v52235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52235 s i)) at 1.
  unfold R.v52235, N.v52235.
  unfold R.v6, N.v6.
  rewrite ?node_12230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52236 (s : N.State) (i : N.Inputs) :
  R.v52236 (state s) (inputs i) = Zmod.unsigned (N.v52236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52236 s i)) at 1.
  unfold R.v52236, N.v52236.
  unfold R.v6, N.v6.
  rewrite ?node_12227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52237 (s : N.State) (i : N.Inputs) :
  R.v52237 (state s) (inputs i) = Zmod.unsigned (N.v52237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52237 s i)) at 1.
  unfold R.v52237, N.v52237.
  rewrite ?node_52235.
  rewrite ?node_52236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52238 (s : N.State) (i : N.Inputs) :
  R.v52238 (state s) (inputs i) = Zmod.unsigned (N.v52238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52238 s i)) at 1.
  unfold R.v52238, N.v52238.
  unfold R.v16484, N.v16484.
  rewrite ?node_52237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52239 (s : N.State) (i : N.Inputs) :
  R.v52239 (state s) (inputs i) = Zmod.unsigned (N.v52239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52239 s i)) at 1.
  unfold R.v52239, N.v52239.
  rewrite ?node_52234.
  rewrite ?node_52238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52240 (s : N.State) (i : N.Inputs) :
  R.v52240 (state s) (inputs i) = Zmod.unsigned (N.v52240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52240 s i)) at 1.
  unfold R.v52240, N.v52240.
  unfold R.v6, N.v6.
  rewrite ?node_52239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52241 (s : N.State) (i : N.Inputs) :
  R.v52241 (state s) (inputs i) = Zmod.unsigned (N.v52241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52241 s i)) at 1.
  unfold R.v52241, N.v52241.
  rewrite ?node_12235.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52242 (s : N.State) (i : N.Inputs) :
  R.v52242 (state s) (inputs i) = Zmod.unsigned (N.v52242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52242 s i)) at 1.
  unfold R.v52242, N.v52242.
  unfold R.v6, N.v6.
  rewrite ?node_12380.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52243 (s : N.State) (i : N.Inputs) :
  R.v52243 (state s) (inputs i) = Zmod.unsigned (N.v52243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52243 s i)) at 1.
  unfold R.v52243, N.v52243.
  rewrite ?node_52241.
  rewrite ?node_52242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52244 (s : N.State) (i : N.Inputs) :
  R.v52244 (state s) (inputs i) = Zmod.unsigned (N.v52244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52244 s i)) at 1.
  unfold R.v52244, N.v52244.
  rewrite ?node_52240.
  rewrite ?node_52243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52245 (s : N.State) (i : N.Inputs) :
  R.v52245 (state s) (inputs i) = Zmod.unsigned (N.v52245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52245 s i)) at 1.
  unfold R.v52245, N.v52245.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52246 (s : N.State) (i : N.Inputs) :
  R.v52246 (state s) (inputs i) = Zmod.unsigned (N.v52246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52246 s i)) at 1.
  unfold R.v52246, N.v52246.
  rewrite ?node_12242.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52247 (s : N.State) (i : N.Inputs) :
  R.v52247 (state s) (inputs i) = Zmod.unsigned (N.v52247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52247 s i)) at 1.
  unfold R.v52247, N.v52247.
  unfold R.v6, N.v6.
  rewrite ?node_12238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52248 (s : N.State) (i : N.Inputs) :
  R.v52248 (state s) (inputs i) = Zmod.unsigned (N.v52248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52248 s i)) at 1.
  unfold R.v52248, N.v52248.
  unfold R.v6, N.v6.
  rewrite ?node_12235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52249 (s : N.State) (i : N.Inputs) :
  R.v52249 (state s) (inputs i) = Zmod.unsigned (N.v52249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52249 s i)) at 1.
  unfold R.v52249, N.v52249.
  rewrite ?node_52247.
  rewrite ?node_52248.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52250 (s : N.State) (i : N.Inputs) :
  R.v52250 (state s) (inputs i) = Zmod.unsigned (N.v52250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52250 s i)) at 1.
  unfold R.v52250, N.v52250.
  unfold R.v16484, N.v16484.
  rewrite ?node_52249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52251 (s : N.State) (i : N.Inputs) :
  R.v52251 (state s) (inputs i) = Zmod.unsigned (N.v52251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52251 s i)) at 1.
  unfold R.v52251, N.v52251.
  rewrite ?node_52246.
  rewrite ?node_52250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52252 (s : N.State) (i : N.Inputs) :
  R.v52252 (state s) (inputs i) = Zmod.unsigned (N.v52252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52252 s i)) at 1.
  unfold R.v52252, N.v52252.
  unfold R.v6, N.v6.
  rewrite ?node_52251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52253 (s : N.State) (i : N.Inputs) :
  R.v52253 (state s) (inputs i) = Zmod.unsigned (N.v52253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52253 s i)) at 1.
  unfold R.v52253, N.v52253.
  rewrite ?node_12243.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52254 (s : N.State) (i : N.Inputs) :
  R.v52254 (state s) (inputs i) = Zmod.unsigned (N.v52254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52254 s i)) at 1.
  unfold R.v52254, N.v52254.
  unfold R.v6, N.v6.
  rewrite ?node_12389.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52255 (s : N.State) (i : N.Inputs) :
  R.v52255 (state s) (inputs i) = Zmod.unsigned (N.v52255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52255 s i)) at 1.
  unfold R.v52255, N.v52255.
  rewrite ?node_52253.
  rewrite ?node_52254.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52256 (s : N.State) (i : N.Inputs) :
  R.v52256 (state s) (inputs i) = Zmod.unsigned (N.v52256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52256 s i)) at 1.
  unfold R.v52256, N.v52256.
  rewrite ?node_52252.
  rewrite ?node_52255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52257 (s : N.State) (i : N.Inputs) :
  R.v52257 (state s) (inputs i) = Zmod.unsigned (N.v52257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52257 s i)) at 1.
  unfold R.v52257, N.v52257.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52258 (s : N.State) (i : N.Inputs) :
  R.v52258 (state s) (inputs i) = Zmod.unsigned (N.v52258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52258 s i)) at 1.
  unfold R.v52258, N.v52258.
  rewrite ?node_12363.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52259 (s : N.State) (i : N.Inputs) :
  R.v52259 (state s) (inputs i) = Zmod.unsigned (N.v52259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52259 s i)) at 1.
  unfold R.v52259, N.v52259.
  rewrite ?node_12359.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52260 (s : N.State) (i : N.Inputs) :
  R.v52260 (state s) (inputs i) = Zmod.unsigned (N.v52260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52260 s i)) at 1.
  unfold R.v52260, N.v52260.
  rewrite ?node_12351.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52261 (s : N.State) (i : N.Inputs) :
  R.v52261 (state s) (inputs i) = Zmod.unsigned (N.v52261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52261 s i)) at 1.
  unfold R.v52261, N.v52261.
  unfold R.v6, N.v6.
  rewrite ?node_12331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52262 (s : N.State) (i : N.Inputs) :
  R.v52262 (state s) (inputs i) = Zmod.unsigned (N.v52262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52262 s i)) at 1.
  unfold R.v52262, N.v52262.
  unfold R.v6, N.v6.
  rewrite ?node_12300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52263 (s : N.State) (i : N.Inputs) :
  R.v52263 (state s) (inputs i) = Zmod.unsigned (N.v52263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52263 s i)) at 1.
  unfold R.v52263, N.v52263.
  rewrite ?node_52261.
  rewrite ?node_52262.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52264 (s : N.State) (i : N.Inputs) :
  R.v52264 (state s) (inputs i) = Zmod.unsigned (N.v52264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52264 s i)) at 1.
  unfold R.v52264, N.v52264.
  unfold R.v16484, N.v16484.
  rewrite ?node_52263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52265 (s : N.State) (i : N.Inputs) :
  R.v52265 (state s) (inputs i) = Zmod.unsigned (N.v52265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52265 s i)) at 1.
  unfold R.v52265, N.v52265.
  rewrite ?node_52258.
  rewrite ?node_52259.
  rewrite ?node_52260.
  rewrite ?node_52264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52266 (s : N.State) (i : N.Inputs) :
  R.v52266 (state s) (inputs i) = Zmod.unsigned (N.v52266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52266 s i)) at 1.
  unfold R.v52266, N.v52266.
  unfold R.v6, N.v6.
  rewrite ?node_52265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52267 (s : N.State) (i : N.Inputs) :
  R.v52267 (state s) (inputs i) = Zmod.unsigned (N.v52267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52267 s i)) at 1.
  unfold R.v52267, N.v52267.
  rewrite ?node_12364.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52268 (s : N.State) (i : N.Inputs) :
  R.v52268 (state s) (inputs i) = Zmod.unsigned (N.v52268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52268 s i)) at 1.
  unfold R.v52268, N.v52268.
  unfold R.v6, N.v6.
  rewrite ?node_12497.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52269 (s : N.State) (i : N.Inputs) :
  R.v52269 (state s) (inputs i) = Zmod.unsigned (N.v52269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52269 s i)) at 1.
  unfold R.v52269, N.v52269.
  unfold R.v6, N.v6.
  rewrite ?node_12519.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52270 (s : N.State) (i : N.Inputs) :
  R.v52270 (state s) (inputs i) = Zmod.unsigned (N.v52270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52270 s i)) at 1.
  unfold R.v52270, N.v52270.
  rewrite ?node_52267.
  rewrite ?node_52268.
  rewrite ?node_52269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52271 (s : N.State) (i : N.Inputs) :
  R.v52271 (state s) (inputs i) = Zmod.unsigned (N.v52271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52271 s i)) at 1.
  unfold R.v52271, N.v52271.
  rewrite ?node_52266.
  rewrite ?node_52270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52272 (s : N.State) (i : N.Inputs) :
  R.v52272 (state s) (inputs i) = Zmod.unsigned (N.v52272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52272 s i)) at 1.
  unfold R.v52272, N.v52272.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52273 (s : N.State) (i : N.Inputs) :
  R.v52273 (state s) (inputs i) = Zmod.unsigned (N.v52273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52273 s i)) at 1.
  unfold R.v52273, N.v52273.
  rewrite ?node_12351.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52274 (s : N.State) (i : N.Inputs) :
  R.v52274 (state s) (inputs i) = Zmod.unsigned (N.v52274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52274 s i)) at 1.
  unfold R.v52274, N.v52274.
  unfold R.v6, N.v6.
  rewrite ?node_12331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52275 (s : N.State) (i : N.Inputs) :
  R.v52275 (state s) (inputs i) = Zmod.unsigned (N.v52275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52275 s i)) at 1.
  unfold R.v52275, N.v52275.
  unfold R.v6, N.v6.
  rewrite ?node_12300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52276 (s : N.State) (i : N.Inputs) :
  R.v52276 (state s) (inputs i) = Zmod.unsigned (N.v52276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52276 s i)) at 1.
  unfold R.v52276, N.v52276.
  rewrite ?node_52274.
  rewrite ?node_52275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52277 (s : N.State) (i : N.Inputs) :
  R.v52277 (state s) (inputs i) = Zmod.unsigned (N.v52277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52277 s i)) at 1.
  unfold R.v52277, N.v52277.
  unfold R.v16484, N.v16484.
  rewrite ?node_52276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52278 (s : N.State) (i : N.Inputs) :
  R.v52278 (state s) (inputs i) = Zmod.unsigned (N.v52278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52278 s i)) at 1.
  unfold R.v52278, N.v52278.
  rewrite ?node_52273.
  rewrite ?node_52277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52279 (s : N.State) (i : N.Inputs) :
  R.v52279 (state s) (inputs i) = Zmod.unsigned (N.v52279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52279 s i)) at 1.
  unfold R.v52279, N.v52279.
  unfold R.v6, N.v6.
  rewrite ?node_52278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52280 (s : N.State) (i : N.Inputs) :
  R.v52280 (state s) (inputs i) = Zmod.unsigned (N.v52280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52280 s i)) at 1.
  unfold R.v52280, N.v52280.
  rewrite ?node_12352.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52281 (s : N.State) (i : N.Inputs) :
  R.v52281 (state s) (inputs i) = Zmod.unsigned (N.v52281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52281 s i)) at 1.
  unfold R.v52281, N.v52281.
  unfold R.v6, N.v6.
  rewrite ?node_12497.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52282 (s : N.State) (i : N.Inputs) :
  R.v52282 (state s) (inputs i) = Zmod.unsigned (N.v52282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52282 s i)) at 1.
  unfold R.v52282, N.v52282.
  rewrite ?node_52280.
  rewrite ?node_52281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52283 (s : N.State) (i : N.Inputs) :
  R.v52283 (state s) (inputs i) = Zmod.unsigned (N.v52283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52283 s i)) at 1.
  unfold R.v52283, N.v52283.
  rewrite ?node_52279.
  rewrite ?node_52282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52284 (s : N.State) (i : N.Inputs) :
  R.v52284 (state s) (inputs i) = Zmod.unsigned (N.v52284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52284 s i)) at 1.
  unfold R.v52284, N.v52284.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52285 (s : N.State) (i : N.Inputs) :
  R.v52285 (state s) (inputs i) = Zmod.unsigned (N.v52285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52285 s i)) at 1.
  unfold R.v52285, N.v52285.
  rewrite ?node_12363.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52286 (s : N.State) (i : N.Inputs) :
  R.v52286 (state s) (inputs i) = Zmod.unsigned (N.v52286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52286 s i)) at 1.
  unfold R.v52286, N.v52286.
  unfold R.v6, N.v6.
  rewrite ?node_12359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52287 (s : N.State) (i : N.Inputs) :
  R.v52287 (state s) (inputs i) = Zmod.unsigned (N.v52287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52287 s i)) at 1.
  unfold R.v52287, N.v52287.
  unfold R.v6, N.v6.
  rewrite ?node_12352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52288 (s : N.State) (i : N.Inputs) :
  R.v52288 (state s) (inputs i) = Zmod.unsigned (N.v52288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52288 s i)) at 1.
  unfold R.v52288, N.v52288.
  rewrite ?node_52286.
  rewrite ?node_52287.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52289 (s : N.State) (i : N.Inputs) :
  R.v52289 (state s) (inputs i) = Zmod.unsigned (N.v52289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52289 s i)) at 1.
  unfold R.v52289, N.v52289.
  unfold R.v16484, N.v16484.
  rewrite ?node_52288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52290 (s : N.State) (i : N.Inputs) :
  R.v52290 (state s) (inputs i) = Zmod.unsigned (N.v52290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52290 s i)) at 1.
  unfold R.v52290, N.v52290.
  rewrite ?node_52285.
  rewrite ?node_52289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52291 (s : N.State) (i : N.Inputs) :
  R.v52291 (state s) (inputs i) = Zmod.unsigned (N.v52291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52291 s i)) at 1.
  unfold R.v52291, N.v52291.
  unfold R.v6, N.v6.
  rewrite ?node_52290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52292 (s : N.State) (i : N.Inputs) :
  R.v52292 (state s) (inputs i) = Zmod.unsigned (N.v52292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52292 s i)) at 1.
  unfold R.v52292, N.v52292.
  rewrite ?node_12364.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52293 (s : N.State) (i : N.Inputs) :
  R.v52293 (state s) (inputs i) = Zmod.unsigned (N.v52293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52293 s i)) at 1.
  unfold R.v52293, N.v52293.
  unfold R.v6, N.v6.
  rewrite ?node_12519.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52294 (s : N.State) (i : N.Inputs) :
  R.v52294 (state s) (inputs i) = Zmod.unsigned (N.v52294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52294 s i)) at 1.
  unfold R.v52294, N.v52294.
  rewrite ?node_52292.
  rewrite ?node_52293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52295 (s : N.State) (i : N.Inputs) :
  R.v52295 (state s) (inputs i) = Zmod.unsigned (N.v52295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52295 s i)) at 1.
  unfold R.v52295, N.v52295.
  rewrite ?node_52291.
  rewrite ?node_52294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52296 (s : N.State) (i : N.Inputs) :
  R.v52296 (state s) (inputs i) = Zmod.unsigned (N.v52296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52296 s i)) at 1.
  unfold R.v52296, N.v52296.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52297 (s : N.State) (i : N.Inputs) :
  R.v52297 (state s) (inputs i) = Zmod.unsigned (N.v52297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52297 s i)) at 1.
  unfold R.v52297, N.v52297.
  rewrite ?node_12380.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52298 (s : N.State) (i : N.Inputs) :
  R.v52298 (state s) (inputs i) = Zmod.unsigned (N.v52298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52298 s i)) at 1.
  unfold R.v52298, N.v52298.
  rewrite ?node_12376.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52299 (s : N.State) (i : N.Inputs) :
  R.v52299 (state s) (inputs i) = Zmod.unsigned (N.v52299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52299 s i)) at 1.
  unfold R.v52299, N.v52299.
  rewrite ?node_12374.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52300 (s : N.State) (i : N.Inputs) :
  R.v52300 (state s) (inputs i) = Zmod.unsigned (N.v52300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52300 s i)) at 1.
  unfold R.v52300, N.v52300.
  unfold R.v6, N.v6.
  rewrite ?node_12370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52301 (s : N.State) (i : N.Inputs) :
  R.v52301 (state s) (inputs i) = Zmod.unsigned (N.v52301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52301 s i)) at 1.
  unfold R.v52301, N.v52301.
  unfold R.v6, N.v6.
  rewrite ?node_12367.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52302 (s : N.State) (i : N.Inputs) :
  R.v52302 (state s) (inputs i) = Zmod.unsigned (N.v52302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52302 s i)) at 1.
  unfold R.v52302, N.v52302.
  rewrite ?node_52300.
  rewrite ?node_52301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52303 (s : N.State) (i : N.Inputs) :
  R.v52303 (state s) (inputs i) = Zmod.unsigned (N.v52303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52303 s i)) at 1.
  unfold R.v52303, N.v52303.
  unfold R.v16484, N.v16484.
  rewrite ?node_52302.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52304 (s : N.State) (i : N.Inputs) :
  R.v52304 (state s) (inputs i) = Zmod.unsigned (N.v52304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52304 s i)) at 1.
  unfold R.v52304, N.v52304.
  rewrite ?node_52297.
  rewrite ?node_52298.
  rewrite ?node_52299.
  rewrite ?node_52303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52305 (s : N.State) (i : N.Inputs) :
  R.v52305 (state s) (inputs i) = Zmod.unsigned (N.v52305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52305 s i)) at 1.
  unfold R.v52305, N.v52305.
  unfold R.v6, N.v6.
  rewrite ?node_52304.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52306 (s : N.State) (i : N.Inputs) :
  R.v52306 (state s) (inputs i) = Zmod.unsigned (N.v52306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52306 s i)) at 1.
  unfold R.v52306, N.v52306.
  rewrite ?node_12381.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52307 (s : N.State) (i : N.Inputs) :
  R.v52307 (state s) (inputs i) = Zmod.unsigned (N.v52307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52307 s i)) at 1.
  unfold R.v52307, N.v52307.
  unfold R.v6, N.v6.
  rewrite ?node_12514.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52308 (s : N.State) (i : N.Inputs) :
  R.v52308 (state s) (inputs i) = Zmod.unsigned (N.v52308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52308 s i)) at 1.
  unfold R.v52308, N.v52308.
  unfold R.v6, N.v6.
  rewrite ?node_12523.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52309 (s : N.State) (i : N.Inputs) :
  R.v52309 (state s) (inputs i) = Zmod.unsigned (N.v52309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52309 s i)) at 1.
  unfold R.v52309, N.v52309.
  rewrite ?node_52306.
  rewrite ?node_52307.
  rewrite ?node_52308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52310 (s : N.State) (i : N.Inputs) :
  R.v52310 (state s) (inputs i) = Zmod.unsigned (N.v52310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52310 s i)) at 1.
  unfold R.v52310, N.v52310.
  rewrite ?node_52305.
  rewrite ?node_52309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52311 (s : N.State) (i : N.Inputs) :
  R.v52311 (state s) (inputs i) = Zmod.unsigned (N.v52311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52311 s i)) at 1.
  unfold R.v52311, N.v52311.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52312 (s : N.State) (i : N.Inputs) :
  R.v52312 (state s) (inputs i) = Zmod.unsigned (N.v52312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52312 s i)) at 1.
  unfold R.v52312, N.v52312.
  rewrite ?node_12374.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52313 (s : N.State) (i : N.Inputs) :
  R.v52313 (state s) (inputs i) = Zmod.unsigned (N.v52313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52313 s i)) at 1.
  unfold R.v52313, N.v52313.
  unfold R.v6, N.v6.
  rewrite ?node_12370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52314 (s : N.State) (i : N.Inputs) :
  R.v52314 (state s) (inputs i) = Zmod.unsigned (N.v52314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52314 s i)) at 1.
  unfold R.v52314, N.v52314.
  unfold R.v6, N.v6.
  rewrite ?node_12367.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52315 (s : N.State) (i : N.Inputs) :
  R.v52315 (state s) (inputs i) = Zmod.unsigned (N.v52315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52315 s i)) at 1.
  unfold R.v52315, N.v52315.
  rewrite ?node_52313.
  rewrite ?node_52314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52316 (s : N.State) (i : N.Inputs) :
  R.v52316 (state s) (inputs i) = Zmod.unsigned (N.v52316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52316 s i)) at 1.
  unfold R.v52316, N.v52316.
  unfold R.v16484, N.v16484.
  rewrite ?node_52315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52317 (s : N.State) (i : N.Inputs) :
  R.v52317 (state s) (inputs i) = Zmod.unsigned (N.v52317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52317 s i)) at 1.
  unfold R.v52317, N.v52317.
  rewrite ?node_52312.
  rewrite ?node_52316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52318 (s : N.State) (i : N.Inputs) :
  R.v52318 (state s) (inputs i) = Zmod.unsigned (N.v52318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52318 s i)) at 1.
  unfold R.v52318, N.v52318.
  unfold R.v6, N.v6.
  rewrite ?node_52317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52319 (s : N.State) (i : N.Inputs) :
  R.v52319 (state s) (inputs i) = Zmod.unsigned (N.v52319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52319 s i)) at 1.
  unfold R.v52319, N.v52319.
  rewrite ?node_12375.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52320 (s : N.State) (i : N.Inputs) :
  R.v52320 (state s) (inputs i) = Zmod.unsigned (N.v52320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52320 s i)) at 1.
  unfold R.v52320, N.v52320.
  unfold R.v6, N.v6.
  rewrite ?node_12514.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52321 (s : N.State) (i : N.Inputs) :
  R.v52321 (state s) (inputs i) = Zmod.unsigned (N.v52321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52321 s i)) at 1.
  unfold R.v52321, N.v52321.
  rewrite ?node_52319.
  rewrite ?node_52320.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52322 (s : N.State) (i : N.Inputs) :
  R.v52322 (state s) (inputs i) = Zmod.unsigned (N.v52322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52322 s i)) at 1.
  unfold R.v52322, N.v52322.
  rewrite ?node_52318.
  rewrite ?node_52321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52323 (s : N.State) (i : N.Inputs) :
  R.v52323 (state s) (inputs i) = Zmod.unsigned (N.v52323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52323 s i)) at 1.
  unfold R.v52323, N.v52323.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52324 (s : N.State) (i : N.Inputs) :
  R.v52324 (state s) (inputs i) = Zmod.unsigned (N.v52324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52324 s i)) at 1.
  unfold R.v52324, N.v52324.
  rewrite ?node_12380.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52325 (s : N.State) (i : N.Inputs) :
  R.v52325 (state s) (inputs i) = Zmod.unsigned (N.v52325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52325 s i)) at 1.
  unfold R.v52325, N.v52325.
  unfold R.v6, N.v6.
  rewrite ?node_12376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52326 (s : N.State) (i : N.Inputs) :
  R.v52326 (state s) (inputs i) = Zmod.unsigned (N.v52326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52326 s i)) at 1.
  unfold R.v52326, N.v52326.
  unfold R.v6, N.v6.
  rewrite ?node_12375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52327 (s : N.State) (i : N.Inputs) :
  R.v52327 (state s) (inputs i) = Zmod.unsigned (N.v52327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52327 s i)) at 1.
  unfold R.v52327, N.v52327.
  rewrite ?node_52325.
  rewrite ?node_52326.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52328 (s : N.State) (i : N.Inputs) :
  R.v52328 (state s) (inputs i) = Zmod.unsigned (N.v52328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52328 s i)) at 1.
  unfold R.v52328, N.v52328.
  unfold R.v16484, N.v16484.
  rewrite ?node_52327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52329 (s : N.State) (i : N.Inputs) :
  R.v52329 (state s) (inputs i) = Zmod.unsigned (N.v52329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52329 s i)) at 1.
  unfold R.v52329, N.v52329.
  rewrite ?node_52324.
  rewrite ?node_52328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52330 (s : N.State) (i : N.Inputs) :
  R.v52330 (state s) (inputs i) = Zmod.unsigned (N.v52330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52330 s i)) at 1.
  unfold R.v52330, N.v52330.
  unfold R.v6, N.v6.
  rewrite ?node_52329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52331 (s : N.State) (i : N.Inputs) :
  R.v52331 (state s) (inputs i) = Zmod.unsigned (N.v52331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52331 s i)) at 1.
  unfold R.v52331, N.v52331.
  rewrite ?node_12381.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52332 (s : N.State) (i : N.Inputs) :
  R.v52332 (state s) (inputs i) = Zmod.unsigned (N.v52332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52332 s i)) at 1.
  unfold R.v52332, N.v52332.
  unfold R.v6, N.v6.
  rewrite ?node_12523.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52333 (s : N.State) (i : N.Inputs) :
  R.v52333 (state s) (inputs i) = Zmod.unsigned (N.v52333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52333 s i)) at 1.
  unfold R.v52333, N.v52333.
  rewrite ?node_52331.
  rewrite ?node_52332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52334 (s : N.State) (i : N.Inputs) :
  R.v52334 (state s) (inputs i) = Zmod.unsigned (N.v52334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52334 s i)) at 1.
  unfold R.v52334, N.v52334.
  rewrite ?node_52330.
  rewrite ?node_52333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52335 (s : N.State) (i : N.Inputs) :
  R.v52335 (state s) (inputs i) = Zmod.unsigned (N.v52335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52335 s i)) at 1.
  unfold R.v52335, N.v52335.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52336 (s : N.State) (i : N.Inputs) :
  R.v52336 (state s) (inputs i) = Zmod.unsigned (N.v52336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52336 s i)) at 1.
  unfold R.v52336, N.v52336.
  rewrite ?node_12497.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52337 (s : N.State) (i : N.Inputs) :
  R.v52337 (state s) (inputs i) = Zmod.unsigned (N.v52337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52337 s i)) at 1.
  unfold R.v52337, N.v52337.
  rewrite ?node_12493.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52338 (s : N.State) (i : N.Inputs) :
  R.v52338 (state s) (inputs i) = Zmod.unsigned (N.v52338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52338 s i)) at 1.
  unfold R.v52338, N.v52338.
  rewrite ?node_12481.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52339 (s : N.State) (i : N.Inputs) :
  R.v52339 (state s) (inputs i) = Zmod.unsigned (N.v52339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52339 s i)) at 1.
  unfold R.v52339, N.v52339.
  unfold R.v6, N.v6.
  rewrite ?node_12461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52340 (s : N.State) (i : N.Inputs) :
  R.v52340 (state s) (inputs i) = Zmod.unsigned (N.v52340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52340 s i)) at 1.
  unfold R.v52340, N.v52340.
  unfold R.v6, N.v6.
  rewrite ?node_12435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52341 (s : N.State) (i : N.Inputs) :
  R.v52341 (state s) (inputs i) = Zmod.unsigned (N.v52341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52341 s i)) at 1.
  unfold R.v52341, N.v52341.
  rewrite ?node_52339.
  rewrite ?node_52340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52342 (s : N.State) (i : N.Inputs) :
  R.v52342 (state s) (inputs i) = Zmod.unsigned (N.v52342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52342 s i)) at 1.
  unfold R.v52342, N.v52342.
  unfold R.v16484, N.v16484.
  rewrite ?node_52341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52343 (s : N.State) (i : N.Inputs) :
  R.v52343 (state s) (inputs i) = Zmod.unsigned (N.v52343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52343 s i)) at 1.
  unfold R.v52343, N.v52343.
  rewrite ?node_52336.
  rewrite ?node_52337.
  rewrite ?node_52338.
  rewrite ?node_52342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52344 (s : N.State) (i : N.Inputs) :
  R.v52344 (state s) (inputs i) = Zmod.unsigned (N.v52344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52344 s i)) at 1.
  unfold R.v52344, N.v52344.
  unfold R.v6, N.v6.
  rewrite ?node_52343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52345 (s : N.State) (i : N.Inputs) :
  R.v52345 (state s) (inputs i) = Zmod.unsigned (N.v52345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52345 s i)) at 1.
  unfold R.v52345, N.v52345.
  rewrite ?node_12498.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52346 (s : N.State) (i : N.Inputs) :
  R.v52346 (state s) (inputs i) = Zmod.unsigned (N.v52346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52346 s i)) at 1.
  unfold R.v52346, N.v52346.
  unfold R.v6, N.v6.
  rewrite ?node_12628.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52347 (s : N.State) (i : N.Inputs) :
  R.v52347 (state s) (inputs i) = Zmod.unsigned (N.v52347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52347 s i)) at 1.
  unfold R.v52347, N.v52347.
  unfold R.v6, N.v6.
  rewrite ?node_12652.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52348 (s : N.State) (i : N.Inputs) :
  R.v52348 (state s) (inputs i) = Zmod.unsigned (N.v52348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52348 s i)) at 1.
  unfold R.v52348, N.v52348.
  rewrite ?node_52345.
  rewrite ?node_52346.
  rewrite ?node_52347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52349 (s : N.State) (i : N.Inputs) :
  R.v52349 (state s) (inputs i) = Zmod.unsigned (N.v52349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52349 s i)) at 1.
  unfold R.v52349, N.v52349.
  rewrite ?node_52344.
  rewrite ?node_52348.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52350 (s : N.State) (i : N.Inputs) :
  R.v52350 (state s) (inputs i) = Zmod.unsigned (N.v52350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52350 s i)) at 1.
  unfold R.v52350, N.v52350.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52351 (s : N.State) (i : N.Inputs) :
  R.v52351 (state s) (inputs i) = Zmod.unsigned (N.v52351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52351 s i)) at 1.
  unfold R.v52351, N.v52351.
  rewrite ?node_12481.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52352 (s : N.State) (i : N.Inputs) :
  R.v52352 (state s) (inputs i) = Zmod.unsigned (N.v52352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52352 s i)) at 1.
  unfold R.v52352, N.v52352.
  unfold R.v6, N.v6.
  rewrite ?node_12461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52353 (s : N.State) (i : N.Inputs) :
  R.v52353 (state s) (inputs i) = Zmod.unsigned (N.v52353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52353 s i)) at 1.
  unfold R.v52353, N.v52353.
  unfold R.v6, N.v6.
  rewrite ?node_12435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52354 (s : N.State) (i : N.Inputs) :
  R.v52354 (state s) (inputs i) = Zmod.unsigned (N.v52354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52354 s i)) at 1.
  unfold R.v52354, N.v52354.
  rewrite ?node_52352.
  rewrite ?node_52353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52355 (s : N.State) (i : N.Inputs) :
  R.v52355 (state s) (inputs i) = Zmod.unsigned (N.v52355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52355 s i)) at 1.
  unfold R.v52355, N.v52355.
  unfold R.v16484, N.v16484.
  rewrite ?node_52354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52356 (s : N.State) (i : N.Inputs) :
  R.v52356 (state s) (inputs i) = Zmod.unsigned (N.v52356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52356 s i)) at 1.
  unfold R.v52356, N.v52356.
  rewrite ?node_52351.
  rewrite ?node_52355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52357 (s : N.State) (i : N.Inputs) :
  R.v52357 (state s) (inputs i) = Zmod.unsigned (N.v52357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52357 s i)) at 1.
  unfold R.v52357, N.v52357.
  unfold R.v6, N.v6.
  rewrite ?node_52356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52358 (s : N.State) (i : N.Inputs) :
  R.v52358 (state s) (inputs i) = Zmod.unsigned (N.v52358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52358 s i)) at 1.
  unfold R.v52358, N.v52358.
  rewrite ?node_12482.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52359 (s : N.State) (i : N.Inputs) :
  R.v52359 (state s) (inputs i) = Zmod.unsigned (N.v52359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52359 s i)) at 1.
  unfold R.v52359, N.v52359.
  unfold R.v6, N.v6.
  rewrite ?node_12628.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52360 (s : N.State) (i : N.Inputs) :
  R.v52360 (state s) (inputs i) = Zmod.unsigned (N.v52360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52360 s i)) at 1.
  unfold R.v52360, N.v52360.
  rewrite ?node_52358.
  rewrite ?node_52359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52361 (s : N.State) (i : N.Inputs) :
  R.v52361 (state s) (inputs i) = Zmod.unsigned (N.v52361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52361 s i)) at 1.
  unfold R.v52361, N.v52361.
  rewrite ?node_52357.
  rewrite ?node_52360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52362 (s : N.State) (i : N.Inputs) :
  R.v52362 (state s) (inputs i) = Zmod.unsigned (N.v52362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52362 s i)) at 1.
  unfold R.v52362, N.v52362.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52363 (s : N.State) (i : N.Inputs) :
  R.v52363 (state s) (inputs i) = Zmod.unsigned (N.v52363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52363 s i)) at 1.
  unfold R.v52363, N.v52363.
  rewrite ?node_12497.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52364 (s : N.State) (i : N.Inputs) :
  R.v52364 (state s) (inputs i) = Zmod.unsigned (N.v52364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52364 s i)) at 1.
  unfold R.v52364, N.v52364.
  unfold R.v6, N.v6.
  rewrite ?node_12493.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52365 (s : N.State) (i : N.Inputs) :
  R.v52365 (state s) (inputs i) = Zmod.unsigned (N.v52365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52365 s i)) at 1.
  unfold R.v52365, N.v52365.
  unfold R.v6, N.v6.
  rewrite ?node_12482.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52366 (s : N.State) (i : N.Inputs) :
  R.v52366 (state s) (inputs i) = Zmod.unsigned (N.v52366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52366 s i)) at 1.
  unfold R.v52366, N.v52366.
  rewrite ?node_52364.
  rewrite ?node_52365.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52367 (s : N.State) (i : N.Inputs) :
  R.v52367 (state s) (inputs i) = Zmod.unsigned (N.v52367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52367 s i)) at 1.
  unfold R.v52367, N.v52367.
  unfold R.v16484, N.v16484.
  rewrite ?node_52366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52368 (s : N.State) (i : N.Inputs) :
  R.v52368 (state s) (inputs i) = Zmod.unsigned (N.v52368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52368 s i)) at 1.
  unfold R.v52368, N.v52368.
  rewrite ?node_52363.
  rewrite ?node_52367.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52369 (s : N.State) (i : N.Inputs) :
  R.v52369 (state s) (inputs i) = Zmod.unsigned (N.v52369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52369 s i)) at 1.
  unfold R.v52369, N.v52369.
  unfold R.v6, N.v6.
  rewrite ?node_52368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52370 (s : N.State) (i : N.Inputs) :
  R.v52370 (state s) (inputs i) = Zmod.unsigned (N.v52370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52370 s i)) at 1.
  unfold R.v52370, N.v52370.
  rewrite ?node_12498.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52371 (s : N.State) (i : N.Inputs) :
  R.v52371 (state s) (inputs i) = Zmod.unsigned (N.v52371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52371 s i)) at 1.
  unfold R.v52371, N.v52371.
  unfold R.v6, N.v6.
  rewrite ?node_12652.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52372 (s : N.State) (i : N.Inputs) :
  R.v52372 (state s) (inputs i) = Zmod.unsigned (N.v52372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52372 s i)) at 1.
  unfold R.v52372, N.v52372.
  rewrite ?node_52370.
  rewrite ?node_52371.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52373 (s : N.State) (i : N.Inputs) :
  R.v52373 (state s) (inputs i) = Zmod.unsigned (N.v52373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52373 s i)) at 1.
  unfold R.v52373, N.v52373.
  rewrite ?node_52369.
  rewrite ?node_52372.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52374 (s : N.State) (i : N.Inputs) :
  R.v52374 (state s) (inputs i) = Zmod.unsigned (N.v52374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52374 s i)) at 1.
  unfold R.v52374, N.v52374.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52375 (s : N.State) (i : N.Inputs) :
  R.v52375 (state s) (inputs i) = Zmod.unsigned (N.v52375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52375 s i)) at 1.
  unfold R.v52375, N.v52375.
  rewrite ?node_12514.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52376 (s : N.State) (i : N.Inputs) :
  R.v52376 (state s) (inputs i) = Zmod.unsigned (N.v52376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52376 s i)) at 1.
  unfold R.v52376, N.v52376.
  rewrite ?node_12510.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52377 (s : N.State) (i : N.Inputs) :
  R.v52377 (state s) (inputs i) = Zmod.unsigned (N.v52377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52377 s i)) at 1.
  unfold R.v52377, N.v52377.
  rewrite ?node_12508.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52378 (s : N.State) (i : N.Inputs) :
  R.v52378 (state s) (inputs i) = Zmod.unsigned (N.v52378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52378 s i)) at 1.
  unfold R.v52378, N.v52378.
  unfold R.v6, N.v6.
  rewrite ?node_12504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52379 (s : N.State) (i : N.Inputs) :
  R.v52379 (state s) (inputs i) = Zmod.unsigned (N.v52379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52379 s i)) at 1.
  unfold R.v52379, N.v52379.
  unfold R.v6, N.v6.
  rewrite ?node_12501.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52380 (s : N.State) (i : N.Inputs) :
  R.v52380 (state s) (inputs i) = Zmod.unsigned (N.v52380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52380 s i)) at 1.
  unfold R.v52380, N.v52380.
  rewrite ?node_52378.
  rewrite ?node_52379.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52381 (s : N.State) (i : N.Inputs) :
  R.v52381 (state s) (inputs i) = Zmod.unsigned (N.v52381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52381 s i)) at 1.
  unfold R.v52381, N.v52381.
  unfold R.v16484, N.v16484.
  rewrite ?node_52380.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52382 (s : N.State) (i : N.Inputs) :
  R.v52382 (state s) (inputs i) = Zmod.unsigned (N.v52382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52382 s i)) at 1.
  unfold R.v52382, N.v52382.
  rewrite ?node_52375.
  rewrite ?node_52376.
  rewrite ?node_52377.
  rewrite ?node_52381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52383 (s : N.State) (i : N.Inputs) :
  R.v52383 (state s) (inputs i) = Zmod.unsigned (N.v52383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52383 s i)) at 1.
  unfold R.v52383, N.v52383.
  unfold R.v6, N.v6.
  rewrite ?node_52382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52384 (s : N.State) (i : N.Inputs) :
  R.v52384 (state s) (inputs i) = Zmod.unsigned (N.v52384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52384 s i)) at 1.
  unfold R.v52384, N.v52384.
  rewrite ?node_12515.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52385 (s : N.State) (i : N.Inputs) :
  R.v52385 (state s) (inputs i) = Zmod.unsigned (N.v52385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52385 s i)) at 1.
  unfold R.v52385, N.v52385.
  unfold R.v6, N.v6.
  rewrite ?node_12647.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52386 (s : N.State) (i : N.Inputs) :
  R.v52386 (state s) (inputs i) = Zmod.unsigned (N.v52386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52386 s i)) at 1.
  unfold R.v52386, N.v52386.
  unfold R.v6, N.v6.
  rewrite ?node_12656.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52387 (s : N.State) (i : N.Inputs) :
  R.v52387 (state s) (inputs i) = Zmod.unsigned (N.v52387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52387 s i)) at 1.
  unfold R.v52387, N.v52387.
  rewrite ?node_52384.
  rewrite ?node_52385.
  rewrite ?node_52386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52388 (s : N.State) (i : N.Inputs) :
  R.v52388 (state s) (inputs i) = Zmod.unsigned (N.v52388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52388 s i)) at 1.
  unfold R.v52388, N.v52388.
  rewrite ?node_52383.
  rewrite ?node_52387.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52389 (s : N.State) (i : N.Inputs) :
  R.v52389 (state s) (inputs i) = Zmod.unsigned (N.v52389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52389 s i)) at 1.
  unfold R.v52389, N.v52389.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52390 (s : N.State) (i : N.Inputs) :
  R.v52390 (state s) (inputs i) = Zmod.unsigned (N.v52390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52390 s i)) at 1.
  unfold R.v52390, N.v52390.
  rewrite ?node_12508.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52391 (s : N.State) (i : N.Inputs) :
  R.v52391 (state s) (inputs i) = Zmod.unsigned (N.v52391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52391 s i)) at 1.
  unfold R.v52391, N.v52391.
  unfold R.v6, N.v6.
  rewrite ?node_12504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52392 (s : N.State) (i : N.Inputs) :
  R.v52392 (state s) (inputs i) = Zmod.unsigned (N.v52392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52392 s i)) at 1.
  unfold R.v52392, N.v52392.
  unfold R.v6, N.v6.
  rewrite ?node_12501.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52393 (s : N.State) (i : N.Inputs) :
  R.v52393 (state s) (inputs i) = Zmod.unsigned (N.v52393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52393 s i)) at 1.
  unfold R.v52393, N.v52393.
  rewrite ?node_52391.
  rewrite ?node_52392.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52394 (s : N.State) (i : N.Inputs) :
  R.v52394 (state s) (inputs i) = Zmod.unsigned (N.v52394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52394 s i)) at 1.
  unfold R.v52394, N.v52394.
  unfold R.v16484, N.v16484.
  rewrite ?node_52393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52395 (s : N.State) (i : N.Inputs) :
  R.v52395 (state s) (inputs i) = Zmod.unsigned (N.v52395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52395 s i)) at 1.
  unfold R.v52395, N.v52395.
  rewrite ?node_52390.
  rewrite ?node_52394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52396 (s : N.State) (i : N.Inputs) :
  R.v52396 (state s) (inputs i) = Zmod.unsigned (N.v52396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52396 s i)) at 1.
  unfold R.v52396, N.v52396.
  unfold R.v6, N.v6.
  rewrite ?node_52395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52397 (s : N.State) (i : N.Inputs) :
  R.v52397 (state s) (inputs i) = Zmod.unsigned (N.v52397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52397 s i)) at 1.
  unfold R.v52397, N.v52397.
  rewrite ?node_12509.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52398 (s : N.State) (i : N.Inputs) :
  R.v52398 (state s) (inputs i) = Zmod.unsigned (N.v52398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52398 s i)) at 1.
  unfold R.v52398, N.v52398.
  unfold R.v6, N.v6.
  rewrite ?node_12647.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52399 (s : N.State) (i : N.Inputs) :
  R.v52399 (state s) (inputs i) = Zmod.unsigned (N.v52399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52399 s i)) at 1.
  unfold R.v52399, N.v52399.
  rewrite ?node_52397.
  rewrite ?node_52398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52400 (s : N.State) (i : N.Inputs) :
  R.v52400 (state s) (inputs i) = Zmod.unsigned (N.v52400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52400 s i)) at 1.
  unfold R.v52400, N.v52400.
  rewrite ?node_52396.
  rewrite ?node_52399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52401 (s : N.State) (i : N.Inputs) :
  R.v52401 (state s) (inputs i) = Zmod.unsigned (N.v52401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52401 s i)) at 1.
  unfold R.v52401, N.v52401.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52402 (s : N.State) (i : N.Inputs) :
  R.v52402 (state s) (inputs i) = Zmod.unsigned (N.v52402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52402 s i)) at 1.
  unfold R.v52402, N.v52402.
  rewrite ?node_12514.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52403 (s : N.State) (i : N.Inputs) :
  R.v52403 (state s) (inputs i) = Zmod.unsigned (N.v52403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52403 s i)) at 1.
  unfold R.v52403, N.v52403.
  unfold R.v6, N.v6.
  rewrite ?node_12510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52404 (s : N.State) (i : N.Inputs) :
  R.v52404 (state s) (inputs i) = Zmod.unsigned (N.v52404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52404 s i)) at 1.
  unfold R.v52404, N.v52404.
  unfold R.v6, N.v6.
  rewrite ?node_12509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52405 (s : N.State) (i : N.Inputs) :
  R.v52405 (state s) (inputs i) = Zmod.unsigned (N.v52405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52405 s i)) at 1.
  unfold R.v52405, N.v52405.
  rewrite ?node_52403.
  rewrite ?node_52404.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52406 (s : N.State) (i : N.Inputs) :
  R.v52406 (state s) (inputs i) = Zmod.unsigned (N.v52406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52406 s i)) at 1.
  unfold R.v52406, N.v52406.
  unfold R.v16484, N.v16484.
  rewrite ?node_52405.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52407 (s : N.State) (i : N.Inputs) :
  R.v52407 (state s) (inputs i) = Zmod.unsigned (N.v52407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52407 s i)) at 1.
  unfold R.v52407, N.v52407.
  rewrite ?node_52402.
  rewrite ?node_52406.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52408 (s : N.State) (i : N.Inputs) :
  R.v52408 (state s) (inputs i) = Zmod.unsigned (N.v52408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52408 s i)) at 1.
  unfold R.v52408, N.v52408.
  unfold R.v6, N.v6.
  rewrite ?node_52407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52409 (s : N.State) (i : N.Inputs) :
  R.v52409 (state s) (inputs i) = Zmod.unsigned (N.v52409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52409 s i)) at 1.
  unfold R.v52409, N.v52409.
  rewrite ?node_12515.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52410 (s : N.State) (i : N.Inputs) :
  R.v52410 (state s) (inputs i) = Zmod.unsigned (N.v52410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52410 s i)) at 1.
  unfold R.v52410, N.v52410.
  unfold R.v6, N.v6.
  rewrite ?node_12656.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52411 (s : N.State) (i : N.Inputs) :
  R.v52411 (state s) (inputs i) = Zmod.unsigned (N.v52411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52411 s i)) at 1.
  unfold R.v52411, N.v52411.
  rewrite ?node_52409.
  rewrite ?node_52410.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52412 (s : N.State) (i : N.Inputs) :
  R.v52412 (state s) (inputs i) = Zmod.unsigned (N.v52412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52412 s i)) at 1.
  unfold R.v52412, N.v52412.
  rewrite ?node_52408.
  rewrite ?node_52411.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52413 (s : N.State) (i : N.Inputs) :
  R.v52413 (state s) (inputs i) = Zmod.unsigned (N.v52413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52413 s i)) at 1.
  unfold R.v52413, N.v52413.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52414 (s : N.State) (i : N.Inputs) :
  R.v52414 (state s) (inputs i) = Zmod.unsigned (N.v52414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52414 s i)) at 1.
  unfold R.v52414, N.v52414.
  rewrite ?node_12628.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52415 (s : N.State) (i : N.Inputs) :
  R.v52415 (state s) (inputs i) = Zmod.unsigned (N.v52415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52415 s i)) at 1.
  unfold R.v52415, N.v52415.
  rewrite ?node_12624.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52416 (s : N.State) (i : N.Inputs) :
  R.v52416 (state s) (inputs i) = Zmod.unsigned (N.v52416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52416 s i)) at 1.
  unfold R.v52416, N.v52416.
  rewrite ?node_12616.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52417 (s : N.State) (i : N.Inputs) :
  R.v52417 (state s) (inputs i) = Zmod.unsigned (N.v52417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52417 s i)) at 1.
  unfold R.v52417, N.v52417.
  unfold R.v6, N.v6.
  rewrite ?node_12596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52418 (s : N.State) (i : N.Inputs) :
  R.v52418 (state s) (inputs i) = Zmod.unsigned (N.v52418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52418 s i)) at 1.
  unfold R.v52418, N.v52418.
  unfold R.v6, N.v6.
  rewrite ?node_12570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52419 (s : N.State) (i : N.Inputs) :
  R.v52419 (state s) (inputs i) = Zmod.unsigned (N.v52419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52419 s i)) at 1.
  unfold R.v52419, N.v52419.
  rewrite ?node_52417.
  rewrite ?node_52418.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52420 (s : N.State) (i : N.Inputs) :
  R.v52420 (state s) (inputs i) = Zmod.unsigned (N.v52420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52420 s i)) at 1.
  unfold R.v52420, N.v52420.
  unfold R.v16484, N.v16484.
  rewrite ?node_52419.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52421 (s : N.State) (i : N.Inputs) :
  R.v52421 (state s) (inputs i) = Zmod.unsigned (N.v52421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52421 s i)) at 1.
  unfold R.v52421, N.v52421.
  rewrite ?node_52414.
  rewrite ?node_52415.
  rewrite ?node_52416.
  rewrite ?node_52420.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52422 (s : N.State) (i : N.Inputs) :
  R.v52422 (state s) (inputs i) = Zmod.unsigned (N.v52422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52422 s i)) at 1.
  unfold R.v52422, N.v52422.
  unfold R.v6, N.v6.
  rewrite ?node_52421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52423 (s : N.State) (i : N.Inputs) :
  R.v52423 (state s) (inputs i) = Zmod.unsigned (N.v52423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52423 s i)) at 1.
  unfold R.v52423, N.v52423.
  rewrite ?node_12629.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52424 (s : N.State) (i : N.Inputs) :
  R.v52424 (state s) (inputs i) = Zmod.unsigned (N.v52424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52424 s i)) at 1.
  unfold R.v52424, N.v52424.
  unfold R.v6, N.v6.
  rewrite ?node_12759.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52425 (s : N.State) (i : N.Inputs) :
  R.v52425 (state s) (inputs i) = Zmod.unsigned (N.v52425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52425 s i)) at 1.
  unfold R.v52425, N.v52425.
  unfold R.v6, N.v6.
  rewrite ?node_12781.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52426 (s : N.State) (i : N.Inputs) :
  R.v52426 (state s) (inputs i) = Zmod.unsigned (N.v52426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52426 s i)) at 1.
  unfold R.v52426, N.v52426.
  rewrite ?node_52423.
  rewrite ?node_52424.
  rewrite ?node_52425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52427 (s : N.State) (i : N.Inputs) :
  R.v52427 (state s) (inputs i) = Zmod.unsigned (N.v52427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52427 s i)) at 1.
  unfold R.v52427, N.v52427.
  rewrite ?node_52422.
  rewrite ?node_52426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52428 (s : N.State) (i : N.Inputs) :
  R.v52428 (state s) (inputs i) = Zmod.unsigned (N.v52428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52428 s i)) at 1.
  unfold R.v52428, N.v52428.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52429 (s : N.State) (i : N.Inputs) :
  R.v52429 (state s) (inputs i) = Zmod.unsigned (N.v52429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52429 s i)) at 1.
  unfold R.v52429, N.v52429.
  rewrite ?node_12616.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52430 (s : N.State) (i : N.Inputs) :
  R.v52430 (state s) (inputs i) = Zmod.unsigned (N.v52430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52430 s i)) at 1.
  unfold R.v52430, N.v52430.
  unfold R.v6, N.v6.
  rewrite ?node_12596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52431 (s : N.State) (i : N.Inputs) :
  R.v52431 (state s) (inputs i) = Zmod.unsigned (N.v52431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52431 s i)) at 1.
  unfold R.v52431, N.v52431.
  unfold R.v6, N.v6.
  rewrite ?node_12570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52432 (s : N.State) (i : N.Inputs) :
  R.v52432 (state s) (inputs i) = Zmod.unsigned (N.v52432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52432 s i)) at 1.
  unfold R.v52432, N.v52432.
  rewrite ?node_52430.
  rewrite ?node_52431.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52433 (s : N.State) (i : N.Inputs) :
  R.v52433 (state s) (inputs i) = Zmod.unsigned (N.v52433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52433 s i)) at 1.
  unfold R.v52433, N.v52433.
  unfold R.v16484, N.v16484.
  rewrite ?node_52432.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52434 (s : N.State) (i : N.Inputs) :
  R.v52434 (state s) (inputs i) = Zmod.unsigned (N.v52434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52434 s i)) at 1.
  unfold R.v52434, N.v52434.
  rewrite ?node_52429.
  rewrite ?node_52433.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52435 (s : N.State) (i : N.Inputs) :
  R.v52435 (state s) (inputs i) = Zmod.unsigned (N.v52435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52435 s i)) at 1.
  unfold R.v52435, N.v52435.
  unfold R.v6, N.v6.
  rewrite ?node_52434.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52436 (s : N.State) (i : N.Inputs) :
  R.v52436 (state s) (inputs i) = Zmod.unsigned (N.v52436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52436 s i)) at 1.
  unfold R.v52436, N.v52436.
  rewrite ?node_12617.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52437 (s : N.State) (i : N.Inputs) :
  R.v52437 (state s) (inputs i) = Zmod.unsigned (N.v52437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52437 s i)) at 1.
  unfold R.v52437, N.v52437.
  unfold R.v6, N.v6.
  rewrite ?node_12759.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52438 (s : N.State) (i : N.Inputs) :
  R.v52438 (state s) (inputs i) = Zmod.unsigned (N.v52438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52438 s i)) at 1.
  unfold R.v52438, N.v52438.
  rewrite ?node_52436.
  rewrite ?node_52437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52439 (s : N.State) (i : N.Inputs) :
  R.v52439 (state s) (inputs i) = Zmod.unsigned (N.v52439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52439 s i)) at 1.
  unfold R.v52439, N.v52439.
  rewrite ?node_52435.
  rewrite ?node_52438.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52440 (s : N.State) (i : N.Inputs) :
  R.v52440 (state s) (inputs i) = Zmod.unsigned (N.v52440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52440 s i)) at 1.
  unfold R.v52440, N.v52440.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52441 (s : N.State) (i : N.Inputs) :
  R.v52441 (state s) (inputs i) = Zmod.unsigned (N.v52441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52441 s i)) at 1.
  unfold R.v52441, N.v52441.
  rewrite ?node_12628.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52442 (s : N.State) (i : N.Inputs) :
  R.v52442 (state s) (inputs i) = Zmod.unsigned (N.v52442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52442 s i)) at 1.
  unfold R.v52442, N.v52442.
  unfold R.v6, N.v6.
  rewrite ?node_12624.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52443 (s : N.State) (i : N.Inputs) :
  R.v52443 (state s) (inputs i) = Zmod.unsigned (N.v52443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52443 s i)) at 1.
  unfold R.v52443, N.v52443.
  unfold R.v6, N.v6.
  rewrite ?node_12617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52444 (s : N.State) (i : N.Inputs) :
  R.v52444 (state s) (inputs i) = Zmod.unsigned (N.v52444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52444 s i)) at 1.
  unfold R.v52444, N.v52444.
  rewrite ?node_52442.
  rewrite ?node_52443.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52445 (s : N.State) (i : N.Inputs) :
  R.v52445 (state s) (inputs i) = Zmod.unsigned (N.v52445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52445 s i)) at 1.
  unfold R.v52445, N.v52445.
  unfold R.v16484, N.v16484.
  rewrite ?node_52444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52446 (s : N.State) (i : N.Inputs) :
  R.v52446 (state s) (inputs i) = Zmod.unsigned (N.v52446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52446 s i)) at 1.
  unfold R.v52446, N.v52446.
  rewrite ?node_52441.
  rewrite ?node_52445.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52447 (s : N.State) (i : N.Inputs) :
  R.v52447 (state s) (inputs i) = Zmod.unsigned (N.v52447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52447 s i)) at 1.
  unfold R.v52447, N.v52447.
  unfold R.v6, N.v6.
  rewrite ?node_52446.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52448 (s : N.State) (i : N.Inputs) :
  R.v52448 (state s) (inputs i) = Zmod.unsigned (N.v52448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52448 s i)) at 1.
  unfold R.v52448, N.v52448.
  rewrite ?node_12629.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52449 (s : N.State) (i : N.Inputs) :
  R.v52449 (state s) (inputs i) = Zmod.unsigned (N.v52449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52449 s i)) at 1.
  unfold R.v52449, N.v52449.
  unfold R.v6, N.v6.
  rewrite ?node_12781.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52450 (s : N.State) (i : N.Inputs) :
  R.v52450 (state s) (inputs i) = Zmod.unsigned (N.v52450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52450 s i)) at 1.
  unfold R.v52450, N.v52450.
  rewrite ?node_52448.
  rewrite ?node_52449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52451 (s : N.State) (i : N.Inputs) :
  R.v52451 (state s) (inputs i) = Zmod.unsigned (N.v52451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52451 s i)) at 1.
  unfold R.v52451, N.v52451.
  rewrite ?node_52447.
  rewrite ?node_52450.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52452 (s : N.State) (i : N.Inputs) :
  R.v52452 (state s) (inputs i) = Zmod.unsigned (N.v52452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52452 s i)) at 1.
  unfold R.v52452, N.v52452.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52453 (s : N.State) (i : N.Inputs) :
  R.v52453 (state s) (inputs i) = Zmod.unsigned (N.v52453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52453 s i)) at 1.
  unfold R.v52453, N.v52453.
  rewrite ?node_12647.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52454 (s : N.State) (i : N.Inputs) :
  R.v52454 (state s) (inputs i) = Zmod.unsigned (N.v52454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52454 s i)) at 1.
  unfold R.v52454, N.v52454.
  rewrite ?node_12643.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52455 (s : N.State) (i : N.Inputs) :
  R.v52455 (state s) (inputs i) = Zmod.unsigned (N.v52455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52455 s i)) at 1.
  unfold R.v52455, N.v52455.
  rewrite ?node_12639.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52456 (s : N.State) (i : N.Inputs) :
  R.v52456 (state s) (inputs i) = Zmod.unsigned (N.v52456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52456 s i)) at 1.
  unfold R.v52456, N.v52456.
  unfold R.v6, N.v6.
  rewrite ?node_12635.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52457 (s : N.State) (i : N.Inputs) :
  R.v52457 (state s) (inputs i) = Zmod.unsigned (N.v52457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52457 s i)) at 1.
  unfold R.v52457, N.v52457.
  unfold R.v6, N.v6.
  rewrite ?node_12632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52458 (s : N.State) (i : N.Inputs) :
  R.v52458 (state s) (inputs i) = Zmod.unsigned (N.v52458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52458 s i)) at 1.
  unfold R.v52458, N.v52458.
  rewrite ?node_52456.
  rewrite ?node_52457.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52459 (s : N.State) (i : N.Inputs) :
  R.v52459 (state s) (inputs i) = Zmod.unsigned (N.v52459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52459 s i)) at 1.
  unfold R.v52459, N.v52459.
  unfold R.v16484, N.v16484.
  rewrite ?node_52458.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52460 (s : N.State) (i : N.Inputs) :
  R.v52460 (state s) (inputs i) = Zmod.unsigned (N.v52460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52460 s i)) at 1.
  unfold R.v52460, N.v52460.
  rewrite ?node_52453.
  rewrite ?node_52454.
  rewrite ?node_52455.
  rewrite ?node_52459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52461 (s : N.State) (i : N.Inputs) :
  R.v52461 (state s) (inputs i) = Zmod.unsigned (N.v52461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52461 s i)) at 1.
  unfold R.v52461, N.v52461.
  unfold R.v6, N.v6.
  rewrite ?node_52460.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52462 (s : N.State) (i : N.Inputs) :
  R.v52462 (state s) (inputs i) = Zmod.unsigned (N.v52462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52462 s i)) at 1.
  unfold R.v52462, N.v52462.
  rewrite ?node_12648.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52463 (s : N.State) (i : N.Inputs) :
  R.v52463 (state s) (inputs i) = Zmod.unsigned (N.v52463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52463 s i)) at 1.
  unfold R.v52463, N.v52463.
  unfold R.v6, N.v6.
  rewrite ?node_12776.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52464 (s : N.State) (i : N.Inputs) :
  R.v52464 (state s) (inputs i) = Zmod.unsigned (N.v52464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52464 s i)) at 1.
  unfold R.v52464, N.v52464.
  unfold R.v6, N.v6.
  rewrite ?node_12785.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52465 (s : N.State) (i : N.Inputs) :
  R.v52465 (state s) (inputs i) = Zmod.unsigned (N.v52465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52465 s i)) at 1.
  unfold R.v52465, N.v52465.
  rewrite ?node_52462.
  rewrite ?node_52463.
  rewrite ?node_52464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52466 (s : N.State) (i : N.Inputs) :
  R.v52466 (state s) (inputs i) = Zmod.unsigned (N.v52466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52466 s i)) at 1.
  unfold R.v52466, N.v52466.
  rewrite ?node_52461.
  rewrite ?node_52465.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52467 (s : N.State) (i : N.Inputs) :
  R.v52467 (state s) (inputs i) = Zmod.unsigned (N.v52467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52467 s i)) at 1.
  unfold R.v52467, N.v52467.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52468 (s : N.State) (i : N.Inputs) :
  R.v52468 (state s) (inputs i) = Zmod.unsigned (N.v52468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52468 s i)) at 1.
  unfold R.v52468, N.v52468.
  rewrite ?node_12639.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52469 (s : N.State) (i : N.Inputs) :
  R.v52469 (state s) (inputs i) = Zmod.unsigned (N.v52469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52469 s i)) at 1.
  unfold R.v52469, N.v52469.
  unfold R.v6, N.v6.
  rewrite ?node_12635.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52470 (s : N.State) (i : N.Inputs) :
  R.v52470 (state s) (inputs i) = Zmod.unsigned (N.v52470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52470 s i)) at 1.
  unfold R.v52470, N.v52470.
  unfold R.v6, N.v6.
  rewrite ?node_12632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52471 (s : N.State) (i : N.Inputs) :
  R.v52471 (state s) (inputs i) = Zmod.unsigned (N.v52471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52471 s i)) at 1.
  unfold R.v52471, N.v52471.
  rewrite ?node_52469.
  rewrite ?node_52470.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52472 (s : N.State) (i : N.Inputs) :
  R.v52472 (state s) (inputs i) = Zmod.unsigned (N.v52472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52472 s i)) at 1.
  unfold R.v52472, N.v52472.
  unfold R.v16484, N.v16484.
  rewrite ?node_52471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52473 (s : N.State) (i : N.Inputs) :
  R.v52473 (state s) (inputs i) = Zmod.unsigned (N.v52473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52473 s i)) at 1.
  unfold R.v52473, N.v52473.
  rewrite ?node_52468.
  rewrite ?node_52472.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52474 (s : N.State) (i : N.Inputs) :
  R.v52474 (state s) (inputs i) = Zmod.unsigned (N.v52474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52474 s i)) at 1.
  unfold R.v52474, N.v52474.
  unfold R.v6, N.v6.
  rewrite ?node_52473.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52475 (s : N.State) (i : N.Inputs) :
  R.v52475 (state s) (inputs i) = Zmod.unsigned (N.v52475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52475 s i)) at 1.
  unfold R.v52475, N.v52475.
  rewrite ?node_12640.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52476 (s : N.State) (i : N.Inputs) :
  R.v52476 (state s) (inputs i) = Zmod.unsigned (N.v52476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52476 s i)) at 1.
  unfold R.v52476, N.v52476.
  unfold R.v6, N.v6.
  rewrite ?node_12776.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52477 (s : N.State) (i : N.Inputs) :
  R.v52477 (state s) (inputs i) = Zmod.unsigned (N.v52477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52477 s i)) at 1.
  unfold R.v52477, N.v52477.
  rewrite ?node_52475.
  rewrite ?node_52476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52478 (s : N.State) (i : N.Inputs) :
  R.v52478 (state s) (inputs i) = Zmod.unsigned (N.v52478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52478 s i)) at 1.
  unfold R.v52478, N.v52478.
  rewrite ?node_52474.
  rewrite ?node_52477.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52479 (s : N.State) (i : N.Inputs) :
  R.v52479 (state s) (inputs i) = Zmod.unsigned (N.v52479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52479 s i)) at 1.
  unfold R.v52479, N.v52479.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52480 (s : N.State) (i : N.Inputs) :
  R.v52480 (state s) (inputs i) = Zmod.unsigned (N.v52480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52480 s i)) at 1.
  unfold R.v52480, N.v52480.
  rewrite ?node_12647.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52481 (s : N.State) (i : N.Inputs) :
  R.v52481 (state s) (inputs i) = Zmod.unsigned (N.v52481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52481 s i)) at 1.
  unfold R.v52481, N.v52481.
  unfold R.v6, N.v6.
  rewrite ?node_12643.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52482 (s : N.State) (i : N.Inputs) :
  R.v52482 (state s) (inputs i) = Zmod.unsigned (N.v52482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52482 s i)) at 1.
  unfold R.v52482, N.v52482.
  unfold R.v6, N.v6.
  rewrite ?node_12640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52483 (s : N.State) (i : N.Inputs) :
  R.v52483 (state s) (inputs i) = Zmod.unsigned (N.v52483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52483 s i)) at 1.
  unfold R.v52483, N.v52483.
  rewrite ?node_52481.
  rewrite ?node_52482.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52484 (s : N.State) (i : N.Inputs) :
  R.v52484 (state s) (inputs i) = Zmod.unsigned (N.v52484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52484 s i)) at 1.
  unfold R.v52484, N.v52484.
  unfold R.v16484, N.v16484.
  rewrite ?node_52483.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52485 (s : N.State) (i : N.Inputs) :
  R.v52485 (state s) (inputs i) = Zmod.unsigned (N.v52485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52485 s i)) at 1.
  unfold R.v52485, N.v52485.
  rewrite ?node_52480.
  rewrite ?node_52484.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52486 (s : N.State) (i : N.Inputs) :
  R.v52486 (state s) (inputs i) = Zmod.unsigned (N.v52486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52486 s i)) at 1.
  unfold R.v52486, N.v52486.
  unfold R.v6, N.v6.
  rewrite ?node_52485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52487 (s : N.State) (i : N.Inputs) :
  R.v52487 (state s) (inputs i) = Zmod.unsigned (N.v52487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52487 s i)) at 1.
  unfold R.v52487, N.v52487.
  rewrite ?node_12648.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52488 (s : N.State) (i : N.Inputs) :
  R.v52488 (state s) (inputs i) = Zmod.unsigned (N.v52488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52488 s i)) at 1.
  unfold R.v52488, N.v52488.
  unfold R.v6, N.v6.
  rewrite ?node_12785.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52489 (s : N.State) (i : N.Inputs) :
  R.v52489 (state s) (inputs i) = Zmod.unsigned (N.v52489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52489 s i)) at 1.
  unfold R.v52489, N.v52489.
  rewrite ?node_52487.
  rewrite ?node_52488.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52490 (s : N.State) (i : N.Inputs) :
  R.v52490 (state s) (inputs i) = Zmod.unsigned (N.v52490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52490 s i)) at 1.
  unfold R.v52490, N.v52490.
  rewrite ?node_52486.
  rewrite ?node_52489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52491 (s : N.State) (i : N.Inputs) :
  R.v52491 (state s) (inputs i) = Zmod.unsigned (N.v52491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52491 s i)) at 1.
  unfold R.v52491, N.v52491.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52492 (s : N.State) (i : N.Inputs) :
  R.v52492 (state s) (inputs i) = Zmod.unsigned (N.v52492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52492 s i)) at 1.
  unfold R.v52492, N.v52492.
  rewrite ?node_12759.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52493 (s : N.State) (i : N.Inputs) :
  R.v52493 (state s) (inputs i) = Zmod.unsigned (N.v52493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52493 s i)) at 1.
  unfold R.v52493, N.v52493.
  rewrite ?node_12755.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52494 (s : N.State) (i : N.Inputs) :
  R.v52494 (state s) (inputs i) = Zmod.unsigned (N.v52494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52494 s i)) at 1.
  unfold R.v52494, N.v52494.
  rewrite ?node_12747.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52495 (s : N.State) (i : N.Inputs) :
  R.v52495 (state s) (inputs i) = Zmod.unsigned (N.v52495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52495 s i)) at 1.
  unfold R.v52495, N.v52495.
  unfold R.v6, N.v6.
  rewrite ?node_12727.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52496 (s : N.State) (i : N.Inputs) :
  R.v52496 (state s) (inputs i) = Zmod.unsigned (N.v52496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52496 s i)) at 1.
  unfold R.v52496, N.v52496.
  unfold R.v6, N.v6.
  rewrite ?node_12702.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52497 (s : N.State) (i : N.Inputs) :
  R.v52497 (state s) (inputs i) = Zmod.unsigned (N.v52497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52497 s i)) at 1.
  unfold R.v52497, N.v52497.
  rewrite ?node_52495.
  rewrite ?node_52496.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52498 (s : N.State) (i : N.Inputs) :
  R.v52498 (state s) (inputs i) = Zmod.unsigned (N.v52498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52498 s i)) at 1.
  unfold R.v52498, N.v52498.
  unfold R.v16484, N.v16484.
  rewrite ?node_52497.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52499 (s : N.State) (i : N.Inputs) :
  R.v52499 (state s) (inputs i) = Zmod.unsigned (N.v52499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52499 s i)) at 1.
  unfold R.v52499, N.v52499.
  rewrite ?node_52492.
  rewrite ?node_52493.
  rewrite ?node_52494.
  rewrite ?node_52498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52500 (s : N.State) (i : N.Inputs) :
  R.v52500 (state s) (inputs i) = Zmod.unsigned (N.v52500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52500 s i)) at 1.
  unfold R.v52500, N.v52500.
  unfold R.v6, N.v6.
  rewrite ?node_52499.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52501 (s : N.State) (i : N.Inputs) :
  R.v52501 (state s) (inputs i) = Zmod.unsigned (N.v52501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52501 s i)) at 1.
  unfold R.v52501, N.v52501.
  rewrite ?node_12760.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52502 (s : N.State) (i : N.Inputs) :
  R.v52502 (state s) (inputs i) = Zmod.unsigned (N.v52502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52502 s i)) at 1.
  unfold R.v52502, N.v52502.
  unfold R.v6, N.v6.
  rewrite ?node_12887.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52503 (s : N.State) (i : N.Inputs) :
  R.v52503 (state s) (inputs i) = Zmod.unsigned (N.v52503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52503 s i)) at 1.
  unfold R.v52503, N.v52503.
  unfold R.v6, N.v6.
  rewrite ?node_12909.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52504 (s : N.State) (i : N.Inputs) :
  R.v52504 (state s) (inputs i) = Zmod.unsigned (N.v52504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52504 s i)) at 1.
  unfold R.v52504, N.v52504.
  rewrite ?node_52501.
  rewrite ?node_52502.
  rewrite ?node_52503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52505 (s : N.State) (i : N.Inputs) :
  R.v52505 (state s) (inputs i) = Zmod.unsigned (N.v52505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52505 s i)) at 1.
  unfold R.v52505, N.v52505.
  rewrite ?node_52500.
  rewrite ?node_52504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52506 (s : N.State) (i : N.Inputs) :
  R.v52506 (state s) (inputs i) = Zmod.unsigned (N.v52506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52506 s i)) at 1.
  unfold R.v52506, N.v52506.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52507 (s : N.State) (i : N.Inputs) :
  R.v52507 (state s) (inputs i) = Zmod.unsigned (N.v52507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52507 s i)) at 1.
  unfold R.v52507, N.v52507.
  rewrite ?node_12747.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52508 (s : N.State) (i : N.Inputs) :
  R.v52508 (state s) (inputs i) = Zmod.unsigned (N.v52508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52508 s i)) at 1.
  unfold R.v52508, N.v52508.
  unfold R.v6, N.v6.
  rewrite ?node_12727.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52509 (s : N.State) (i : N.Inputs) :
  R.v52509 (state s) (inputs i) = Zmod.unsigned (N.v52509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52509 s i)) at 1.
  unfold R.v52509, N.v52509.
  unfold R.v6, N.v6.
  rewrite ?node_12702.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52510 (s : N.State) (i : N.Inputs) :
  R.v52510 (state s) (inputs i) = Zmod.unsigned (N.v52510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52510 s i)) at 1.
  unfold R.v52510, N.v52510.
  rewrite ?node_52508.
  rewrite ?node_52509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52511 (s : N.State) (i : N.Inputs) :
  R.v52511 (state s) (inputs i) = Zmod.unsigned (N.v52511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52511 s i)) at 1.
  unfold R.v52511, N.v52511.
  unfold R.v16484, N.v16484.
  rewrite ?node_52510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52512 (s : N.State) (i : N.Inputs) :
  R.v52512 (state s) (inputs i) = Zmod.unsigned (N.v52512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52512 s i)) at 1.
  unfold R.v52512, N.v52512.
  rewrite ?node_52507.
  rewrite ?node_52511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52513 (s : N.State) (i : N.Inputs) :
  R.v52513 (state s) (inputs i) = Zmod.unsigned (N.v52513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52513 s i)) at 1.
  unfold R.v52513, N.v52513.
  unfold R.v6, N.v6.
  rewrite ?node_52512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52514 (s : N.State) (i : N.Inputs) :
  R.v52514 (state s) (inputs i) = Zmod.unsigned (N.v52514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52514 s i)) at 1.
  unfold R.v52514, N.v52514.
  rewrite ?node_12748.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52515 (s : N.State) (i : N.Inputs) :
  R.v52515 (state s) (inputs i) = Zmod.unsigned (N.v52515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52515 s i)) at 1.
  unfold R.v52515, N.v52515.
  unfold R.v6, N.v6.
  rewrite ?node_12887.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52516 (s : N.State) (i : N.Inputs) :
  R.v52516 (state s) (inputs i) = Zmod.unsigned (N.v52516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52516 s i)) at 1.
  unfold R.v52516, N.v52516.
  rewrite ?node_52514.
  rewrite ?node_52515.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52517 (s : N.State) (i : N.Inputs) :
  R.v52517 (state s) (inputs i) = Zmod.unsigned (N.v52517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52517 s i)) at 1.
  unfold R.v52517, N.v52517.
  rewrite ?node_52513.
  rewrite ?node_52516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52518 (s : N.State) (i : N.Inputs) :
  R.v52518 (state s) (inputs i) = Zmod.unsigned (N.v52518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52518 s i)) at 1.
  unfold R.v52518, N.v52518.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52519 (s : N.State) (i : N.Inputs) :
  R.v52519 (state s) (inputs i) = Zmod.unsigned (N.v52519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52519 s i)) at 1.
  unfold R.v52519, N.v52519.
  rewrite ?node_12759.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52520 (s : N.State) (i : N.Inputs) :
  R.v52520 (state s) (inputs i) = Zmod.unsigned (N.v52520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52520 s i)) at 1.
  unfold R.v52520, N.v52520.
  unfold R.v6, N.v6.
  rewrite ?node_12755.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52521 (s : N.State) (i : N.Inputs) :
  R.v52521 (state s) (inputs i) = Zmod.unsigned (N.v52521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52521 s i)) at 1.
  unfold R.v52521, N.v52521.
  unfold R.v6, N.v6.
  rewrite ?node_12748.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52522 (s : N.State) (i : N.Inputs) :
  R.v52522 (state s) (inputs i) = Zmod.unsigned (N.v52522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52522 s i)) at 1.
  unfold R.v52522, N.v52522.
  rewrite ?node_52520.
  rewrite ?node_52521.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52523 (s : N.State) (i : N.Inputs) :
  R.v52523 (state s) (inputs i) = Zmod.unsigned (N.v52523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52523 s i)) at 1.
  unfold R.v52523, N.v52523.
  unfold R.v16484, N.v16484.
  rewrite ?node_52522.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52524 (s : N.State) (i : N.Inputs) :
  R.v52524 (state s) (inputs i) = Zmod.unsigned (N.v52524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52524 s i)) at 1.
  unfold R.v52524, N.v52524.
  rewrite ?node_52519.
  rewrite ?node_52523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52525 (s : N.State) (i : N.Inputs) :
  R.v52525 (state s) (inputs i) = Zmod.unsigned (N.v52525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52525 s i)) at 1.
  unfold R.v52525, N.v52525.
  unfold R.v6, N.v6.
  rewrite ?node_52524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52526 (s : N.State) (i : N.Inputs) :
  R.v52526 (state s) (inputs i) = Zmod.unsigned (N.v52526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52526 s i)) at 1.
  unfold R.v52526, N.v52526.
  rewrite ?node_12760.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52527 (s : N.State) (i : N.Inputs) :
  R.v52527 (state s) (inputs i) = Zmod.unsigned (N.v52527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52527 s i)) at 1.
  unfold R.v52527, N.v52527.
  unfold R.v6, N.v6.
  rewrite ?node_12909.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52528 (s : N.State) (i : N.Inputs) :
  R.v52528 (state s) (inputs i) = Zmod.unsigned (N.v52528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52528 s i)) at 1.
  unfold R.v52528, N.v52528.
  rewrite ?node_52526.
  rewrite ?node_52527.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52529 (s : N.State) (i : N.Inputs) :
  R.v52529 (state s) (inputs i) = Zmod.unsigned (N.v52529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52529 s i)) at 1.
  unfold R.v52529, N.v52529.
  rewrite ?node_52525.
  rewrite ?node_52528.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52530 (s : N.State) (i : N.Inputs) :
  R.v52530 (state s) (inputs i) = Zmod.unsigned (N.v52530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52530 s i)) at 1.
  unfold R.v52530, N.v52530.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52531 (s : N.State) (i : N.Inputs) :
  R.v52531 (state s) (inputs i) = Zmod.unsigned (N.v52531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52531 s i)) at 1.
  unfold R.v52531, N.v52531.
  rewrite ?node_12776.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52532 (s : N.State) (i : N.Inputs) :
  R.v52532 (state s) (inputs i) = Zmod.unsigned (N.v52532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52532 s i)) at 1.
  unfold R.v52532, N.v52532.
  rewrite ?node_12772.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52533 (s : N.State) (i : N.Inputs) :
  R.v52533 (state s) (inputs i) = Zmod.unsigned (N.v52533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52533 s i)) at 1.
  unfold R.v52533, N.v52533.
  rewrite ?node_12770.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52534 (s : N.State) (i : N.Inputs) :
  R.v52534 (state s) (inputs i) = Zmod.unsigned (N.v52534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52534 s i)) at 1.
  unfold R.v52534, N.v52534.
  unfold R.v6, N.v6.
  rewrite ?node_12766.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52535 (s : N.State) (i : N.Inputs) :
  R.v52535 (state s) (inputs i) = Zmod.unsigned (N.v52535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52535 s i)) at 1.
  unfold R.v52535, N.v52535.
  unfold R.v6, N.v6.
  rewrite ?node_12763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52536 (s : N.State) (i : N.Inputs) :
  R.v52536 (state s) (inputs i) = Zmod.unsigned (N.v52536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52536 s i)) at 1.
  unfold R.v52536, N.v52536.
  rewrite ?node_52534.
  rewrite ?node_52535.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52537 (s : N.State) (i : N.Inputs) :
  R.v52537 (state s) (inputs i) = Zmod.unsigned (N.v52537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52537 s i)) at 1.
  unfold R.v52537, N.v52537.
  unfold R.v16484, N.v16484.
  rewrite ?node_52536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52538 (s : N.State) (i : N.Inputs) :
  R.v52538 (state s) (inputs i) = Zmod.unsigned (N.v52538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52538 s i)) at 1.
  unfold R.v52538, N.v52538.
  rewrite ?node_52531.
  rewrite ?node_52532.
  rewrite ?node_52533.
  rewrite ?node_52537.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52539 (s : N.State) (i : N.Inputs) :
  R.v52539 (state s) (inputs i) = Zmod.unsigned (N.v52539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52539 s i)) at 1.
  unfold R.v52539, N.v52539.
  unfold R.v6, N.v6.
  rewrite ?node_52538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52540 (s : N.State) (i : N.Inputs) :
  R.v52540 (state s) (inputs i) = Zmod.unsigned (N.v52540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52540 s i)) at 1.
  unfold R.v52540, N.v52540.
  rewrite ?node_12777.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52541 (s : N.State) (i : N.Inputs) :
  R.v52541 (state s) (inputs i) = Zmod.unsigned (N.v52541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52541 s i)) at 1.
  unfold R.v52541, N.v52541.
  unfold R.v6, N.v6.
  rewrite ?node_12904.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52542 (s : N.State) (i : N.Inputs) :
  R.v52542 (state s) (inputs i) = Zmod.unsigned (N.v52542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52542 s i)) at 1.
  unfold R.v52542, N.v52542.
  unfold R.v6, N.v6.
  rewrite ?node_12913.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52543 (s : N.State) (i : N.Inputs) :
  R.v52543 (state s) (inputs i) = Zmod.unsigned (N.v52543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52543 s i)) at 1.
  unfold R.v52543, N.v52543.
  rewrite ?node_52540.
  rewrite ?node_52541.
  rewrite ?node_52542.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52544 (s : N.State) (i : N.Inputs) :
  R.v52544 (state s) (inputs i) = Zmod.unsigned (N.v52544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52544 s i)) at 1.
  unfold R.v52544, N.v52544.
  rewrite ?node_52539.
  rewrite ?node_52543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52545 (s : N.State) (i : N.Inputs) :
  R.v52545 (state s) (inputs i) = Zmod.unsigned (N.v52545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52545 s i)) at 1.
  unfold R.v52545, N.v52545.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52546 (s : N.State) (i : N.Inputs) :
  R.v52546 (state s) (inputs i) = Zmod.unsigned (N.v52546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52546 s i)) at 1.
  unfold R.v52546, N.v52546.
  rewrite ?node_12770.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52547 (s : N.State) (i : N.Inputs) :
  R.v52547 (state s) (inputs i) = Zmod.unsigned (N.v52547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52547 s i)) at 1.
  unfold R.v52547, N.v52547.
  unfold R.v6, N.v6.
  rewrite ?node_12766.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52548 (s : N.State) (i : N.Inputs) :
  R.v52548 (state s) (inputs i) = Zmod.unsigned (N.v52548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52548 s i)) at 1.
  unfold R.v52548, N.v52548.
  unfold R.v6, N.v6.
  rewrite ?node_12763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52549 (s : N.State) (i : N.Inputs) :
  R.v52549 (state s) (inputs i) = Zmod.unsigned (N.v52549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52549 s i)) at 1.
  unfold R.v52549, N.v52549.
  rewrite ?node_52547.
  rewrite ?node_52548.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52550 (s : N.State) (i : N.Inputs) :
  R.v52550 (state s) (inputs i) = Zmod.unsigned (N.v52550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52550 s i)) at 1.
  unfold R.v52550, N.v52550.
  unfold R.v16484, N.v16484.
  rewrite ?node_52549.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52551 (s : N.State) (i : N.Inputs) :
  R.v52551 (state s) (inputs i) = Zmod.unsigned (N.v52551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52551 s i)) at 1.
  unfold R.v52551, N.v52551.
  rewrite ?node_52546.
  rewrite ?node_52550.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52552 (s : N.State) (i : N.Inputs) :
  R.v52552 (state s) (inputs i) = Zmod.unsigned (N.v52552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52552 s i)) at 1.
  unfold R.v52552, N.v52552.
  unfold R.v6, N.v6.
  rewrite ?node_52551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52553 (s : N.State) (i : N.Inputs) :
  R.v52553 (state s) (inputs i) = Zmod.unsigned (N.v52553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52553 s i)) at 1.
  unfold R.v52553, N.v52553.
  rewrite ?node_12771.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52554 (s : N.State) (i : N.Inputs) :
  R.v52554 (state s) (inputs i) = Zmod.unsigned (N.v52554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52554 s i)) at 1.
  unfold R.v52554, N.v52554.
  unfold R.v6, N.v6.
  rewrite ?node_12904.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52555 (s : N.State) (i : N.Inputs) :
  R.v52555 (state s) (inputs i) = Zmod.unsigned (N.v52555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52555 s i)) at 1.
  unfold R.v52555, N.v52555.
  rewrite ?node_52553.
  rewrite ?node_52554.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52556 (s : N.State) (i : N.Inputs) :
  R.v52556 (state s) (inputs i) = Zmod.unsigned (N.v52556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52556 s i)) at 1.
  unfold R.v52556, N.v52556.
  rewrite ?node_52552.
  rewrite ?node_52555.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52557 (s : N.State) (i : N.Inputs) :
  R.v52557 (state s) (inputs i) = Zmod.unsigned (N.v52557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52557 s i)) at 1.
  unfold R.v52557, N.v52557.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52558 (s : N.State) (i : N.Inputs) :
  R.v52558 (state s) (inputs i) = Zmod.unsigned (N.v52558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52558 s i)) at 1.
  unfold R.v52558, N.v52558.
  rewrite ?node_12776.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52559 (s : N.State) (i : N.Inputs) :
  R.v52559 (state s) (inputs i) = Zmod.unsigned (N.v52559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52559 s i)) at 1.
  unfold R.v52559, N.v52559.
  unfold R.v6, N.v6.
  rewrite ?node_12772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52560 (s : N.State) (i : N.Inputs) :
  R.v52560 (state s) (inputs i) = Zmod.unsigned (N.v52560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52560 s i)) at 1.
  unfold R.v52560, N.v52560.
  unfold R.v6, N.v6.
  rewrite ?node_12771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52561 (s : N.State) (i : N.Inputs) :
  R.v52561 (state s) (inputs i) = Zmod.unsigned (N.v52561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52561 s i)) at 1.
  unfold R.v52561, N.v52561.
  rewrite ?node_52559.
  rewrite ?node_52560.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52562 (s : N.State) (i : N.Inputs) :
  R.v52562 (state s) (inputs i) = Zmod.unsigned (N.v52562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52562 s i)) at 1.
  unfold R.v52562, N.v52562.
  unfold R.v16484, N.v16484.
  rewrite ?node_52561.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52563 (s : N.State) (i : N.Inputs) :
  R.v52563 (state s) (inputs i) = Zmod.unsigned (N.v52563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52563 s i)) at 1.
  unfold R.v52563, N.v52563.
  rewrite ?node_52558.
  rewrite ?node_52562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52564 (s : N.State) (i : N.Inputs) :
  R.v52564 (state s) (inputs i) = Zmod.unsigned (N.v52564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52564 s i)) at 1.
  unfold R.v52564, N.v52564.
  unfold R.v6, N.v6.
  rewrite ?node_52563.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52565 (s : N.State) (i : N.Inputs) :
  R.v52565 (state s) (inputs i) = Zmod.unsigned (N.v52565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52565 s i)) at 1.
  unfold R.v52565, N.v52565.
  rewrite ?node_12777.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52566 (s : N.State) (i : N.Inputs) :
  R.v52566 (state s) (inputs i) = Zmod.unsigned (N.v52566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52566 s i)) at 1.
  unfold R.v52566, N.v52566.
  unfold R.v6, N.v6.
  rewrite ?node_12913.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52567 (s : N.State) (i : N.Inputs) :
  R.v52567 (state s) (inputs i) = Zmod.unsigned (N.v52567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52567 s i)) at 1.
  unfold R.v52567, N.v52567.
  rewrite ?node_52565.
  rewrite ?node_52566.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52568 (s : N.State) (i : N.Inputs) :
  R.v52568 (state s) (inputs i) = Zmod.unsigned (N.v52568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52568 s i)) at 1.
  unfold R.v52568, N.v52568.
  rewrite ?node_52564.
  rewrite ?node_52567.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52569 (s : N.State) (i : N.Inputs) :
  R.v52569 (state s) (inputs i) = Zmod.unsigned (N.v52569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52569 s i)) at 1.
  unfold R.v52569, N.v52569.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52570 (s : N.State) (i : N.Inputs) :
  R.v52570 (state s) (inputs i) = Zmod.unsigned (N.v52570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52570 s i)) at 1.
  unfold R.v52570, N.v52570.
  rewrite ?node_12887.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52571 (s : N.State) (i : N.Inputs) :
  R.v52571 (state s) (inputs i) = Zmod.unsigned (N.v52571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52571 s i)) at 1.
  unfold R.v52571, N.v52571.
  rewrite ?node_12883.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52572 (s : N.State) (i : N.Inputs) :
  R.v52572 (state s) (inputs i) = Zmod.unsigned (N.v52572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52572 s i)) at 1.
  unfold R.v52572, N.v52572.
  rewrite ?node_12877.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52573 (s : N.State) (i : N.Inputs) :
  R.v52573 (state s) (inputs i) = Zmod.unsigned (N.v52573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52573 s i)) at 1.
  unfold R.v52573, N.v52573.
  unfold R.v6, N.v6.
  rewrite ?node_12857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52574 (s : N.State) (i : N.Inputs) :
  R.v52574 (state s) (inputs i) = Zmod.unsigned (N.v52574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52574 s i)) at 1.
  unfold R.v52574, N.v52574.
  unfold R.v6, N.v6.
  rewrite ?node_12832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52575 (s : N.State) (i : N.Inputs) :
  R.v52575 (state s) (inputs i) = Zmod.unsigned (N.v52575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52575 s i)) at 1.
  unfold R.v52575, N.v52575.
  rewrite ?node_52573.
  rewrite ?node_52574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52576 (s : N.State) (i : N.Inputs) :
  R.v52576 (state s) (inputs i) = Zmod.unsigned (N.v52576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52576 s i)) at 1.
  unfold R.v52576, N.v52576.
  unfold R.v16484, N.v16484.
  rewrite ?node_52575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52577 (s : N.State) (i : N.Inputs) :
  R.v52577 (state s) (inputs i) = Zmod.unsigned (N.v52577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52577 s i)) at 1.
  unfold R.v52577, N.v52577.
  rewrite ?node_52570.
  rewrite ?node_52571.
  rewrite ?node_52572.
  rewrite ?node_52576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52578 (s : N.State) (i : N.Inputs) :
  R.v52578 (state s) (inputs i) = Zmod.unsigned (N.v52578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52578 s i)) at 1.
  unfold R.v52578, N.v52578.
  unfold R.v6, N.v6.
  rewrite ?node_52577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52579 (s : N.State) (i : N.Inputs) :
  R.v52579 (state s) (inputs i) = Zmod.unsigned (N.v52579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52579 s i)) at 1.
  unfold R.v52579, N.v52579.
  rewrite ?node_12888.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52580 (s : N.State) (i : N.Inputs) :
  R.v52580 (state s) (inputs i) = Zmod.unsigned (N.v52580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52580 s i)) at 1.
  unfold R.v52580, N.v52580.
  unfold R.v6, N.v6.
  rewrite ?node_13013.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52581 (s : N.State) (i : N.Inputs) :
  R.v52581 (state s) (inputs i) = Zmod.unsigned (N.v52581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52581 s i)) at 1.
  unfold R.v52581, N.v52581.
  unfold R.v6, N.v6.
  rewrite ?node_13035.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52582 (s : N.State) (i : N.Inputs) :
  R.v52582 (state s) (inputs i) = Zmod.unsigned (N.v52582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52582 s i)) at 1.
  unfold R.v52582, N.v52582.
  rewrite ?node_52579.
  rewrite ?node_52580.
  rewrite ?node_52581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52583 (s : N.State) (i : N.Inputs) :
  R.v52583 (state s) (inputs i) = Zmod.unsigned (N.v52583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52583 s i)) at 1.
  unfold R.v52583, N.v52583.
  rewrite ?node_52578.
  rewrite ?node_52582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52584 (s : N.State) (i : N.Inputs) :
  R.v52584 (state s) (inputs i) = Zmod.unsigned (N.v52584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52584 s i)) at 1.
  unfold R.v52584, N.v52584.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52585 (s : N.State) (i : N.Inputs) :
  R.v52585 (state s) (inputs i) = Zmod.unsigned (N.v52585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52585 s i)) at 1.
  unfold R.v52585, N.v52585.
  rewrite ?node_12877.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52586 (s : N.State) (i : N.Inputs) :
  R.v52586 (state s) (inputs i) = Zmod.unsigned (N.v52586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52586 s i)) at 1.
  unfold R.v52586, N.v52586.
  unfold R.v6, N.v6.
  rewrite ?node_12857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52587 (s : N.State) (i : N.Inputs) :
  R.v52587 (state s) (inputs i) = Zmod.unsigned (N.v52587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52587 s i)) at 1.
  unfold R.v52587, N.v52587.
  unfold R.v6, N.v6.
  rewrite ?node_12832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52588 (s : N.State) (i : N.Inputs) :
  R.v52588 (state s) (inputs i) = Zmod.unsigned (N.v52588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52588 s i)) at 1.
  unfold R.v52588, N.v52588.
  rewrite ?node_52586.
  rewrite ?node_52587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52589 (s : N.State) (i : N.Inputs) :
  R.v52589 (state s) (inputs i) = Zmod.unsigned (N.v52589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52589 s i)) at 1.
  unfold R.v52589, N.v52589.
  unfold R.v16484, N.v16484.
  rewrite ?node_52588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52590 (s : N.State) (i : N.Inputs) :
  R.v52590 (state s) (inputs i) = Zmod.unsigned (N.v52590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52590 s i)) at 1.
  unfold R.v52590, N.v52590.
  rewrite ?node_52585.
  rewrite ?node_52589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52591 (s : N.State) (i : N.Inputs) :
  R.v52591 (state s) (inputs i) = Zmod.unsigned (N.v52591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52591 s i)) at 1.
  unfold R.v52591, N.v52591.
  unfold R.v6, N.v6.
  rewrite ?node_52590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52592 (s : N.State) (i : N.Inputs) :
  R.v52592 (state s) (inputs i) = Zmod.unsigned (N.v52592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52592 s i)) at 1.
  unfold R.v52592, N.v52592.
  rewrite ?node_12878.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52593 (s : N.State) (i : N.Inputs) :
  R.v52593 (state s) (inputs i) = Zmod.unsigned (N.v52593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52593 s i)) at 1.
  unfold R.v52593, N.v52593.
  unfold R.v6, N.v6.
  rewrite ?node_13013.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52594 (s : N.State) (i : N.Inputs) :
  R.v52594 (state s) (inputs i) = Zmod.unsigned (N.v52594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52594 s i)) at 1.
  unfold R.v52594, N.v52594.
  rewrite ?node_52592.
  rewrite ?node_52593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52595 (s : N.State) (i : N.Inputs) :
  R.v52595 (state s) (inputs i) = Zmod.unsigned (N.v52595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52595 s i)) at 1.
  unfold R.v52595, N.v52595.
  rewrite ?node_52591.
  rewrite ?node_52594.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52596 (s : N.State) (i : N.Inputs) :
  R.v52596 (state s) (inputs i) = Zmod.unsigned (N.v52596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52596 s i)) at 1.
  unfold R.v52596, N.v52596.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52597 (s : N.State) (i : N.Inputs) :
  R.v52597 (state s) (inputs i) = Zmod.unsigned (N.v52597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52597 s i)) at 1.
  unfold R.v52597, N.v52597.
  rewrite ?node_12887.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52598 (s : N.State) (i : N.Inputs) :
  R.v52598 (state s) (inputs i) = Zmod.unsigned (N.v52598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52598 s i)) at 1.
  unfold R.v52598, N.v52598.
  unfold R.v6, N.v6.
  rewrite ?node_12883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52599 (s : N.State) (i : N.Inputs) :
  R.v52599 (state s) (inputs i) = Zmod.unsigned (N.v52599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52599 s i)) at 1.
  unfold R.v52599, N.v52599.
  unfold R.v6, N.v6.
  rewrite ?node_12878.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52600 (s : N.State) (i : N.Inputs) :
  R.v52600 (state s) (inputs i) = Zmod.unsigned (N.v52600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52600 s i)) at 1.
  unfold R.v52600, N.v52600.
  rewrite ?node_52598.
  rewrite ?node_52599.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52601 (s : N.State) (i : N.Inputs) :
  R.v52601 (state s) (inputs i) = Zmod.unsigned (N.v52601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52601 s i)) at 1.
  unfold R.v52601, N.v52601.
  unfold R.v16484, N.v16484.
  rewrite ?node_52600.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52602 (s : N.State) (i : N.Inputs) :
  R.v52602 (state s) (inputs i) = Zmod.unsigned (N.v52602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52602 s i)) at 1.
  unfold R.v52602, N.v52602.
  rewrite ?node_52597.
  rewrite ?node_52601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52603 (s : N.State) (i : N.Inputs) :
  R.v52603 (state s) (inputs i) = Zmod.unsigned (N.v52603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52603 s i)) at 1.
  unfold R.v52603, N.v52603.
  unfold R.v6, N.v6.
  rewrite ?node_52602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52604 (s : N.State) (i : N.Inputs) :
  R.v52604 (state s) (inputs i) = Zmod.unsigned (N.v52604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52604 s i)) at 1.
  unfold R.v52604, N.v52604.
  rewrite ?node_12888.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52605 (s : N.State) (i : N.Inputs) :
  R.v52605 (state s) (inputs i) = Zmod.unsigned (N.v52605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52605 s i)) at 1.
  unfold R.v52605, N.v52605.
  unfold R.v6, N.v6.
  rewrite ?node_13035.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52606 (s : N.State) (i : N.Inputs) :
  R.v52606 (state s) (inputs i) = Zmod.unsigned (N.v52606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52606 s i)) at 1.
  unfold R.v52606, N.v52606.
  rewrite ?node_52604.
  rewrite ?node_52605.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52607 (s : N.State) (i : N.Inputs) :
  R.v52607 (state s) (inputs i) = Zmod.unsigned (N.v52607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52607 s i)) at 1.
  unfold R.v52607, N.v52607.
  rewrite ?node_52603.
  rewrite ?node_52606.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52608 (s : N.State) (i : N.Inputs) :
  R.v52608 (state s) (inputs i) = Zmod.unsigned (N.v52608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52608 s i)) at 1.
  unfold R.v52608, N.v52608.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52609 (s : N.State) (i : N.Inputs) :
  R.v52609 (state s) (inputs i) = Zmod.unsigned (N.v52609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52609 s i)) at 1.
  unfold R.v52609, N.v52609.
  rewrite ?node_12904.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52610 (s : N.State) (i : N.Inputs) :
  R.v52610 (state s) (inputs i) = Zmod.unsigned (N.v52610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52610 s i)) at 1.
  unfold R.v52610, N.v52610.
  rewrite ?node_12900.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52611 (s : N.State) (i : N.Inputs) :
  R.v52611 (state s) (inputs i) = Zmod.unsigned (N.v52611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52611 s i)) at 1.
  unfold R.v52611, N.v52611.
  rewrite ?node_12898.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52612 (s : N.State) (i : N.Inputs) :
  R.v52612 (state s) (inputs i) = Zmod.unsigned (N.v52612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52612 s i)) at 1.
  unfold R.v52612, N.v52612.
  unfold R.v6, N.v6.
  rewrite ?node_12894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52613 (s : N.State) (i : N.Inputs) :
  R.v52613 (state s) (inputs i) = Zmod.unsigned (N.v52613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52613 s i)) at 1.
  unfold R.v52613, N.v52613.
  unfold R.v6, N.v6.
  rewrite ?node_12891.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52614 (s : N.State) (i : N.Inputs) :
  R.v52614 (state s) (inputs i) = Zmod.unsigned (N.v52614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52614 s i)) at 1.
  unfold R.v52614, N.v52614.
  rewrite ?node_52612.
  rewrite ?node_52613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52615 (s : N.State) (i : N.Inputs) :
  R.v52615 (state s) (inputs i) = Zmod.unsigned (N.v52615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52615 s i)) at 1.
  unfold R.v52615, N.v52615.
  unfold R.v16484, N.v16484.
  rewrite ?node_52614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52616 (s : N.State) (i : N.Inputs) :
  R.v52616 (state s) (inputs i) = Zmod.unsigned (N.v52616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52616 s i)) at 1.
  unfold R.v52616, N.v52616.
  rewrite ?node_52609.
  rewrite ?node_52610.
  rewrite ?node_52611.
  rewrite ?node_52615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52617 (s : N.State) (i : N.Inputs) :
  R.v52617 (state s) (inputs i) = Zmod.unsigned (N.v52617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52617 s i)) at 1.
  unfold R.v52617, N.v52617.
  unfold R.v6, N.v6.
  rewrite ?node_52616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52618 (s : N.State) (i : N.Inputs) :
  R.v52618 (state s) (inputs i) = Zmod.unsigned (N.v52618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52618 s i)) at 1.
  unfold R.v52618, N.v52618.
  rewrite ?node_12905.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52619 (s : N.State) (i : N.Inputs) :
  R.v52619 (state s) (inputs i) = Zmod.unsigned (N.v52619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52619 s i)) at 1.
  unfold R.v52619, N.v52619.
  unfold R.v6, N.v6.
  rewrite ?node_13030.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52620 (s : N.State) (i : N.Inputs) :
  R.v52620 (state s) (inputs i) = Zmod.unsigned (N.v52620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52620 s i)) at 1.
  unfold R.v52620, N.v52620.
  unfold R.v6, N.v6.
  rewrite ?node_13039.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52621 (s : N.State) (i : N.Inputs) :
  R.v52621 (state s) (inputs i) = Zmod.unsigned (N.v52621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52621 s i)) at 1.
  unfold R.v52621, N.v52621.
  rewrite ?node_52618.
  rewrite ?node_52619.
  rewrite ?node_52620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52622 (s : N.State) (i : N.Inputs) :
  R.v52622 (state s) (inputs i) = Zmod.unsigned (N.v52622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52622 s i)) at 1.
  unfold R.v52622, N.v52622.
  rewrite ?node_52617.
  rewrite ?node_52621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52623 (s : N.State) (i : N.Inputs) :
  R.v52623 (state s) (inputs i) = Zmod.unsigned (N.v52623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52623 s i)) at 1.
  unfold R.v52623, N.v52623.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52624 (s : N.State) (i : N.Inputs) :
  R.v52624 (state s) (inputs i) = Zmod.unsigned (N.v52624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52624 s i)) at 1.
  unfold R.v52624, N.v52624.
  rewrite ?node_12898.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52625 (s : N.State) (i : N.Inputs) :
  R.v52625 (state s) (inputs i) = Zmod.unsigned (N.v52625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52625 s i)) at 1.
  unfold R.v52625, N.v52625.
  unfold R.v6, N.v6.
  rewrite ?node_12894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52626 (s : N.State) (i : N.Inputs) :
  R.v52626 (state s) (inputs i) = Zmod.unsigned (N.v52626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52626 s i)) at 1.
  unfold R.v52626, N.v52626.
  unfold R.v6, N.v6.
  rewrite ?node_12891.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52627 (s : N.State) (i : N.Inputs) :
  R.v52627 (state s) (inputs i) = Zmod.unsigned (N.v52627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52627 s i)) at 1.
  unfold R.v52627, N.v52627.
  rewrite ?node_52625.
  rewrite ?node_52626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52628 (s : N.State) (i : N.Inputs) :
  R.v52628 (state s) (inputs i) = Zmod.unsigned (N.v52628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52628 s i)) at 1.
  unfold R.v52628, N.v52628.
  unfold R.v16484, N.v16484.
  rewrite ?node_52627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52629 (s : N.State) (i : N.Inputs) :
  R.v52629 (state s) (inputs i) = Zmod.unsigned (N.v52629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52629 s i)) at 1.
  unfold R.v52629, N.v52629.
  rewrite ?node_52624.
  rewrite ?node_52628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52630 (s : N.State) (i : N.Inputs) :
  R.v52630 (state s) (inputs i) = Zmod.unsigned (N.v52630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52630 s i)) at 1.
  unfold R.v52630, N.v52630.
  unfold R.v6, N.v6.
  rewrite ?node_52629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52631 (s : N.State) (i : N.Inputs) :
  R.v52631 (state s) (inputs i) = Zmod.unsigned (N.v52631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52631 s i)) at 1.
  unfold R.v52631, N.v52631.
  rewrite ?node_12899.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52632 (s : N.State) (i : N.Inputs) :
  R.v52632 (state s) (inputs i) = Zmod.unsigned (N.v52632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52632 s i)) at 1.
  unfold R.v52632, N.v52632.
  unfold R.v6, N.v6.
  rewrite ?node_13030.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52633 (s : N.State) (i : N.Inputs) :
  R.v52633 (state s) (inputs i) = Zmod.unsigned (N.v52633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52633 s i)) at 1.
  unfold R.v52633, N.v52633.
  rewrite ?node_52631.
  rewrite ?node_52632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52634 (s : N.State) (i : N.Inputs) :
  R.v52634 (state s) (inputs i) = Zmod.unsigned (N.v52634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52634 s i)) at 1.
  unfold R.v52634, N.v52634.
  rewrite ?node_52630.
  rewrite ?node_52633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52635 (s : N.State) (i : N.Inputs) :
  R.v52635 (state s) (inputs i) = Zmod.unsigned (N.v52635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52635 s i)) at 1.
  unfold R.v52635, N.v52635.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52636 (s : N.State) (i : N.Inputs) :
  R.v52636 (state s) (inputs i) = Zmod.unsigned (N.v52636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52636 s i)) at 1.
  unfold R.v52636, N.v52636.
  rewrite ?node_12904.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52637 (s : N.State) (i : N.Inputs) :
  R.v52637 (state s) (inputs i) = Zmod.unsigned (N.v52637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52637 s i)) at 1.
  unfold R.v52637, N.v52637.
  unfold R.v6, N.v6.
  rewrite ?node_12900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52638 (s : N.State) (i : N.Inputs) :
  R.v52638 (state s) (inputs i) = Zmod.unsigned (N.v52638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52638 s i)) at 1.
  unfold R.v52638, N.v52638.
  unfold R.v6, N.v6.
  rewrite ?node_12899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52639 (s : N.State) (i : N.Inputs) :
  R.v52639 (state s) (inputs i) = Zmod.unsigned (N.v52639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52639 s i)) at 1.
  unfold R.v52639, N.v52639.
  rewrite ?node_52637.
  rewrite ?node_52638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52640 (s : N.State) (i : N.Inputs) :
  R.v52640 (state s) (inputs i) = Zmod.unsigned (N.v52640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52640 s i)) at 1.
  unfold R.v52640, N.v52640.
  unfold R.v16484, N.v16484.
  rewrite ?node_52639.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52641 (s : N.State) (i : N.Inputs) :
  R.v52641 (state s) (inputs i) = Zmod.unsigned (N.v52641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52641 s i)) at 1.
  unfold R.v52641, N.v52641.
  rewrite ?node_52636.
  rewrite ?node_52640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52642 (s : N.State) (i : N.Inputs) :
  R.v52642 (state s) (inputs i) = Zmod.unsigned (N.v52642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52642 s i)) at 1.
  unfold R.v52642, N.v52642.
  unfold R.v6, N.v6.
  rewrite ?node_52641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52643 (s : N.State) (i : N.Inputs) :
  R.v52643 (state s) (inputs i) = Zmod.unsigned (N.v52643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52643 s i)) at 1.
  unfold R.v52643, N.v52643.
  rewrite ?node_12905.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52644 (s : N.State) (i : N.Inputs) :
  R.v52644 (state s) (inputs i) = Zmod.unsigned (N.v52644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52644 s i)) at 1.
  unfold R.v52644, N.v52644.
  unfold R.v6, N.v6.
  rewrite ?node_13039.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52645 (s : N.State) (i : N.Inputs) :
  R.v52645 (state s) (inputs i) = Zmod.unsigned (N.v52645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52645 s i)) at 1.
  unfold R.v52645, N.v52645.
  rewrite ?node_52643.
  rewrite ?node_52644.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52646 (s : N.State) (i : N.Inputs) :
  R.v52646 (state s) (inputs i) = Zmod.unsigned (N.v52646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52646 s i)) at 1.
  unfold R.v52646, N.v52646.
  rewrite ?node_52642.
  rewrite ?node_52645.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52647 (s : N.State) (i : N.Inputs) :
  R.v52647 (state s) (inputs i) = Zmod.unsigned (N.v52647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52647 s i)) at 1.
  unfold R.v52647, N.v52647.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52648 (s : N.State) (i : N.Inputs) :
  R.v52648 (state s) (inputs i) = Zmod.unsigned (N.v52648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52648 s i)) at 1.
  unfold R.v52648, N.v52648.
  rewrite ?node_13013.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52649 (s : N.State) (i : N.Inputs) :
  R.v52649 (state s) (inputs i) = Zmod.unsigned (N.v52649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52649 s i)) at 1.
  unfold R.v52649, N.v52649.
  rewrite ?node_13009.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52650 (s : N.State) (i : N.Inputs) :
  R.v52650 (state s) (inputs i) = Zmod.unsigned (N.v52650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52650 s i)) at 1.
  unfold R.v52650, N.v52650.
  rewrite ?node_13003.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52651 (s : N.State) (i : N.Inputs) :
  R.v52651 (state s) (inputs i) = Zmod.unsigned (N.v52651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52651 s i)) at 1.
  unfold R.v52651, N.v52651.
  unfold R.v6, N.v6.
  rewrite ?node_12983.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52652 (s : N.State) (i : N.Inputs) :
  R.v52652 (state s) (inputs i) = Zmod.unsigned (N.v52652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52652 s i)) at 1.
  unfold R.v52652, N.v52652.
  unfold R.v6, N.v6.
  rewrite ?node_12959.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52653 (s : N.State) (i : N.Inputs) :
  R.v52653 (state s) (inputs i) = Zmod.unsigned (N.v52653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52653 s i)) at 1.
  unfold R.v52653, N.v52653.
  rewrite ?node_52651.
  rewrite ?node_52652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52654 (s : N.State) (i : N.Inputs) :
  R.v52654 (state s) (inputs i) = Zmod.unsigned (N.v52654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52654 s i)) at 1.
  unfold R.v52654, N.v52654.
  unfold R.v16484, N.v16484.
  rewrite ?node_52653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52655 (s : N.State) (i : N.Inputs) :
  R.v52655 (state s) (inputs i) = Zmod.unsigned (N.v52655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52655 s i)) at 1.
  unfold R.v52655, N.v52655.
  rewrite ?node_52648.
  rewrite ?node_52649.
  rewrite ?node_52650.
  rewrite ?node_52654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52656 (s : N.State) (i : N.Inputs) :
  R.v52656 (state s) (inputs i) = Zmod.unsigned (N.v52656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52656 s i)) at 1.
  unfold R.v52656, N.v52656.
  unfold R.v6, N.v6.
  rewrite ?node_52655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52657 (s : N.State) (i : N.Inputs) :
  R.v52657 (state s) (inputs i) = Zmod.unsigned (N.v52657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52657 s i)) at 1.
  unfold R.v52657, N.v52657.
  rewrite ?node_13014.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52658 (s : N.State) (i : N.Inputs) :
  R.v52658 (state s) (inputs i) = Zmod.unsigned (N.v52658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52658 s i)) at 1.
  unfold R.v52658, N.v52658.
  unfold R.v6, N.v6.
  rewrite ?node_13138.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52659 (s : N.State) (i : N.Inputs) :
  R.v52659 (state s) (inputs i) = Zmod.unsigned (N.v52659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52659 s i)) at 1.
  unfold R.v52659, N.v52659.
  unfold R.v6, N.v6.
  rewrite ?node_13160.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52660 (s : N.State) (i : N.Inputs) :
  R.v52660 (state s) (inputs i) = Zmod.unsigned (N.v52660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52660 s i)) at 1.
  unfold R.v52660, N.v52660.
  rewrite ?node_52657.
  rewrite ?node_52658.
  rewrite ?node_52659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52661 (s : N.State) (i : N.Inputs) :
  R.v52661 (state s) (inputs i) = Zmod.unsigned (N.v52661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52661 s i)) at 1.
  unfold R.v52661, N.v52661.
  rewrite ?node_52656.
  rewrite ?node_52660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52662 (s : N.State) (i : N.Inputs) :
  R.v52662 (state s) (inputs i) = Zmod.unsigned (N.v52662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52662 s i)) at 1.
  unfold R.v52662, N.v52662.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52663 (s : N.State) (i : N.Inputs) :
  R.v52663 (state s) (inputs i) = Zmod.unsigned (N.v52663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52663 s i)) at 1.
  unfold R.v52663, N.v52663.
  rewrite ?node_13003.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52664 (s : N.State) (i : N.Inputs) :
  R.v52664 (state s) (inputs i) = Zmod.unsigned (N.v52664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52664 s i)) at 1.
  unfold R.v52664, N.v52664.
  unfold R.v6, N.v6.
  rewrite ?node_12983.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52665 (s : N.State) (i : N.Inputs) :
  R.v52665 (state s) (inputs i) = Zmod.unsigned (N.v52665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52665 s i)) at 1.
  unfold R.v52665, N.v52665.
  unfold R.v6, N.v6.
  rewrite ?node_12959.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52666 (s : N.State) (i : N.Inputs) :
  R.v52666 (state s) (inputs i) = Zmod.unsigned (N.v52666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52666 s i)) at 1.
  unfold R.v52666, N.v52666.
  rewrite ?node_52664.
  rewrite ?node_52665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52667 (s : N.State) (i : N.Inputs) :
  R.v52667 (state s) (inputs i) = Zmod.unsigned (N.v52667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52667 s i)) at 1.
  unfold R.v52667, N.v52667.
  unfold R.v16484, N.v16484.
  rewrite ?node_52666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52668 (s : N.State) (i : N.Inputs) :
  R.v52668 (state s) (inputs i) = Zmod.unsigned (N.v52668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52668 s i)) at 1.
  unfold R.v52668, N.v52668.
  rewrite ?node_52663.
  rewrite ?node_52667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52669 (s : N.State) (i : N.Inputs) :
  R.v52669 (state s) (inputs i) = Zmod.unsigned (N.v52669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52669 s i)) at 1.
  unfold R.v52669, N.v52669.
  unfold R.v6, N.v6.
  rewrite ?node_52668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52670 (s : N.State) (i : N.Inputs) :
  R.v52670 (state s) (inputs i) = Zmod.unsigned (N.v52670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52670 s i)) at 1.
  unfold R.v52670, N.v52670.
  rewrite ?node_13004.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52671 (s : N.State) (i : N.Inputs) :
  R.v52671 (state s) (inputs i) = Zmod.unsigned (N.v52671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52671 s i)) at 1.
  unfold R.v52671, N.v52671.
  unfold R.v6, N.v6.
  rewrite ?node_13138.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52672 (s : N.State) (i : N.Inputs) :
  R.v52672 (state s) (inputs i) = Zmod.unsigned (N.v52672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52672 s i)) at 1.
  unfold R.v52672, N.v52672.
  rewrite ?node_52670.
  rewrite ?node_52671.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52673 (s : N.State) (i : N.Inputs) :
  R.v52673 (state s) (inputs i) = Zmod.unsigned (N.v52673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52673 s i)) at 1.
  unfold R.v52673, N.v52673.
  rewrite ?node_52669.
  rewrite ?node_52672.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52674 (s : N.State) (i : N.Inputs) :
  R.v52674 (state s) (inputs i) = Zmod.unsigned (N.v52674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52674 s i)) at 1.
  unfold R.v52674, N.v52674.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52675 (s : N.State) (i : N.Inputs) :
  R.v52675 (state s) (inputs i) = Zmod.unsigned (N.v52675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52675 s i)) at 1.
  unfold R.v52675, N.v52675.
  rewrite ?node_13013.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52676 (s : N.State) (i : N.Inputs) :
  R.v52676 (state s) (inputs i) = Zmod.unsigned (N.v52676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52676 s i)) at 1.
  unfold R.v52676, N.v52676.
  unfold R.v6, N.v6.
  rewrite ?node_13009.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52677 (s : N.State) (i : N.Inputs) :
  R.v52677 (state s) (inputs i) = Zmod.unsigned (N.v52677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52677 s i)) at 1.
  unfold R.v52677, N.v52677.
  unfold R.v6, N.v6.
  rewrite ?node_13004.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52678 (s : N.State) (i : N.Inputs) :
  R.v52678 (state s) (inputs i) = Zmod.unsigned (N.v52678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52678 s i)) at 1.
  unfold R.v52678, N.v52678.
  rewrite ?node_52676.
  rewrite ?node_52677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52679 (s : N.State) (i : N.Inputs) :
  R.v52679 (state s) (inputs i) = Zmod.unsigned (N.v52679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52679 s i)) at 1.
  unfold R.v52679, N.v52679.
  unfold R.v16484, N.v16484.
  rewrite ?node_52678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52680 (s : N.State) (i : N.Inputs) :
  R.v52680 (state s) (inputs i) = Zmod.unsigned (N.v52680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52680 s i)) at 1.
  unfold R.v52680, N.v52680.
  rewrite ?node_52675.
  rewrite ?node_52679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52681 (s : N.State) (i : N.Inputs) :
  R.v52681 (state s) (inputs i) = Zmod.unsigned (N.v52681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52681 s i)) at 1.
  unfold R.v52681, N.v52681.
  unfold R.v6, N.v6.
  rewrite ?node_52680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52682 (s : N.State) (i : N.Inputs) :
  R.v52682 (state s) (inputs i) = Zmod.unsigned (N.v52682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52682 s i)) at 1.
  unfold R.v52682, N.v52682.
  rewrite ?node_13014.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52683 (s : N.State) (i : N.Inputs) :
  R.v52683 (state s) (inputs i) = Zmod.unsigned (N.v52683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52683 s i)) at 1.
  unfold R.v52683, N.v52683.
  unfold R.v6, N.v6.
  rewrite ?node_13160.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52684 (s : N.State) (i : N.Inputs) :
  R.v52684 (state s) (inputs i) = Zmod.unsigned (N.v52684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52684 s i)) at 1.
  unfold R.v52684, N.v52684.
  rewrite ?node_52682.
  rewrite ?node_52683.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52685 (s : N.State) (i : N.Inputs) :
  R.v52685 (state s) (inputs i) = Zmod.unsigned (N.v52685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52685 s i)) at 1.
  unfold R.v52685, N.v52685.
  rewrite ?node_52681.
  rewrite ?node_52684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52686 (s : N.State) (i : N.Inputs) :
  R.v52686 (state s) (inputs i) = Zmod.unsigned (N.v52686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52686 s i)) at 1.
  unfold R.v52686, N.v52686.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52687 (s : N.State) (i : N.Inputs) :
  R.v52687 (state s) (inputs i) = Zmod.unsigned (N.v52687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52687 s i)) at 1.
  unfold R.v52687, N.v52687.
  rewrite ?node_13030.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52688 (s : N.State) (i : N.Inputs) :
  R.v52688 (state s) (inputs i) = Zmod.unsigned (N.v52688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52688 s i)) at 1.
  unfold R.v52688, N.v52688.
  rewrite ?node_13026.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52689 (s : N.State) (i : N.Inputs) :
  R.v52689 (state s) (inputs i) = Zmod.unsigned (N.v52689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52689 s i)) at 1.
  unfold R.v52689, N.v52689.
  rewrite ?node_13024.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52690 (s : N.State) (i : N.Inputs) :
  R.v52690 (state s) (inputs i) = Zmod.unsigned (N.v52690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52690 s i)) at 1.
  unfold R.v52690, N.v52690.
  unfold R.v6, N.v6.
  rewrite ?node_13020.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52691 (s : N.State) (i : N.Inputs) :
  R.v52691 (state s) (inputs i) = Zmod.unsigned (N.v52691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52691 s i)) at 1.
  unfold R.v52691, N.v52691.
  unfold R.v6, N.v6.
  rewrite ?node_13017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52692 (s : N.State) (i : N.Inputs) :
  R.v52692 (state s) (inputs i) = Zmod.unsigned (N.v52692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52692 s i)) at 1.
  unfold R.v52692, N.v52692.
  rewrite ?node_52690.
  rewrite ?node_52691.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52693 (s : N.State) (i : N.Inputs) :
  R.v52693 (state s) (inputs i) = Zmod.unsigned (N.v52693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52693 s i)) at 1.
  unfold R.v52693, N.v52693.
  unfold R.v16484, N.v16484.
  rewrite ?node_52692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52694 (s : N.State) (i : N.Inputs) :
  R.v52694 (state s) (inputs i) = Zmod.unsigned (N.v52694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52694 s i)) at 1.
  unfold R.v52694, N.v52694.
  rewrite ?node_52687.
  rewrite ?node_52688.
  rewrite ?node_52689.
  rewrite ?node_52693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52695 (s : N.State) (i : N.Inputs) :
  R.v52695 (state s) (inputs i) = Zmod.unsigned (N.v52695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52695 s i)) at 1.
  unfold R.v52695, N.v52695.
  unfold R.v6, N.v6.
  rewrite ?node_52694.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52696 (s : N.State) (i : N.Inputs) :
  R.v52696 (state s) (inputs i) = Zmod.unsigned (N.v52696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52696 s i)) at 1.
  unfold R.v52696, N.v52696.
  rewrite ?node_13031.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52697 (s : N.State) (i : N.Inputs) :
  R.v52697 (state s) (inputs i) = Zmod.unsigned (N.v52697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52697 s i)) at 1.
  unfold R.v52697, N.v52697.
  unfold R.v6, N.v6.
  rewrite ?node_13155.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52698 (s : N.State) (i : N.Inputs) :
  R.v52698 (state s) (inputs i) = Zmod.unsigned (N.v52698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52698 s i)) at 1.
  unfold R.v52698, N.v52698.
  unfold R.v6, N.v6.
  rewrite ?node_13164.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52699 (s : N.State) (i : N.Inputs) :
  R.v52699 (state s) (inputs i) = Zmod.unsigned (N.v52699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52699 s i)) at 1.
  unfold R.v52699, N.v52699.
  rewrite ?node_52696.
  rewrite ?node_52697.
  rewrite ?node_52698.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52700 (s : N.State) (i : N.Inputs) :
  R.v52700 (state s) (inputs i) = Zmod.unsigned (N.v52700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52700 s i)) at 1.
  unfold R.v52700, N.v52700.
  rewrite ?node_52695.
  rewrite ?node_52699.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52701 (s : N.State) (i : N.Inputs) :
  R.v52701 (state s) (inputs i) = Zmod.unsigned (N.v52701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52701 s i)) at 1.
  unfold R.v52701, N.v52701.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52702 (s : N.State) (i : N.Inputs) :
  R.v52702 (state s) (inputs i) = Zmod.unsigned (N.v52702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52702 s i)) at 1.
  unfold R.v52702, N.v52702.
  rewrite ?node_13024.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52703 (s : N.State) (i : N.Inputs) :
  R.v52703 (state s) (inputs i) = Zmod.unsigned (N.v52703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52703 s i)) at 1.
  unfold R.v52703, N.v52703.
  unfold R.v6, N.v6.
  rewrite ?node_13020.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52704 (s : N.State) (i : N.Inputs) :
  R.v52704 (state s) (inputs i) = Zmod.unsigned (N.v52704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52704 s i)) at 1.
  unfold R.v52704, N.v52704.
  unfold R.v6, N.v6.
  rewrite ?node_13017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52705 (s : N.State) (i : N.Inputs) :
  R.v52705 (state s) (inputs i) = Zmod.unsigned (N.v52705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52705 s i)) at 1.
  unfold R.v52705, N.v52705.
  rewrite ?node_52703.
  rewrite ?node_52704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52706 (s : N.State) (i : N.Inputs) :
  R.v52706 (state s) (inputs i) = Zmod.unsigned (N.v52706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52706 s i)) at 1.
  unfold R.v52706, N.v52706.
  unfold R.v16484, N.v16484.
  rewrite ?node_52705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52707 (s : N.State) (i : N.Inputs) :
  R.v52707 (state s) (inputs i) = Zmod.unsigned (N.v52707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52707 s i)) at 1.
  unfold R.v52707, N.v52707.
  rewrite ?node_52702.
  rewrite ?node_52706.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52708 (s : N.State) (i : N.Inputs) :
  R.v52708 (state s) (inputs i) = Zmod.unsigned (N.v52708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52708 s i)) at 1.
  unfold R.v52708, N.v52708.
  unfold R.v6, N.v6.
  rewrite ?node_52707.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52709 (s : N.State) (i : N.Inputs) :
  R.v52709 (state s) (inputs i) = Zmod.unsigned (N.v52709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52709 s i)) at 1.
  unfold R.v52709, N.v52709.
  rewrite ?node_13025.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52710 (s : N.State) (i : N.Inputs) :
  R.v52710 (state s) (inputs i) = Zmod.unsigned (N.v52710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52710 s i)) at 1.
  unfold R.v52710, N.v52710.
  unfold R.v6, N.v6.
  rewrite ?node_13155.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52711 (s : N.State) (i : N.Inputs) :
  R.v52711 (state s) (inputs i) = Zmod.unsigned (N.v52711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52711 s i)) at 1.
  unfold R.v52711, N.v52711.
  rewrite ?node_52709.
  rewrite ?node_52710.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52712 (s : N.State) (i : N.Inputs) :
  R.v52712 (state s) (inputs i) = Zmod.unsigned (N.v52712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52712 s i)) at 1.
  unfold R.v52712, N.v52712.
  rewrite ?node_52708.
  rewrite ?node_52711.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52713 (s : N.State) (i : N.Inputs) :
  R.v52713 (state s) (inputs i) = Zmod.unsigned (N.v52713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52713 s i)) at 1.
  unfold R.v52713, N.v52713.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52714 (s : N.State) (i : N.Inputs) :
  R.v52714 (state s) (inputs i) = Zmod.unsigned (N.v52714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52714 s i)) at 1.
  unfold R.v52714, N.v52714.
  rewrite ?node_13030.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52715 (s : N.State) (i : N.Inputs) :
  R.v52715 (state s) (inputs i) = Zmod.unsigned (N.v52715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52715 s i)) at 1.
  unfold R.v52715, N.v52715.
  unfold R.v6, N.v6.
  rewrite ?node_13026.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52716 (s : N.State) (i : N.Inputs) :
  R.v52716 (state s) (inputs i) = Zmod.unsigned (N.v52716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52716 s i)) at 1.
  unfold R.v52716, N.v52716.
  unfold R.v6, N.v6.
  rewrite ?node_13025.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52717 (s : N.State) (i : N.Inputs) :
  R.v52717 (state s) (inputs i) = Zmod.unsigned (N.v52717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52717 s i)) at 1.
  unfold R.v52717, N.v52717.
  rewrite ?node_52715.
  rewrite ?node_52716.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52718 (s : N.State) (i : N.Inputs) :
  R.v52718 (state s) (inputs i) = Zmod.unsigned (N.v52718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52718 s i)) at 1.
  unfold R.v52718, N.v52718.
  unfold R.v16484, N.v16484.
  rewrite ?node_52717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52719 (s : N.State) (i : N.Inputs) :
  R.v52719 (state s) (inputs i) = Zmod.unsigned (N.v52719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52719 s i)) at 1.
  unfold R.v52719, N.v52719.
  rewrite ?node_52714.
  rewrite ?node_52718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52720 (s : N.State) (i : N.Inputs) :
  R.v52720 (state s) (inputs i) = Zmod.unsigned (N.v52720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52720 s i)) at 1.
  unfold R.v52720, N.v52720.
  unfold R.v6, N.v6.
  rewrite ?node_52719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52721 (s : N.State) (i : N.Inputs) :
  R.v52721 (state s) (inputs i) = Zmod.unsigned (N.v52721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52721 s i)) at 1.
  unfold R.v52721, N.v52721.
  rewrite ?node_13031.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52722 (s : N.State) (i : N.Inputs) :
  R.v52722 (state s) (inputs i) = Zmod.unsigned (N.v52722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52722 s i)) at 1.
  unfold R.v52722, N.v52722.
  unfold R.v6, N.v6.
  rewrite ?node_13164.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52723 (s : N.State) (i : N.Inputs) :
  R.v52723 (state s) (inputs i) = Zmod.unsigned (N.v52723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52723 s i)) at 1.
  unfold R.v52723, N.v52723.
  rewrite ?node_52721.
  rewrite ?node_52722.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52724 (s : N.State) (i : N.Inputs) :
  R.v52724 (state s) (inputs i) = Zmod.unsigned (N.v52724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52724 s i)) at 1.
  unfold R.v52724, N.v52724.
  rewrite ?node_52720.
  rewrite ?node_52723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52725 (s : N.State) (i : N.Inputs) :
  R.v52725 (state s) (inputs i) = Zmod.unsigned (N.v52725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52725 s i)) at 1.
  unfold R.v52725, N.v52725.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52726 (s : N.State) (i : N.Inputs) :
  R.v52726 (state s) (inputs i) = Zmod.unsigned (N.v52726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52726 s i)) at 1.
  unfold R.v52726, N.v52726.
  rewrite ?node_13138.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52727 (s : N.State) (i : N.Inputs) :
  R.v52727 (state s) (inputs i) = Zmod.unsigned (N.v52727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52727 s i)) at 1.
  unfold R.v52727, N.v52727.
  rewrite ?node_13134.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52728 (s : N.State) (i : N.Inputs) :
  R.v52728 (state s) (inputs i) = Zmod.unsigned (N.v52728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52728 s i)) at 1.
  unfold R.v52728, N.v52728.
  rewrite ?node_13130.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52729 (s : N.State) (i : N.Inputs) :
  R.v52729 (state s) (inputs i) = Zmod.unsigned (N.v52729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52729 s i)) at 1.
  unfold R.v52729, N.v52729.
  unfold R.v6, N.v6.
  rewrite ?node_13110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52730 (s : N.State) (i : N.Inputs) :
  R.v52730 (state s) (inputs i) = Zmod.unsigned (N.v52730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52730 s i)) at 1.
  unfold R.v52730, N.v52730.
  unfold R.v6, N.v6.
  rewrite ?node_13086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52731 (s : N.State) (i : N.Inputs) :
  R.v52731 (state s) (inputs i) = Zmod.unsigned (N.v52731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52731 s i)) at 1.
  unfold R.v52731, N.v52731.
  rewrite ?node_52729.
  rewrite ?node_52730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52732 (s : N.State) (i : N.Inputs) :
  R.v52732 (state s) (inputs i) = Zmod.unsigned (N.v52732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52732 s i)) at 1.
  unfold R.v52732, N.v52732.
  unfold R.v16484, N.v16484.
  rewrite ?node_52731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52733 (s : N.State) (i : N.Inputs) :
  R.v52733 (state s) (inputs i) = Zmod.unsigned (N.v52733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52733 s i)) at 1.
  unfold R.v52733, N.v52733.
  rewrite ?node_52726.
  rewrite ?node_52727.
  rewrite ?node_52728.
  rewrite ?node_52732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52734 (s : N.State) (i : N.Inputs) :
  R.v52734 (state s) (inputs i) = Zmod.unsigned (N.v52734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52734 s i)) at 1.
  unfold R.v52734, N.v52734.
  unfold R.v6, N.v6.
  rewrite ?node_52733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52735 (s : N.State) (i : N.Inputs) :
  R.v52735 (state s) (inputs i) = Zmod.unsigned (N.v52735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52735 s i)) at 1.
  unfold R.v52735, N.v52735.
  rewrite ?node_13139.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52736 (s : N.State) (i : N.Inputs) :
  R.v52736 (state s) (inputs i) = Zmod.unsigned (N.v52736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52736 s i)) at 1.
  unfold R.v52736, N.v52736.
  unfold R.v6, N.v6.
  rewrite ?node_13265.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52737 (s : N.State) (i : N.Inputs) :
  R.v52737 (state s) (inputs i) = Zmod.unsigned (N.v52737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52737 s i)) at 1.
  unfold R.v52737, N.v52737.
  unfold R.v6, N.v6.
  rewrite ?node_13281.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52738 (s : N.State) (i : N.Inputs) :
  R.v52738 (state s) (inputs i) = Zmod.unsigned (N.v52738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52738 s i)) at 1.
  unfold R.v52738, N.v52738.
  rewrite ?node_52735.
  rewrite ?node_52736.
  rewrite ?node_52737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52739 (s : N.State) (i : N.Inputs) :
  R.v52739 (state s) (inputs i) = Zmod.unsigned (N.v52739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52739 s i)) at 1.
  unfold R.v52739, N.v52739.
  rewrite ?node_52734.
  rewrite ?node_52738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52740 (s : N.State) (i : N.Inputs) :
  R.v52740 (state s) (inputs i) = Zmod.unsigned (N.v52740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52740 s i)) at 1.
  unfold R.v52740, N.v52740.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52741 (s : N.State) (i : N.Inputs) :
  R.v52741 (state s) (inputs i) = Zmod.unsigned (N.v52741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52741 s i)) at 1.
  unfold R.v52741, N.v52741.
  rewrite ?node_13130.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52742 (s : N.State) (i : N.Inputs) :
  R.v52742 (state s) (inputs i) = Zmod.unsigned (N.v52742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52742 s i)) at 1.
  unfold R.v52742, N.v52742.
  unfold R.v6, N.v6.
  rewrite ?node_13110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52743 (s : N.State) (i : N.Inputs) :
  R.v52743 (state s) (inputs i) = Zmod.unsigned (N.v52743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52743 s i)) at 1.
  unfold R.v52743, N.v52743.
  unfold R.v6, N.v6.
  rewrite ?node_13086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52744 (s : N.State) (i : N.Inputs) :
  R.v52744 (state s) (inputs i) = Zmod.unsigned (N.v52744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52744 s i)) at 1.
  unfold R.v52744, N.v52744.
  rewrite ?node_52742.
  rewrite ?node_52743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52745 (s : N.State) (i : N.Inputs) :
  R.v52745 (state s) (inputs i) = Zmod.unsigned (N.v52745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52745 s i)) at 1.
  unfold R.v52745, N.v52745.
  unfold R.v16484, N.v16484.
  rewrite ?node_52744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52746 (s : N.State) (i : N.Inputs) :
  R.v52746 (state s) (inputs i) = Zmod.unsigned (N.v52746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52746 s i)) at 1.
  unfold R.v52746, N.v52746.
  rewrite ?node_52741.
  rewrite ?node_52745.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52747 (s : N.State) (i : N.Inputs) :
  R.v52747 (state s) (inputs i) = Zmod.unsigned (N.v52747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52747 s i)) at 1.
  unfold R.v52747, N.v52747.
  unfold R.v6, N.v6.
  rewrite ?node_52746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52748 (s : N.State) (i : N.Inputs) :
  R.v52748 (state s) (inputs i) = Zmod.unsigned (N.v52748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52748 s i)) at 1.
  unfold R.v52748, N.v52748.
  rewrite ?node_13131.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52749 (s : N.State) (i : N.Inputs) :
  R.v52749 (state s) (inputs i) = Zmod.unsigned (N.v52749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52749 s i)) at 1.
  unfold R.v52749, N.v52749.
  unfold R.v6, N.v6.
  rewrite ?node_13265.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52750 (s : N.State) (i : N.Inputs) :
  R.v52750 (state s) (inputs i) = Zmod.unsigned (N.v52750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52750 s i)) at 1.
  unfold R.v52750, N.v52750.
  rewrite ?node_52748.
  rewrite ?node_52749.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52751 (s : N.State) (i : N.Inputs) :
  R.v52751 (state s) (inputs i) = Zmod.unsigned (N.v52751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52751 s i)) at 1.
  unfold R.v52751, N.v52751.
  rewrite ?node_52747.
  rewrite ?node_52750.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52752 (s : N.State) (i : N.Inputs) :
  R.v52752 (state s) (inputs i) = Zmod.unsigned (N.v52752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52752 s i)) at 1.
  unfold R.v52752, N.v52752.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52753 (s : N.State) (i : N.Inputs) :
  R.v52753 (state s) (inputs i) = Zmod.unsigned (N.v52753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52753 s i)) at 1.
  unfold R.v52753, N.v52753.
  rewrite ?node_13138.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52754 (s : N.State) (i : N.Inputs) :
  R.v52754 (state s) (inputs i) = Zmod.unsigned (N.v52754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52754 s i)) at 1.
  unfold R.v52754, N.v52754.
  unfold R.v6, N.v6.
  rewrite ?node_13134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52755 (s : N.State) (i : N.Inputs) :
  R.v52755 (state s) (inputs i) = Zmod.unsigned (N.v52755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52755 s i)) at 1.
  unfold R.v52755, N.v52755.
  unfold R.v6, N.v6.
  rewrite ?node_13131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52756 (s : N.State) (i : N.Inputs) :
  R.v52756 (state s) (inputs i) = Zmod.unsigned (N.v52756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52756 s i)) at 1.
  unfold R.v52756, N.v52756.
  rewrite ?node_52754.
  rewrite ?node_52755.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52757 (s : N.State) (i : N.Inputs) :
  R.v52757 (state s) (inputs i) = Zmod.unsigned (N.v52757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52757 s i)) at 1.
  unfold R.v52757, N.v52757.
  unfold R.v16484, N.v16484.
  rewrite ?node_52756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52758 (s : N.State) (i : N.Inputs) :
  R.v52758 (state s) (inputs i) = Zmod.unsigned (N.v52758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52758 s i)) at 1.
  unfold R.v52758, N.v52758.
  rewrite ?node_52753.
  rewrite ?node_52757.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52759 (s : N.State) (i : N.Inputs) :
  R.v52759 (state s) (inputs i) = Zmod.unsigned (N.v52759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52759 s i)) at 1.
  unfold R.v52759, N.v52759.
  unfold R.v6, N.v6.
  rewrite ?node_52758.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52760 (s : N.State) (i : N.Inputs) :
  R.v52760 (state s) (inputs i) = Zmod.unsigned (N.v52760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52760 s i)) at 1.
  unfold R.v52760, N.v52760.
  rewrite ?node_13139.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52761 (s : N.State) (i : N.Inputs) :
  R.v52761 (state s) (inputs i) = Zmod.unsigned (N.v52761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52761 s i)) at 1.
  unfold R.v52761, N.v52761.
  unfold R.v6, N.v6.
  rewrite ?node_13281.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52762 (s : N.State) (i : N.Inputs) :
  R.v52762 (state s) (inputs i) = Zmod.unsigned (N.v52762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52762 s i)) at 1.
  unfold R.v52762, N.v52762.
  rewrite ?node_52760.
  rewrite ?node_52761.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52763 (s : N.State) (i : N.Inputs) :
  R.v52763 (state s) (inputs i) = Zmod.unsigned (N.v52763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52763 s i)) at 1.
  unfold R.v52763, N.v52763.
  rewrite ?node_52759.
  rewrite ?node_52762.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52764 (s : N.State) (i : N.Inputs) :
  R.v52764 (state s) (inputs i) = Zmod.unsigned (N.v52764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52764 s i)) at 1.
  unfold R.v52764, N.v52764.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52765 (s : N.State) (i : N.Inputs) :
  R.v52765 (state s) (inputs i) = Zmod.unsigned (N.v52765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52765 s i)) at 1.
  unfold R.v52765, N.v52765.
  rewrite ?node_13155.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52766 (s : N.State) (i : N.Inputs) :
  R.v52766 (state s) (inputs i) = Zmod.unsigned (N.v52766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52766 s i)) at 1.
  unfold R.v52766, N.v52766.
  rewrite ?node_13151.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52767 (s : N.State) (i : N.Inputs) :
  R.v52767 (state s) (inputs i) = Zmod.unsigned (N.v52767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52767 s i)) at 1.
  unfold R.v52767, N.v52767.
  rewrite ?node_13149.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52768 (s : N.State) (i : N.Inputs) :
  R.v52768 (state s) (inputs i) = Zmod.unsigned (N.v52768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52768 s i)) at 1.
  unfold R.v52768, N.v52768.
  unfold R.v6, N.v6.
  rewrite ?node_13145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52769 (s : N.State) (i : N.Inputs) :
  R.v52769 (state s) (inputs i) = Zmod.unsigned (N.v52769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52769 s i)) at 1.
  unfold R.v52769, N.v52769.
  unfold R.v6, N.v6.
  rewrite ?node_13142.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52770 (s : N.State) (i : N.Inputs) :
  R.v52770 (state s) (inputs i) = Zmod.unsigned (N.v52770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52770 s i)) at 1.
  unfold R.v52770, N.v52770.
  rewrite ?node_52768.
  rewrite ?node_52769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52771 (s : N.State) (i : N.Inputs) :
  R.v52771 (state s) (inputs i) = Zmod.unsigned (N.v52771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52771 s i)) at 1.
  unfold R.v52771, N.v52771.
  unfold R.v16484, N.v16484.
  rewrite ?node_52770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52772 (s : N.State) (i : N.Inputs) :
  R.v52772 (state s) (inputs i) = Zmod.unsigned (N.v52772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52772 s i)) at 1.
  unfold R.v52772, N.v52772.
  rewrite ?node_52765.
  rewrite ?node_52766.
  rewrite ?node_52767.
  rewrite ?node_52771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52773 (s : N.State) (i : N.Inputs) :
  R.v52773 (state s) (inputs i) = Zmod.unsigned (N.v52773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52773 s i)) at 1.
  unfold R.v52773, N.v52773.
  unfold R.v6, N.v6.
  rewrite ?node_52772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52774 (s : N.State) (i : N.Inputs) :
  R.v52774 (state s) (inputs i) = Zmod.unsigned (N.v52774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52774 s i)) at 1.
  unfold R.v52774, N.v52774.
  rewrite ?node_13156.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52775 (s : N.State) (i : N.Inputs) :
  R.v52775 (state s) (inputs i) = Zmod.unsigned (N.v52775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52775 s i)) at 1.
  unfold R.v52775, N.v52775.
  unfold R.v6, N.v6.
  rewrite ?node_13277.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52776 (s : N.State) (i : N.Inputs) :
  R.v52776 (state s) (inputs i) = Zmod.unsigned (N.v52776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52776 s i)) at 1.
  unfold R.v52776, N.v52776.
  unfold R.v6, N.v6.
  rewrite ?node_13289.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52777 (s : N.State) (i : N.Inputs) :
  R.v52777 (state s) (inputs i) = Zmod.unsigned (N.v52777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52777 s i)) at 1.
  unfold R.v52777, N.v52777.
  rewrite ?node_52774.
  rewrite ?node_52775.
  rewrite ?node_52776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52778 (s : N.State) (i : N.Inputs) :
  R.v52778 (state s) (inputs i) = Zmod.unsigned (N.v52778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52778 s i)) at 1.
  unfold R.v52778, N.v52778.
  rewrite ?node_52773.
  rewrite ?node_52777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52779 (s : N.State) (i : N.Inputs) :
  R.v52779 (state s) (inputs i) = Zmod.unsigned (N.v52779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52779 s i)) at 1.
  unfold R.v52779, N.v52779.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52780 (s : N.State) (i : N.Inputs) :
  R.v52780 (state s) (inputs i) = Zmod.unsigned (N.v52780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52780 s i)) at 1.
  unfold R.v52780, N.v52780.
  rewrite ?node_13149.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52781 (s : N.State) (i : N.Inputs) :
  R.v52781 (state s) (inputs i) = Zmod.unsigned (N.v52781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52781 s i)) at 1.
  unfold R.v52781, N.v52781.
  unfold R.v6, N.v6.
  rewrite ?node_13145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52782 (s : N.State) (i : N.Inputs) :
  R.v52782 (state s) (inputs i) = Zmod.unsigned (N.v52782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52782 s i)) at 1.
  unfold R.v52782, N.v52782.
  unfold R.v6, N.v6.
  rewrite ?node_13142.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52783 (s : N.State) (i : N.Inputs) :
  R.v52783 (state s) (inputs i) = Zmod.unsigned (N.v52783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52783 s i)) at 1.
  unfold R.v52783, N.v52783.
  rewrite ?node_52781.
  rewrite ?node_52782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52784 (s : N.State) (i : N.Inputs) :
  R.v52784 (state s) (inputs i) = Zmod.unsigned (N.v52784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52784 s i)) at 1.
  unfold R.v52784, N.v52784.
  unfold R.v16484, N.v16484.
  rewrite ?node_52783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52785 (s : N.State) (i : N.Inputs) :
  R.v52785 (state s) (inputs i) = Zmod.unsigned (N.v52785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52785 s i)) at 1.
  unfold R.v52785, N.v52785.
  rewrite ?node_52780.
  rewrite ?node_52784.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52786 (s : N.State) (i : N.Inputs) :
  R.v52786 (state s) (inputs i) = Zmod.unsigned (N.v52786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52786 s i)) at 1.
  unfold R.v52786, N.v52786.
  unfold R.v6, N.v6.
  rewrite ?node_52785.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52787 (s : N.State) (i : N.Inputs) :
  R.v52787 (state s) (inputs i) = Zmod.unsigned (N.v52787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52787 s i)) at 1.
  unfold R.v52787, N.v52787.
  rewrite ?node_13150.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52788 (s : N.State) (i : N.Inputs) :
  R.v52788 (state s) (inputs i) = Zmod.unsigned (N.v52788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52788 s i)) at 1.
  unfold R.v52788, N.v52788.
  unfold R.v6, N.v6.
  rewrite ?node_13277.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52789 (s : N.State) (i : N.Inputs) :
  R.v52789 (state s) (inputs i) = Zmod.unsigned (N.v52789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52789 s i)) at 1.
  unfold R.v52789, N.v52789.
  rewrite ?node_52787.
  rewrite ?node_52788.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52790 (s : N.State) (i : N.Inputs) :
  R.v52790 (state s) (inputs i) = Zmod.unsigned (N.v52790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52790 s i)) at 1.
  unfold R.v52790, N.v52790.
  rewrite ?node_52786.
  rewrite ?node_52789.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52791 (s : N.State) (i : N.Inputs) :
  R.v52791 (state s) (inputs i) = Zmod.unsigned (N.v52791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52791 s i)) at 1.
  unfold R.v52791, N.v52791.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52792 (s : N.State) (i : N.Inputs) :
  R.v52792 (state s) (inputs i) = Zmod.unsigned (N.v52792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52792 s i)) at 1.
  unfold R.v52792, N.v52792.
  rewrite ?node_13155.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52793 (s : N.State) (i : N.Inputs) :
  R.v52793 (state s) (inputs i) = Zmod.unsigned (N.v52793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52793 s i)) at 1.
  unfold R.v52793, N.v52793.
  unfold R.v6, N.v6.
  rewrite ?node_13151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52794 (s : N.State) (i : N.Inputs) :
  R.v52794 (state s) (inputs i) = Zmod.unsigned (N.v52794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52794 s i)) at 1.
  unfold R.v52794, N.v52794.
  unfold R.v6, N.v6.
  rewrite ?node_13150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52795 (s : N.State) (i : N.Inputs) :
  R.v52795 (state s) (inputs i) = Zmod.unsigned (N.v52795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52795 s i)) at 1.
  unfold R.v52795, N.v52795.
  rewrite ?node_52793.
  rewrite ?node_52794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52796 (s : N.State) (i : N.Inputs) :
  R.v52796 (state s) (inputs i) = Zmod.unsigned (N.v52796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52796 s i)) at 1.
  unfold R.v52796, N.v52796.
  unfold R.v16484, N.v16484.
  rewrite ?node_52795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52797 (s : N.State) (i : N.Inputs) :
  R.v52797 (state s) (inputs i) = Zmod.unsigned (N.v52797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52797 s i)) at 1.
  unfold R.v52797, N.v52797.
  rewrite ?node_52792.
  rewrite ?node_52796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52798 (s : N.State) (i : N.Inputs) :
  R.v52798 (state s) (inputs i) = Zmod.unsigned (N.v52798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52798 s i)) at 1.
  unfold R.v52798, N.v52798.
  unfold R.v6, N.v6.
  rewrite ?node_52797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52799 (s : N.State) (i : N.Inputs) :
  R.v52799 (state s) (inputs i) = Zmod.unsigned (N.v52799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52799 s i)) at 1.
  unfold R.v52799, N.v52799.
  rewrite ?node_13156.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52800 (s : N.State) (i : N.Inputs) :
  R.v52800 (state s) (inputs i) = Zmod.unsigned (N.v52800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52800 s i)) at 1.
  unfold R.v52800, N.v52800.
  unfold R.v6, N.v6.
  rewrite ?node_13289.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52801 (s : N.State) (i : N.Inputs) :
  R.v52801 (state s) (inputs i) = Zmod.unsigned (N.v52801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52801 s i)) at 1.
  unfold R.v52801, N.v52801.
  rewrite ?node_52799.
  rewrite ?node_52800.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52802 (s : N.State) (i : N.Inputs) :
  R.v52802 (state s) (inputs i) = Zmod.unsigned (N.v52802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52802 s i)) at 1.
  unfold R.v52802, N.v52802.
  rewrite ?node_52798.
  rewrite ?node_52801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52803 (s : N.State) (i : N.Inputs) :
  R.v52803 (state s) (inputs i) = Zmod.unsigned (N.v52803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52803 s i)) at 1.
  unfold R.v52803, N.v52803.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52804 (s : N.State) (i : N.Inputs) :
  R.v52804 (state s) (inputs i) = Zmod.unsigned (N.v52804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52804 s i)) at 1.
  unfold R.v52804, N.v52804.
  rewrite ?node_13265.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52805 (s : N.State) (i : N.Inputs) :
  R.v52805 (state s) (inputs i) = Zmod.unsigned (N.v52805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52805 s i)) at 1.
  unfold R.v52805, N.v52805.
  rewrite ?node_13261.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52806 (s : N.State) (i : N.Inputs) :
  R.v52806 (state s) (inputs i) = Zmod.unsigned (N.v52806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52806 s i)) at 1.
  unfold R.v52806, N.v52806.
  rewrite ?node_13257.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52807 (s : N.State) (i : N.Inputs) :
  R.v52807 (state s) (inputs i) = Zmod.unsigned (N.v52807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52807 s i)) at 1.
  unfold R.v52807, N.v52807.
  unfold R.v6, N.v6.
  rewrite ?node_13237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52808 (s : N.State) (i : N.Inputs) :
  R.v52808 (state s) (inputs i) = Zmod.unsigned (N.v52808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52808 s i)) at 1.
  unfold R.v52808, N.v52808.
  unfold R.v6, N.v6.
  rewrite ?node_13210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52809 (s : N.State) (i : N.Inputs) :
  R.v52809 (state s) (inputs i) = Zmod.unsigned (N.v52809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52809 s i)) at 1.
  unfold R.v52809, N.v52809.
  rewrite ?node_52807.
  rewrite ?node_52808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52810 (s : N.State) (i : N.Inputs) :
  R.v52810 (state s) (inputs i) = Zmod.unsigned (N.v52810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52810 s i)) at 1.
  unfold R.v52810, N.v52810.
  unfold R.v16484, N.v16484.
  rewrite ?node_52809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52811 (s : N.State) (i : N.Inputs) :
  R.v52811 (state s) (inputs i) = Zmod.unsigned (N.v52811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52811 s i)) at 1.
  unfold R.v52811, N.v52811.
  rewrite ?node_52804.
  rewrite ?node_52805.
  rewrite ?node_52806.
  rewrite ?node_52810.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52812 (s : N.State) (i : N.Inputs) :
  R.v52812 (state s) (inputs i) = Zmod.unsigned (N.v52812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52812 s i)) at 1.
  unfold R.v52812, N.v52812.
  unfold R.v6, N.v6.
  rewrite ?node_52811.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52813 (s : N.State) (i : N.Inputs) :
  R.v52813 (state s) (inputs i) = Zmod.unsigned (N.v52813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52813 s i)) at 1.
  unfold R.v52813, N.v52813.
  rewrite ?node_13266.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52814 (s : N.State) (i : N.Inputs) :
  R.v52814 (state s) (inputs i) = Zmod.unsigned (N.v52814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52814 s i)) at 1.
  unfold R.v52814, N.v52814.
  unfold R.v6, N.v6.
  rewrite ?node_13387.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52815 (s : N.State) (i : N.Inputs) :
  R.v52815 (state s) (inputs i) = Zmod.unsigned (N.v52815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52815 s i)) at 1.
  unfold R.v52815, N.v52815.
  unfold R.v6, N.v6.
  rewrite ?node_13399.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52816 (s : N.State) (i : N.Inputs) :
  R.v52816 (state s) (inputs i) = Zmod.unsigned (N.v52816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52816 s i)) at 1.
  unfold R.v52816, N.v52816.
  rewrite ?node_52813.
  rewrite ?node_52814.
  rewrite ?node_52815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52817 (s : N.State) (i : N.Inputs) :
  R.v52817 (state s) (inputs i) = Zmod.unsigned (N.v52817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52817 s i)) at 1.
  unfold R.v52817, N.v52817.
  rewrite ?node_52812.
  rewrite ?node_52816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52818 (s : N.State) (i : N.Inputs) :
  R.v52818 (state s) (inputs i) = Zmod.unsigned (N.v52818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52818 s i)) at 1.
  unfold R.v52818, N.v52818.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52819 (s : N.State) (i : N.Inputs) :
  R.v52819 (state s) (inputs i) = Zmod.unsigned (N.v52819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52819 s i)) at 1.
  unfold R.v52819, N.v52819.
  rewrite ?node_13257.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52820 (s : N.State) (i : N.Inputs) :
  R.v52820 (state s) (inputs i) = Zmod.unsigned (N.v52820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52820 s i)) at 1.
  unfold R.v52820, N.v52820.
  unfold R.v6, N.v6.
  rewrite ?node_13237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52821 (s : N.State) (i : N.Inputs) :
  R.v52821 (state s) (inputs i) = Zmod.unsigned (N.v52821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52821 s i)) at 1.
  unfold R.v52821, N.v52821.
  unfold R.v6, N.v6.
  rewrite ?node_13210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52822 (s : N.State) (i : N.Inputs) :
  R.v52822 (state s) (inputs i) = Zmod.unsigned (N.v52822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52822 s i)) at 1.
  unfold R.v52822, N.v52822.
  rewrite ?node_52820.
  rewrite ?node_52821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52823 (s : N.State) (i : N.Inputs) :
  R.v52823 (state s) (inputs i) = Zmod.unsigned (N.v52823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52823 s i)) at 1.
  unfold R.v52823, N.v52823.
  unfold R.v16484, N.v16484.
  rewrite ?node_52822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52824 (s : N.State) (i : N.Inputs) :
  R.v52824 (state s) (inputs i) = Zmod.unsigned (N.v52824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52824 s i)) at 1.
  unfold R.v52824, N.v52824.
  rewrite ?node_52819.
  rewrite ?node_52823.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52825 (s : N.State) (i : N.Inputs) :
  R.v52825 (state s) (inputs i) = Zmod.unsigned (N.v52825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52825 s i)) at 1.
  unfold R.v52825, N.v52825.
  unfold R.v6, N.v6.
  rewrite ?node_52824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52826 (s : N.State) (i : N.Inputs) :
  R.v52826 (state s) (inputs i) = Zmod.unsigned (N.v52826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52826 s i)) at 1.
  unfold R.v52826, N.v52826.
  rewrite ?node_13258.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52827 (s : N.State) (i : N.Inputs) :
  R.v52827 (state s) (inputs i) = Zmod.unsigned (N.v52827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52827 s i)) at 1.
  unfold R.v52827, N.v52827.
  unfold R.v6, N.v6.
  rewrite ?node_13387.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52828 (s : N.State) (i : N.Inputs) :
  R.v52828 (state s) (inputs i) = Zmod.unsigned (N.v52828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52828 s i)) at 1.
  unfold R.v52828, N.v52828.
  rewrite ?node_52826.
  rewrite ?node_52827.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52829 (s : N.State) (i : N.Inputs) :
  R.v52829 (state s) (inputs i) = Zmod.unsigned (N.v52829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52829 s i)) at 1.
  unfold R.v52829, N.v52829.
  rewrite ?node_52825.
  rewrite ?node_52828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52830 (s : N.State) (i : N.Inputs) :
  R.v52830 (state s) (inputs i) = Zmod.unsigned (N.v52830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52830 s i)) at 1.
  unfold R.v52830, N.v52830.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52831 (s : N.State) (i : N.Inputs) :
  R.v52831 (state s) (inputs i) = Zmod.unsigned (N.v52831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52831 s i)) at 1.
  unfold R.v52831, N.v52831.
  rewrite ?node_13265.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52832 (s : N.State) (i : N.Inputs) :
  R.v52832 (state s) (inputs i) = Zmod.unsigned (N.v52832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52832 s i)) at 1.
  unfold R.v52832, N.v52832.
  unfold R.v6, N.v6.
  rewrite ?node_13261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52833 (s : N.State) (i : N.Inputs) :
  R.v52833 (state s) (inputs i) = Zmod.unsigned (N.v52833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52833 s i)) at 1.
  unfold R.v52833, N.v52833.
  unfold R.v6, N.v6.
  rewrite ?node_13258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52834 (s : N.State) (i : N.Inputs) :
  R.v52834 (state s) (inputs i) = Zmod.unsigned (N.v52834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52834 s i)) at 1.
  unfold R.v52834, N.v52834.
  rewrite ?node_52832.
  rewrite ?node_52833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52835 (s : N.State) (i : N.Inputs) :
  R.v52835 (state s) (inputs i) = Zmod.unsigned (N.v52835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52835 s i)) at 1.
  unfold R.v52835, N.v52835.
  unfold R.v16484, N.v16484.
  rewrite ?node_52834.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52836 (s : N.State) (i : N.Inputs) :
  R.v52836 (state s) (inputs i) = Zmod.unsigned (N.v52836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52836 s i)) at 1.
  unfold R.v52836, N.v52836.
  rewrite ?node_52831.
  rewrite ?node_52835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52837 (s : N.State) (i : N.Inputs) :
  R.v52837 (state s) (inputs i) = Zmod.unsigned (N.v52837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52837 s i)) at 1.
  unfold R.v52837, N.v52837.
  unfold R.v6, N.v6.
  rewrite ?node_52836.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52838 (s : N.State) (i : N.Inputs) :
  R.v52838 (state s) (inputs i) = Zmod.unsigned (N.v52838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52838 s i)) at 1.
  unfold R.v52838, N.v52838.
  rewrite ?node_13266.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52839 (s : N.State) (i : N.Inputs) :
  R.v52839 (state s) (inputs i) = Zmod.unsigned (N.v52839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52839 s i)) at 1.
  unfold R.v52839, N.v52839.
  unfold R.v6, N.v6.
  rewrite ?node_13399.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52840 (s : N.State) (i : N.Inputs) :
  R.v52840 (state s) (inputs i) = Zmod.unsigned (N.v52840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52840 s i)) at 1.
  unfold R.v52840, N.v52840.
  rewrite ?node_52838.
  rewrite ?node_52839.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52841 (s : N.State) (i : N.Inputs) :
  R.v52841 (state s) (inputs i) = Zmod.unsigned (N.v52841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52841 s i)) at 1.
  unfold R.v52841, N.v52841.
  rewrite ?node_52837.
  rewrite ?node_52840.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52842 (s : N.State) (i : N.Inputs) :
  R.v52842 (state s) (inputs i) = Zmod.unsigned (N.v52842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52842 s i)) at 1.
  unfold R.v52842, N.v52842.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52843 (s : N.State) (i : N.Inputs) :
  R.v52843 (state s) (inputs i) = Zmod.unsigned (N.v52843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52843 s i)) at 1.
  unfold R.v52843, N.v52843.
  unfold R.v6, N.v6.
  rewrite ?node_13272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52844 (s : N.State) (i : N.Inputs) :
  R.v52844 (state s) (inputs i) = Zmod.unsigned (N.v52844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52844 s i)) at 1.
  unfold R.v52844, N.v52844.
  unfold R.v6, N.v6.
  rewrite ?node_13269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52845 (s : N.State) (i : N.Inputs) :
  R.v52845 (state s) (inputs i) = Zmod.unsigned (N.v52845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52845 s i)) at 1.
  unfold R.v52845, N.v52845.
  rewrite ?node_52843.
  rewrite ?node_52844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52846 (s : N.State) (i : N.Inputs) :
  R.v52846 (state s) (inputs i) = Zmod.unsigned (N.v52846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52846 s i)) at 1.
  unfold R.v52846, N.v52846.
  unfold R.v16463, N.v16463.
  rewrite ?node_52845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52847 (s : N.State) (i : N.Inputs) :
  R.v52847 (state s) (inputs i) = Zmod.unsigned (N.v52847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52847 s i)) at 1.
  unfold R.v52847, N.v52847.
  rewrite ?node_13273.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52848 (s : N.State) (i : N.Inputs) :
  R.v52848 (state s) (inputs i) = Zmod.unsigned (N.v52848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52848 s i)) at 1.
  unfold R.v52848, N.v52848.
  unfold R.v6, N.v6.
  rewrite ?node_13401.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52849 (s : N.State) (i : N.Inputs) :
  R.v52849 (state s) (inputs i) = Zmod.unsigned (N.v52849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52849 s i)) at 1.
  unfold R.v52849, N.v52849.
  rewrite ?node_52847.
  rewrite ?node_52848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52850 (s : N.State) (i : N.Inputs) :
  R.v52850 (state s) (inputs i) = Zmod.unsigned (N.v52850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52850 s i)) at 1.
  unfold R.v52850, N.v52850.
  rewrite ?node_52846.
  rewrite ?node_52849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52851 (s : N.State) (i : N.Inputs) :
  R.v52851 (state s) (inputs i) = Zmod.unsigned (N.v52851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52851 s i)) at 1.
  unfold R.v52851, N.v52851.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52852 (s : N.State) (i : N.Inputs) :
  R.v52852 (state s) (inputs i) = Zmod.unsigned (N.v52852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52852 s i)) at 1.
  unfold R.v52852, N.v52852.
  rewrite ?node_13387.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52853 (s : N.State) (i : N.Inputs) :
  R.v52853 (state s) (inputs i) = Zmod.unsigned (N.v52853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52853 s i)) at 1.
  unfold R.v52853, N.v52853.
  rewrite ?node_13383.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52854 (s : N.State) (i : N.Inputs) :
  R.v52854 (state s) (inputs i) = Zmod.unsigned (N.v52854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52854 s i)) at 1.
  unfold R.v52854, N.v52854.
  rewrite ?node_13379.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52855 (s : N.State) (i : N.Inputs) :
  R.v52855 (state s) (inputs i) = Zmod.unsigned (N.v52855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52855 s i)) at 1.
  unfold R.v52855, N.v52855.
  unfold R.v6, N.v6.
  rewrite ?node_13359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52856 (s : N.State) (i : N.Inputs) :
  R.v52856 (state s) (inputs i) = Zmod.unsigned (N.v52856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52856 s i)) at 1.
  unfold R.v52856, N.v52856.
  unfold R.v6, N.v6.
  rewrite ?node_13332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52857 (s : N.State) (i : N.Inputs) :
  R.v52857 (state s) (inputs i) = Zmod.unsigned (N.v52857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52857 s i)) at 1.
  unfold R.v52857, N.v52857.
  rewrite ?node_52855.
  rewrite ?node_52856.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52858 (s : N.State) (i : N.Inputs) :
  R.v52858 (state s) (inputs i) = Zmod.unsigned (N.v52858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52858 s i)) at 1.
  unfold R.v52858, N.v52858.
  unfold R.v16484, N.v16484.
  rewrite ?node_52857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52859 (s : N.State) (i : N.Inputs) :
  R.v52859 (state s) (inputs i) = Zmod.unsigned (N.v52859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52859 s i)) at 1.
  unfold R.v52859, N.v52859.
  rewrite ?node_52852.
  rewrite ?node_52853.
  rewrite ?node_52854.
  rewrite ?node_52858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52860 (s : N.State) (i : N.Inputs) :
  R.v52860 (state s) (inputs i) = Zmod.unsigned (N.v52860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52860 s i)) at 1.
  unfold R.v52860, N.v52860.
  unfold R.v6, N.v6.
  rewrite ?node_52859.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52861 (s : N.State) (i : N.Inputs) :
  R.v52861 (state s) (inputs i) = Zmod.unsigned (N.v52861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52861 s i)) at 1.
  unfold R.v52861, N.v52861.
  rewrite ?node_13388.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52862 (s : N.State) (i : N.Inputs) :
  R.v52862 (state s) (inputs i) = Zmod.unsigned (N.v52862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52862 s i)) at 1.
  unfold R.v52862, N.v52862.
  unfold R.v6, N.v6.
  rewrite ?node_13499.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52863 (s : N.State) (i : N.Inputs) :
  R.v52863 (state s) (inputs i) = Zmod.unsigned (N.v52863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52863 s i)) at 1.
  unfold R.v52863, N.v52863.
  unfold R.v6, N.v6.
  rewrite ?node_13515.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52864 (s : N.State) (i : N.Inputs) :
  R.v52864 (state s) (inputs i) = Zmod.unsigned (N.v52864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52864 s i)) at 1.
  unfold R.v52864, N.v52864.
  rewrite ?node_52861.
  rewrite ?node_52862.
  rewrite ?node_52863.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52865 (s : N.State) (i : N.Inputs) :
  R.v52865 (state s) (inputs i) = Zmod.unsigned (N.v52865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52865 s i)) at 1.
  unfold R.v52865, N.v52865.
  rewrite ?node_52860.
  rewrite ?node_52864.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52866 (s : N.State) (i : N.Inputs) :
  R.v52866 (state s) (inputs i) = Zmod.unsigned (N.v52866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52866 s i)) at 1.
  unfold R.v52866, N.v52866.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52867 (s : N.State) (i : N.Inputs) :
  R.v52867 (state s) (inputs i) = Zmod.unsigned (N.v52867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52867 s i)) at 1.
  unfold R.v52867, N.v52867.
  rewrite ?node_13379.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52868 (s : N.State) (i : N.Inputs) :
  R.v52868 (state s) (inputs i) = Zmod.unsigned (N.v52868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52868 s i)) at 1.
  unfold R.v52868, N.v52868.
  unfold R.v6, N.v6.
  rewrite ?node_13359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52869 (s : N.State) (i : N.Inputs) :
  R.v52869 (state s) (inputs i) = Zmod.unsigned (N.v52869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52869 s i)) at 1.
  unfold R.v52869, N.v52869.
  unfold R.v6, N.v6.
  rewrite ?node_13332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52870 (s : N.State) (i : N.Inputs) :
  R.v52870 (state s) (inputs i) = Zmod.unsigned (N.v52870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52870 s i)) at 1.
  unfold R.v52870, N.v52870.
  rewrite ?node_52868.
  rewrite ?node_52869.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52871 (s : N.State) (i : N.Inputs) :
  R.v52871 (state s) (inputs i) = Zmod.unsigned (N.v52871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52871 s i)) at 1.
  unfold R.v52871, N.v52871.
  unfold R.v16484, N.v16484.
  rewrite ?node_52870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52872 (s : N.State) (i : N.Inputs) :
  R.v52872 (state s) (inputs i) = Zmod.unsigned (N.v52872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52872 s i)) at 1.
  unfold R.v52872, N.v52872.
  rewrite ?node_52867.
  rewrite ?node_52871.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52873 (s : N.State) (i : N.Inputs) :
  R.v52873 (state s) (inputs i) = Zmod.unsigned (N.v52873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52873 s i)) at 1.
  unfold R.v52873, N.v52873.
  unfold R.v6, N.v6.
  rewrite ?node_52872.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52874 (s : N.State) (i : N.Inputs) :
  R.v52874 (state s) (inputs i) = Zmod.unsigned (N.v52874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52874 s i)) at 1.
  unfold R.v52874, N.v52874.
  rewrite ?node_13380.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52875 (s : N.State) (i : N.Inputs) :
  R.v52875 (state s) (inputs i) = Zmod.unsigned (N.v52875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52875 s i)) at 1.
  unfold R.v52875, N.v52875.
  unfold R.v6, N.v6.
  rewrite ?node_13499.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52876 (s : N.State) (i : N.Inputs) :
  R.v52876 (state s) (inputs i) = Zmod.unsigned (N.v52876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52876 s i)) at 1.
  unfold R.v52876, N.v52876.
  rewrite ?node_52874.
  rewrite ?node_52875.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52877 (s : N.State) (i : N.Inputs) :
  R.v52877 (state s) (inputs i) = Zmod.unsigned (N.v52877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52877 s i)) at 1.
  unfold R.v52877, N.v52877.
  rewrite ?node_52873.
  rewrite ?node_52876.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52878 (s : N.State) (i : N.Inputs) :
  R.v52878 (state s) (inputs i) = Zmod.unsigned (N.v52878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52878 s i)) at 1.
  unfold R.v52878, N.v52878.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52879 (s : N.State) (i : N.Inputs) :
  R.v52879 (state s) (inputs i) = Zmod.unsigned (N.v52879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52879 s i)) at 1.
  unfold R.v52879, N.v52879.
  rewrite ?node_13387.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52880 (s : N.State) (i : N.Inputs) :
  R.v52880 (state s) (inputs i) = Zmod.unsigned (N.v52880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52880 s i)) at 1.
  unfold R.v52880, N.v52880.
  unfold R.v6, N.v6.
  rewrite ?node_13383.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52881 (s : N.State) (i : N.Inputs) :
  R.v52881 (state s) (inputs i) = Zmod.unsigned (N.v52881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52881 s i)) at 1.
  unfold R.v52881, N.v52881.
  unfold R.v6, N.v6.
  rewrite ?node_13380.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52882 (s : N.State) (i : N.Inputs) :
  R.v52882 (state s) (inputs i) = Zmod.unsigned (N.v52882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52882 s i)) at 1.
  unfold R.v52882, N.v52882.
  rewrite ?node_52880.
  rewrite ?node_52881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52883 (s : N.State) (i : N.Inputs) :
  R.v52883 (state s) (inputs i) = Zmod.unsigned (N.v52883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52883 s i)) at 1.
  unfold R.v52883, N.v52883.
  unfold R.v16484, N.v16484.
  rewrite ?node_52882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52884 (s : N.State) (i : N.Inputs) :
  R.v52884 (state s) (inputs i) = Zmod.unsigned (N.v52884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52884 s i)) at 1.
  unfold R.v52884, N.v52884.
  rewrite ?node_52879.
  rewrite ?node_52883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52885 (s : N.State) (i : N.Inputs) :
  R.v52885 (state s) (inputs i) = Zmod.unsigned (N.v52885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52885 s i)) at 1.
  unfold R.v52885, N.v52885.
  unfold R.v6, N.v6.
  rewrite ?node_52884.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52886 (s : N.State) (i : N.Inputs) :
  R.v52886 (state s) (inputs i) = Zmod.unsigned (N.v52886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52886 s i)) at 1.
  unfold R.v52886, N.v52886.
  rewrite ?node_13388.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52887 (s : N.State) (i : N.Inputs) :
  R.v52887 (state s) (inputs i) = Zmod.unsigned (N.v52887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52887 s i)) at 1.
  unfold R.v52887, N.v52887.
  unfold R.v6, N.v6.
  rewrite ?node_13515.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52888 (s : N.State) (i : N.Inputs) :
  R.v52888 (state s) (inputs i) = Zmod.unsigned (N.v52888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52888 s i)) at 1.
  unfold R.v52888, N.v52888.
  rewrite ?node_52886.
  rewrite ?node_52887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52889 (s : N.State) (i : N.Inputs) :
  R.v52889 (state s) (inputs i) = Zmod.unsigned (N.v52889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52889 s i)) at 1.
  unfold R.v52889, N.v52889.
  rewrite ?node_52885.
  rewrite ?node_52888.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52890 (s : N.State) (i : N.Inputs) :
  R.v52890 (state s) (inputs i) = Zmod.unsigned (N.v52890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52890 s i)) at 1.
  unfold R.v52890, N.v52890.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52891 (s : N.State) (i : N.Inputs) :
  R.v52891 (state s) (inputs i) = Zmod.unsigned (N.v52891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52891 s i)) at 1.
  unfold R.v52891, N.v52891.
  unfold R.v6, N.v6.
  rewrite ?node_13394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52892 (s : N.State) (i : N.Inputs) :
  R.v52892 (state s) (inputs i) = Zmod.unsigned (N.v52892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52892 s i)) at 1.
  unfold R.v52892, N.v52892.
  unfold R.v6, N.v6.
  rewrite ?node_13391.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52893 (s : N.State) (i : N.Inputs) :
  R.v52893 (state s) (inputs i) = Zmod.unsigned (N.v52893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52893 s i)) at 1.
  unfold R.v52893, N.v52893.
  rewrite ?node_52891.
  rewrite ?node_52892.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52894 (s : N.State) (i : N.Inputs) :
  R.v52894 (state s) (inputs i) = Zmod.unsigned (N.v52894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52894 s i)) at 1.
  unfold R.v52894, N.v52894.
  unfold R.v16463, N.v16463.
  rewrite ?node_52893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52895 (s : N.State) (i : N.Inputs) :
  R.v52895 (state s) (inputs i) = Zmod.unsigned (N.v52895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52895 s i)) at 1.
  unfold R.v52895, N.v52895.
  rewrite ?node_13395.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52896 (s : N.State) (i : N.Inputs) :
  R.v52896 (state s) (inputs i) = Zmod.unsigned (N.v52896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52896 s i)) at 1.
  unfold R.v52896, N.v52896.
  unfold R.v6, N.v6.
  rewrite ?node_13517.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52897 (s : N.State) (i : N.Inputs) :
  R.v52897 (state s) (inputs i) = Zmod.unsigned (N.v52897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52897 s i)) at 1.
  unfold R.v52897, N.v52897.
  rewrite ?node_52895.
  rewrite ?node_52896.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52898 (s : N.State) (i : N.Inputs) :
  R.v52898 (state s) (inputs i) = Zmod.unsigned (N.v52898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52898 s i)) at 1.
  unfold R.v52898, N.v52898.
  rewrite ?node_52894.
  rewrite ?node_52897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52899 (s : N.State) (i : N.Inputs) :
  R.v52899 (state s) (inputs i) = Zmod.unsigned (N.v52899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52899 s i)) at 1.
  unfold R.v52899, N.v52899.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52900 (s : N.State) (i : N.Inputs) :
  R.v52900 (state s) (inputs i) = Zmod.unsigned (N.v52900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52900 s i)) at 1.
  unfold R.v52900, N.v52900.
  rewrite ?node_13499.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52901 (s : N.State) (i : N.Inputs) :
  R.v52901 (state s) (inputs i) = Zmod.unsigned (N.v52901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52901 s i)) at 1.
  unfold R.v52901, N.v52901.
  rewrite ?node_13495.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52902 (s : N.State) (i : N.Inputs) :
  R.v52902 (state s) (inputs i) = Zmod.unsigned (N.v52902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52902 s i)) at 1.
  unfold R.v52902, N.v52902.
  rewrite ?node_13491.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52903 (s : N.State) (i : N.Inputs) :
  R.v52903 (state s) (inputs i) = Zmod.unsigned (N.v52903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52903 s i)) at 1.
  unfold R.v52903, N.v52903.
  unfold R.v6, N.v6.
  rewrite ?node_13471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52904 (s : N.State) (i : N.Inputs) :
  R.v52904 (state s) (inputs i) = Zmod.unsigned (N.v52904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52904 s i)) at 1.
  unfold R.v52904, N.v52904.
  unfold R.v6, N.v6.
  rewrite ?node_13449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52905 (s : N.State) (i : N.Inputs) :
  R.v52905 (state s) (inputs i) = Zmod.unsigned (N.v52905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52905 s i)) at 1.
  unfold R.v52905, N.v52905.
  rewrite ?node_52903.
  rewrite ?node_52904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52906 (s : N.State) (i : N.Inputs) :
  R.v52906 (state s) (inputs i) = Zmod.unsigned (N.v52906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52906 s i)) at 1.
  unfold R.v52906, N.v52906.
  unfold R.v16484, N.v16484.
  rewrite ?node_52905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52907 (s : N.State) (i : N.Inputs) :
  R.v52907 (state s) (inputs i) = Zmod.unsigned (N.v52907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52907 s i)) at 1.
  unfold R.v52907, N.v52907.
  rewrite ?node_52900.
  rewrite ?node_52901.
  rewrite ?node_52902.
  rewrite ?node_52906.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52908 (s : N.State) (i : N.Inputs) :
  R.v52908 (state s) (inputs i) = Zmod.unsigned (N.v52908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52908 s i)) at 1.
  unfold R.v52908, N.v52908.
  unfold R.v6, N.v6.
  rewrite ?node_52907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52909 (s : N.State) (i : N.Inputs) :
  R.v52909 (state s) (inputs i) = Zmod.unsigned (N.v52909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52909 s i)) at 1.
  unfold R.v52909, N.v52909.
  rewrite ?node_13500.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52910 (s : N.State) (i : N.Inputs) :
  R.v52910 (state s) (inputs i) = Zmod.unsigned (N.v52910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52910 s i)) at 1.
  unfold R.v52910, N.v52910.
  unfold R.v6, N.v6.
  rewrite ?node_13614.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52911 (s : N.State) (i : N.Inputs) :
  R.v52911 (state s) (inputs i) = Zmod.unsigned (N.v52911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52911 s i)) at 1.
  unfold R.v52911, N.v52911.
  unfold R.v6, N.v6.
  rewrite ?node_13626.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52912 (s : N.State) (i : N.Inputs) :
  R.v52912 (state s) (inputs i) = Zmod.unsigned (N.v52912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52912 s i)) at 1.
  unfold R.v52912, N.v52912.
  rewrite ?node_52909.
  rewrite ?node_52910.
  rewrite ?node_52911.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52913 (s : N.State) (i : N.Inputs) :
  R.v52913 (state s) (inputs i) = Zmod.unsigned (N.v52913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52913 s i)) at 1.
  unfold R.v52913, N.v52913.
  rewrite ?node_52908.
  rewrite ?node_52912.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52914 (s : N.State) (i : N.Inputs) :
  R.v52914 (state s) (inputs i) = Zmod.unsigned (N.v52914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52914 s i)) at 1.
  unfold R.v52914, N.v52914.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52915 (s : N.State) (i : N.Inputs) :
  R.v52915 (state s) (inputs i) = Zmod.unsigned (N.v52915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52915 s i)) at 1.
  unfold R.v52915, N.v52915.
  rewrite ?node_13491.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52916 (s : N.State) (i : N.Inputs) :
  R.v52916 (state s) (inputs i) = Zmod.unsigned (N.v52916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52916 s i)) at 1.
  unfold R.v52916, N.v52916.
  unfold R.v6, N.v6.
  rewrite ?node_13471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52917 (s : N.State) (i : N.Inputs) :
  R.v52917 (state s) (inputs i) = Zmod.unsigned (N.v52917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52917 s i)) at 1.
  unfold R.v52917, N.v52917.
  unfold R.v6, N.v6.
  rewrite ?node_13449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52918 (s : N.State) (i : N.Inputs) :
  R.v52918 (state s) (inputs i) = Zmod.unsigned (N.v52918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52918 s i)) at 1.
  unfold R.v52918, N.v52918.
  rewrite ?node_52916.
  rewrite ?node_52917.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52919 (s : N.State) (i : N.Inputs) :
  R.v52919 (state s) (inputs i) = Zmod.unsigned (N.v52919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52919 s i)) at 1.
  unfold R.v52919, N.v52919.
  unfold R.v16484, N.v16484.
  rewrite ?node_52918.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52920 (s : N.State) (i : N.Inputs) :
  R.v52920 (state s) (inputs i) = Zmod.unsigned (N.v52920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52920 s i)) at 1.
  unfold R.v52920, N.v52920.
  rewrite ?node_52915.
  rewrite ?node_52919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52921 (s : N.State) (i : N.Inputs) :
  R.v52921 (state s) (inputs i) = Zmod.unsigned (N.v52921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52921 s i)) at 1.
  unfold R.v52921, N.v52921.
  unfold R.v6, N.v6.
  rewrite ?node_52920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52922 (s : N.State) (i : N.Inputs) :
  R.v52922 (state s) (inputs i) = Zmod.unsigned (N.v52922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52922 s i)) at 1.
  unfold R.v52922, N.v52922.
  rewrite ?node_13492.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52923 (s : N.State) (i : N.Inputs) :
  R.v52923 (state s) (inputs i) = Zmod.unsigned (N.v52923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52923 s i)) at 1.
  unfold R.v52923, N.v52923.
  unfold R.v6, N.v6.
  rewrite ?node_13614.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52924 (s : N.State) (i : N.Inputs) :
  R.v52924 (state s) (inputs i) = Zmod.unsigned (N.v52924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52924 s i)) at 1.
  unfold R.v52924, N.v52924.
  rewrite ?node_52922.
  rewrite ?node_52923.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52925 (s : N.State) (i : N.Inputs) :
  R.v52925 (state s) (inputs i) = Zmod.unsigned (N.v52925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52925 s i)) at 1.
  unfold R.v52925, N.v52925.
  rewrite ?node_52921.
  rewrite ?node_52924.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52926 (s : N.State) (i : N.Inputs) :
  R.v52926 (state s) (inputs i) = Zmod.unsigned (N.v52926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52926 s i)) at 1.
  unfold R.v52926, N.v52926.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52927 (s : N.State) (i : N.Inputs) :
  R.v52927 (state s) (inputs i) = Zmod.unsigned (N.v52927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52927 s i)) at 1.
  unfold R.v52927, N.v52927.
  rewrite ?node_13499.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52928 (s : N.State) (i : N.Inputs) :
  R.v52928 (state s) (inputs i) = Zmod.unsigned (N.v52928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52928 s i)) at 1.
  unfold R.v52928, N.v52928.
  unfold R.v6, N.v6.
  rewrite ?node_13495.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52929 (s : N.State) (i : N.Inputs) :
  R.v52929 (state s) (inputs i) = Zmod.unsigned (N.v52929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52929 s i)) at 1.
  unfold R.v52929, N.v52929.
  unfold R.v6, N.v6.
  rewrite ?node_13492.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52930 (s : N.State) (i : N.Inputs) :
  R.v52930 (state s) (inputs i) = Zmod.unsigned (N.v52930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52930 s i)) at 1.
  unfold R.v52930, N.v52930.
  rewrite ?node_52928.
  rewrite ?node_52929.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52931 (s : N.State) (i : N.Inputs) :
  R.v52931 (state s) (inputs i) = Zmod.unsigned (N.v52931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52931 s i)) at 1.
  unfold R.v52931, N.v52931.
  unfold R.v16484, N.v16484.
  rewrite ?node_52930.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52932 (s : N.State) (i : N.Inputs) :
  R.v52932 (state s) (inputs i) = Zmod.unsigned (N.v52932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52932 s i)) at 1.
  unfold R.v52932, N.v52932.
  rewrite ?node_52927.
  rewrite ?node_52931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52933 (s : N.State) (i : N.Inputs) :
  R.v52933 (state s) (inputs i) = Zmod.unsigned (N.v52933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52933 s i)) at 1.
  unfold R.v52933, N.v52933.
  unfold R.v6, N.v6.
  rewrite ?node_52932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52934 (s : N.State) (i : N.Inputs) :
  R.v52934 (state s) (inputs i) = Zmod.unsigned (N.v52934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52934 s i)) at 1.
  unfold R.v52934, N.v52934.
  rewrite ?node_13500.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52935 (s : N.State) (i : N.Inputs) :
  R.v52935 (state s) (inputs i) = Zmod.unsigned (N.v52935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52935 s i)) at 1.
  unfold R.v52935, N.v52935.
  unfold R.v6, N.v6.
  rewrite ?node_13626.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52936 (s : N.State) (i : N.Inputs) :
  R.v52936 (state s) (inputs i) = Zmod.unsigned (N.v52936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52936 s i)) at 1.
  unfold R.v52936, N.v52936.
  rewrite ?node_52934.
  rewrite ?node_52935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52937 (s : N.State) (i : N.Inputs) :
  R.v52937 (state s) (inputs i) = Zmod.unsigned (N.v52937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52937 s i)) at 1.
  unfold R.v52937, N.v52937.
  rewrite ?node_52933.
  rewrite ?node_52936.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52938 (s : N.State) (i : N.Inputs) :
  R.v52938 (state s) (inputs i) = Zmod.unsigned (N.v52938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52938 s i)) at 1.
  unfold R.v52938, N.v52938.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52939 (s : N.State) (i : N.Inputs) :
  R.v52939 (state s) (inputs i) = Zmod.unsigned (N.v52939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52939 s i)) at 1.
  unfold R.v52939, N.v52939.
  rewrite ?node_13510.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52940 (s : N.State) (i : N.Inputs) :
  R.v52940 (state s) (inputs i) = Zmod.unsigned (N.v52940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52940 s i)) at 1.
  unfold R.v52940, N.v52940.
  unfold R.v6, N.v6.
  rewrite ?node_13506.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52941 (s : N.State) (i : N.Inputs) :
  R.v52941 (state s) (inputs i) = Zmod.unsigned (N.v52941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52941 s i)) at 1.
  unfold R.v52941, N.v52941.
  unfold R.v6, N.v6.
  rewrite ?node_13503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52942 (s : N.State) (i : N.Inputs) :
  R.v52942 (state s) (inputs i) = Zmod.unsigned (N.v52942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52942 s i)) at 1.
  unfold R.v52942, N.v52942.
  rewrite ?node_52940.
  rewrite ?node_52941.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52943 (s : N.State) (i : N.Inputs) :
  R.v52943 (state s) (inputs i) = Zmod.unsigned (N.v52943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52943 s i)) at 1.
  unfold R.v52943, N.v52943.
  unfold R.v16484, N.v16484.
  rewrite ?node_52942.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52944 (s : N.State) (i : N.Inputs) :
  R.v52944 (state s) (inputs i) = Zmod.unsigned (N.v52944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52944 s i)) at 1.
  unfold R.v52944, N.v52944.
  rewrite ?node_52939.
  rewrite ?node_52943.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52945 (s : N.State) (i : N.Inputs) :
  R.v52945 (state s) (inputs i) = Zmod.unsigned (N.v52945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52945 s i)) at 1.
  unfold R.v52945, N.v52945.
  unfold R.v6, N.v6.
  rewrite ?node_52944.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52946 (s : N.State) (i : N.Inputs) :
  R.v52946 (state s) (inputs i) = Zmod.unsigned (N.v52946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52946 s i)) at 1.
  unfold R.v52946, N.v52946.
  rewrite ?node_13511.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52947 (s : N.State) (i : N.Inputs) :
  R.v52947 (state s) (inputs i) = Zmod.unsigned (N.v52947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52947 s i)) at 1.
  unfold R.v52947, N.v52947.
  unfold R.v6, N.v6.
  rewrite ?node_13630.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52948 (s : N.State) (i : N.Inputs) :
  R.v52948 (state s) (inputs i) = Zmod.unsigned (N.v52948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52948 s i)) at 1.
  unfold R.v52948, N.v52948.
  rewrite ?node_52946.
  rewrite ?node_52947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52949 (s : N.State) (i : N.Inputs) :
  R.v52949 (state s) (inputs i) = Zmod.unsigned (N.v52949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52949 s i)) at 1.
  unfold R.v52949, N.v52949.
  rewrite ?node_52945.
  rewrite ?node_52948.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52950 (s : N.State) (i : N.Inputs) :
  R.v52950 (state s) (inputs i) = Zmod.unsigned (N.v52950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52950 s i)) at 1.
  unfold R.v52950, N.v52950.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52951 (s : N.State) (i : N.Inputs) :
  R.v52951 (state s) (inputs i) = Zmod.unsigned (N.v52951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52951 s i)) at 1.
  unfold R.v52951, N.v52951.
  rewrite ?node_13614.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52952 (s : N.State) (i : N.Inputs) :
  R.v52952 (state s) (inputs i) = Zmod.unsigned (N.v52952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52952 s i)) at 1.
  unfold R.v52952, N.v52952.
  rewrite ?node_13610.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52953 (s : N.State) (i : N.Inputs) :
  R.v52953 (state s) (inputs i) = Zmod.unsigned (N.v52953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52953 s i)) at 1.
  unfold R.v52953, N.v52953.
  rewrite ?node_13606.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52954 (s : N.State) (i : N.Inputs) :
  R.v52954 (state s) (inputs i) = Zmod.unsigned (N.v52954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52954 s i)) at 1.
  unfold R.v52954, N.v52954.
  unfold R.v6, N.v6.
  rewrite ?node_13586.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52955 (s : N.State) (i : N.Inputs) :
  R.v52955 (state s) (inputs i) = Zmod.unsigned (N.v52955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52955 s i)) at 1.
  unfold R.v52955, N.v52955.
  unfold R.v6, N.v6.
  rewrite ?node_13564.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52956 (s : N.State) (i : N.Inputs) :
  R.v52956 (state s) (inputs i) = Zmod.unsigned (N.v52956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52956 s i)) at 1.
  unfold R.v52956, N.v52956.
  rewrite ?node_52954.
  rewrite ?node_52955.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52957 (s : N.State) (i : N.Inputs) :
  R.v52957 (state s) (inputs i) = Zmod.unsigned (N.v52957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52957 s i)) at 1.
  unfold R.v52957, N.v52957.
  unfold R.v16484, N.v16484.
  rewrite ?node_52956.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52958 (s : N.State) (i : N.Inputs) :
  R.v52958 (state s) (inputs i) = Zmod.unsigned (N.v52958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52958 s i)) at 1.
  unfold R.v52958, N.v52958.
  rewrite ?node_52951.
  rewrite ?node_52952.
  rewrite ?node_52953.
  rewrite ?node_52957.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52959 (s : N.State) (i : N.Inputs) :
  R.v52959 (state s) (inputs i) = Zmod.unsigned (N.v52959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52959 s i)) at 1.
  unfold R.v52959, N.v52959.
  unfold R.v6, N.v6.
  rewrite ?node_52958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52960 (s : N.State) (i : N.Inputs) :
  R.v52960 (state s) (inputs i) = Zmod.unsigned (N.v52960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52960 s i)) at 1.
  unfold R.v52960, N.v52960.
  rewrite ?node_13615.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52961 (s : N.State) (i : N.Inputs) :
  R.v52961 (state s) (inputs i) = Zmod.unsigned (N.v52961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52961 s i)) at 1.
  unfold R.v52961, N.v52961.
  unfold R.v6, N.v6.
  rewrite ?node_13725.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52962 (s : N.State) (i : N.Inputs) :
  R.v52962 (state s) (inputs i) = Zmod.unsigned (N.v52962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52962 s i)) at 1.
  unfold R.v52962, N.v52962.
  unfold R.v6, N.v6.
  rewrite ?node_13737.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52963 (s : N.State) (i : N.Inputs) :
  R.v52963 (state s) (inputs i) = Zmod.unsigned (N.v52963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52963 s i)) at 1.
  unfold R.v52963, N.v52963.
  rewrite ?node_52960.
  rewrite ?node_52961.
  rewrite ?node_52962.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52964 (s : N.State) (i : N.Inputs) :
  R.v52964 (state s) (inputs i) = Zmod.unsigned (N.v52964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52964 s i)) at 1.
  unfold R.v52964, N.v52964.
  rewrite ?node_52959.
  rewrite ?node_52963.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52965 (s : N.State) (i : N.Inputs) :
  R.v52965 (state s) (inputs i) = Zmod.unsigned (N.v52965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52965 s i)) at 1.
  unfold R.v52965, N.v52965.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52966 (s : N.State) (i : N.Inputs) :
  R.v52966 (state s) (inputs i) = Zmod.unsigned (N.v52966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52966 s i)) at 1.
  unfold R.v52966, N.v52966.
  rewrite ?node_13606.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52967 (s : N.State) (i : N.Inputs) :
  R.v52967 (state s) (inputs i) = Zmod.unsigned (N.v52967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52967 s i)) at 1.
  unfold R.v52967, N.v52967.
  unfold R.v6, N.v6.
  rewrite ?node_13586.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52968 (s : N.State) (i : N.Inputs) :
  R.v52968 (state s) (inputs i) = Zmod.unsigned (N.v52968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52968 s i)) at 1.
  unfold R.v52968, N.v52968.
  unfold R.v6, N.v6.
  rewrite ?node_13564.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52969 (s : N.State) (i : N.Inputs) :
  R.v52969 (state s) (inputs i) = Zmod.unsigned (N.v52969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52969 s i)) at 1.
  unfold R.v52969, N.v52969.
  rewrite ?node_52967.
  rewrite ?node_52968.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52970 (s : N.State) (i : N.Inputs) :
  R.v52970 (state s) (inputs i) = Zmod.unsigned (N.v52970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52970 s i)) at 1.
  unfold R.v52970, N.v52970.
  unfold R.v16484, N.v16484.
  rewrite ?node_52969.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52971 (s : N.State) (i : N.Inputs) :
  R.v52971 (state s) (inputs i) = Zmod.unsigned (N.v52971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52971 s i)) at 1.
  unfold R.v52971, N.v52971.
  rewrite ?node_52966.
  rewrite ?node_52970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52972 (s : N.State) (i : N.Inputs) :
  R.v52972 (state s) (inputs i) = Zmod.unsigned (N.v52972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52972 s i)) at 1.
  unfold R.v52972, N.v52972.
  unfold R.v6, N.v6.
  rewrite ?node_52971.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52973 (s : N.State) (i : N.Inputs) :
  R.v52973 (state s) (inputs i) = Zmod.unsigned (N.v52973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52973 s i)) at 1.
  unfold R.v52973, N.v52973.
  rewrite ?node_13607.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52974 (s : N.State) (i : N.Inputs) :
  R.v52974 (state s) (inputs i) = Zmod.unsigned (N.v52974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52974 s i)) at 1.
  unfold R.v52974, N.v52974.
  unfold R.v6, N.v6.
  rewrite ?node_13725.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52975 (s : N.State) (i : N.Inputs) :
  R.v52975 (state s) (inputs i) = Zmod.unsigned (N.v52975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52975 s i)) at 1.
  unfold R.v52975, N.v52975.
  rewrite ?node_52973.
  rewrite ?node_52974.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52976 (s : N.State) (i : N.Inputs) :
  R.v52976 (state s) (inputs i) = Zmod.unsigned (N.v52976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52976 s i)) at 1.
  unfold R.v52976, N.v52976.
  rewrite ?node_52972.
  rewrite ?node_52975.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52977 (s : N.State) (i : N.Inputs) :
  R.v52977 (state s) (inputs i) = Zmod.unsigned (N.v52977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52977 s i)) at 1.
  unfold R.v52977, N.v52977.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52978 (s : N.State) (i : N.Inputs) :
  R.v52978 (state s) (inputs i) = Zmod.unsigned (N.v52978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52978 s i)) at 1.
  unfold R.v52978, N.v52978.
  rewrite ?node_13614.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52979 (s : N.State) (i : N.Inputs) :
  R.v52979 (state s) (inputs i) = Zmod.unsigned (N.v52979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52979 s i)) at 1.
  unfold R.v52979, N.v52979.
  unfold R.v6, N.v6.
  rewrite ?node_13610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52980 (s : N.State) (i : N.Inputs) :
  R.v52980 (state s) (inputs i) = Zmod.unsigned (N.v52980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52980 s i)) at 1.
  unfold R.v52980, N.v52980.
  unfold R.v6, N.v6.
  rewrite ?node_13607.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52981 (s : N.State) (i : N.Inputs) :
  R.v52981 (state s) (inputs i) = Zmod.unsigned (N.v52981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52981 s i)) at 1.
  unfold R.v52981, N.v52981.
  rewrite ?node_52979.
  rewrite ?node_52980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52982 (s : N.State) (i : N.Inputs) :
  R.v52982 (state s) (inputs i) = Zmod.unsigned (N.v52982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52982 s i)) at 1.
  unfold R.v52982, N.v52982.
  unfold R.v16484, N.v16484.
  rewrite ?node_52981.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52983 (s : N.State) (i : N.Inputs) :
  R.v52983 (state s) (inputs i) = Zmod.unsigned (N.v52983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52983 s i)) at 1.
  unfold R.v52983, N.v52983.
  rewrite ?node_52978.
  rewrite ?node_52982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52984 (s : N.State) (i : N.Inputs) :
  R.v52984 (state s) (inputs i) = Zmod.unsigned (N.v52984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52984 s i)) at 1.
  unfold R.v52984, N.v52984.
  unfold R.v6, N.v6.
  rewrite ?node_52983.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52985 (s : N.State) (i : N.Inputs) :
  R.v52985 (state s) (inputs i) = Zmod.unsigned (N.v52985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52985 s i)) at 1.
  unfold R.v52985, N.v52985.
  rewrite ?node_13615.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52986 (s : N.State) (i : N.Inputs) :
  R.v52986 (state s) (inputs i) = Zmod.unsigned (N.v52986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52986 s i)) at 1.
  unfold R.v52986, N.v52986.
  unfold R.v6, N.v6.
  rewrite ?node_13737.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52987 (s : N.State) (i : N.Inputs) :
  R.v52987 (state s) (inputs i) = Zmod.unsigned (N.v52987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52987 s i)) at 1.
  unfold R.v52987, N.v52987.
  rewrite ?node_52985.
  rewrite ?node_52986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52988 (s : N.State) (i : N.Inputs) :
  R.v52988 (state s) (inputs i) = Zmod.unsigned (N.v52988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52988 s i)) at 1.
  unfold R.v52988, N.v52988.
  rewrite ?node_52984.
  rewrite ?node_52987.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52989 (s : N.State) (i : N.Inputs) :
  R.v52989 (state s) (inputs i) = Zmod.unsigned (N.v52989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52989 s i)) at 1.
  unfold R.v52989, N.v52989.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52990 (s : N.State) (i : N.Inputs) :
  R.v52990 (state s) (inputs i) = Zmod.unsigned (N.v52990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52990 s i)) at 1.
  unfold R.v52990, N.v52990.
  unfold R.v6, N.v6.
  rewrite ?node_13621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52991 (s : N.State) (i : N.Inputs) :
  R.v52991 (state s) (inputs i) = Zmod.unsigned (N.v52991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52991 s i)) at 1.
  unfold R.v52991, N.v52991.
  unfold R.v6, N.v6.
  rewrite ?node_13618.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52992 (s : N.State) (i : N.Inputs) :
  R.v52992 (state s) (inputs i) = Zmod.unsigned (N.v52992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52992 s i)) at 1.
  unfold R.v52992, N.v52992.
  rewrite ?node_52990.
  rewrite ?node_52991.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52993 (s : N.State) (i : N.Inputs) :
  R.v52993 (state s) (inputs i) = Zmod.unsigned (N.v52993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52993 s i)) at 1.
  unfold R.v52993, N.v52993.
  unfold R.v16463, N.v16463.
  rewrite ?node_52992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52994 (s : N.State) (i : N.Inputs) :
  R.v52994 (state s) (inputs i) = Zmod.unsigned (N.v52994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52994 s i)) at 1.
  unfold R.v52994, N.v52994.
  rewrite ?node_13622.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52995 (s : N.State) (i : N.Inputs) :
  R.v52995 (state s) (inputs i) = Zmod.unsigned (N.v52995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52995 s i)) at 1.
  unfold R.v52995, N.v52995.
  unfold R.v6, N.v6.
  rewrite ?node_13739.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52996 (s : N.State) (i : N.Inputs) :
  R.v52996 (state s) (inputs i) = Zmod.unsigned (N.v52996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52996 s i)) at 1.
  unfold R.v52996, N.v52996.
  rewrite ?node_52994.
  rewrite ?node_52995.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52997 (s : N.State) (i : N.Inputs) :
  R.v52997 (state s) (inputs i) = Zmod.unsigned (N.v52997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52997 s i)) at 1.
  unfold R.v52997, N.v52997.
  rewrite ?node_52993.
  rewrite ?node_52996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52998 (s : N.State) (i : N.Inputs) :
  R.v52998 (state s) (inputs i) = Zmod.unsigned (N.v52998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52998 s i)) at 1.
  unfold R.v52998, N.v52998.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52999 (s : N.State) (i : N.Inputs) :
  R.v52999 (state s) (inputs i) = Zmod.unsigned (N.v52999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52999 s i)) at 1.
  unfold R.v52999, N.v52999.
  rewrite ?node_13725.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
