(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes016.
Lemma node_17000 (s : N.State) (i : N.Inputs) :
  R.v17000 (state s) (inputs i) = Zmod.unsigned (N.v17000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17000 s i)) at 1.
  unfold R.v17000, N.v17000.
  unfold R.v6, N.v6.
  rewrite ?node_5355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17001 (s : N.State) (i : N.Inputs) :
  R.v17001 (state s) (inputs i) = Zmod.unsigned (N.v17001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17001 s i)) at 1.
  unfold R.v17001, N.v17001.
  rewrite ?node_16999.
  rewrite ?node_17000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17002 (s : N.State) (i : N.Inputs) :
  R.v17002 (state s) (inputs i) = Zmod.unsigned (N.v17002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17002 s i)) at 1.
  unfold R.v17002, N.v17002.
  unfold R.v16484, N.v16484.
  rewrite ?node_17001.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17003 (s : N.State) (i : N.Inputs) :
  R.v17003 (state s) (inputs i) = Zmod.unsigned (N.v17003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17003 s i)) at 1.
  unfold R.v17003, N.v17003.
  rewrite ?node_16998.
  rewrite ?node_17002.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17004 (s : N.State) (i : N.Inputs) :
  R.v17004 (state s) (inputs i) = Zmod.unsigned (N.v17004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17004 s i)) at 1.
  unfold R.v17004, N.v17004.
  unfold R.v6, N.v6.
  rewrite ?node_17003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17005 (s : N.State) (i : N.Inputs) :
  R.v17005 (state s) (inputs i) = Zmod.unsigned (N.v17005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17005 s i)) at 1.
  unfold R.v17005, N.v17005.
  rewrite ?node_5360.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17006 (s : N.State) (i : N.Inputs) :
  R.v17006 (state s) (inputs i) = Zmod.unsigned (N.v17006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17006 s i)) at 1.
  unfold R.v17006, N.v17006.
  unfold R.v6, N.v6.
  rewrite ?node_5409.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17007 (s : N.State) (i : N.Inputs) :
  R.v17007 (state s) (inputs i) = Zmod.unsigned (N.v17007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17007 s i)) at 1.
  unfold R.v17007, N.v17007.
  rewrite ?node_17005.
  rewrite ?node_17006.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17008 (s : N.State) (i : N.Inputs) :
  R.v17008 (state s) (inputs i) = Zmod.unsigned (N.v17008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17008 s i)) at 1.
  unfold R.v17008, N.v17008.
  rewrite ?node_17004.
  rewrite ?node_17007.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17009 (s : N.State) (i : N.Inputs) :
  R.v17009 (state s) (inputs i) = Zmod.unsigned (N.v17009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17009 s i)) at 1.
  unfold R.v17009, N.v17009.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17010 (s : N.State) (i : N.Inputs) :
  R.v17010 (state s) (inputs i) = Zmod.unsigned (N.v17010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17010 s i)) at 1.
  unfold R.v17010, N.v17010.
  rewrite ?node_5388.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17011 (s : N.State) (i : N.Inputs) :
  R.v17011 (state s) (inputs i) = Zmod.unsigned (N.v17011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17011 s i)) at 1.
  unfold R.v17011, N.v17011.
  unfold R.v16463, N.v16463.
  rewrite !state_r73_nr_5F73.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r73_nr_5F73 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17012 (s : N.State) (i : N.Inputs) :
  R.v17012 (state s) (inputs i) = Zmod.unsigned (N.v17012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17012 s i)) at 1.
  unfold R.v17012, N.v17012.
  unfold R.v16463, N.v16463.
  rewrite !state_r72_nr_5F72.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r72_nr_5F72 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17013 (s : N.State) (i : N.Inputs) :
  R.v17013 (state s) (inputs i) = Zmod.unsigned (N.v17013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17013 s i)) at 1.
  unfold R.v17013, N.v17013.
  unfold R.v6, N.v6.
  rewrite !state_r71_nr_5F71.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r71_nr_5F71 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17014 (s : N.State) (i : N.Inputs) :
  R.v17014 (state s) (inputs i) = Zmod.unsigned (N.v17014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17014 s i)) at 1.
  unfold R.v17014, N.v17014.
  unfold R.v6, N.v6.
  rewrite !state_r70_nr_5F70.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r70_nr_5F70 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17015 (s : N.State) (i : N.Inputs) :
  R.v17015 (state s) (inputs i) = Zmod.unsigned (N.v17015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17015 s i)) at 1.
  unfold R.v17015, N.v17015.
  rewrite ?node_17013.
  rewrite ?node_17014.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17016 (s : N.State) (i : N.Inputs) :
  R.v17016 (state s) (inputs i) = Zmod.unsigned (N.v17016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17016 s i)) at 1.
  unfold R.v17016, N.v17016.
  unfold R.v16484, N.v16484.
  rewrite ?node_17015.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17017 (s : N.State) (i : N.Inputs) :
  R.v17017 (state s) (inputs i) = Zmod.unsigned (N.v17017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17017 s i)) at 1.
  unfold R.v17017, N.v17017.
  rewrite ?node_17010.
  rewrite ?node_17011.
  rewrite ?node_17012.
  rewrite ?node_17016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17018 (s : N.State) (i : N.Inputs) :
  R.v17018 (state s) (inputs i) = Zmod.unsigned (N.v17018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17018 s i)) at 1.
  unfold R.v17018, N.v17018.
  unfold R.v6, N.v6.
  rewrite ?node_17017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17019 (s : N.State) (i : N.Inputs) :
  R.v17019 (state s) (inputs i) = Zmod.unsigned (N.v17019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17019 s i)) at 1.
  unfold R.v17019, N.v17019.
  rewrite ?node_5389.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17020 (s : N.State) (i : N.Inputs) :
  R.v17020 (state s) (inputs i) = Zmod.unsigned (N.v17020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17020 s i)) at 1.
  unfold R.v17020, N.v17020.
  unfold R.v6, N.v6.
  rewrite ?node_5427.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17021 (s : N.State) (i : N.Inputs) :
  R.v17021 (state s) (inputs i) = Zmod.unsigned (N.v17021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17021 s i)) at 1.
  unfold R.v17021, N.v17021.
  unfold R.v6, N.v6.
  rewrite ?node_5440.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17022 (s : N.State) (i : N.Inputs) :
  R.v17022 (state s) (inputs i) = Zmod.unsigned (N.v17022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17022 s i)) at 1.
  unfold R.v17022, N.v17022.
  rewrite ?node_17019.
  rewrite ?node_17020.
  rewrite ?node_17021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17023 (s : N.State) (i : N.Inputs) :
  R.v17023 (state s) (inputs i) = Zmod.unsigned (N.v17023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17023 s i)) at 1.
  unfold R.v17023, N.v17023.
  rewrite ?node_17018.
  rewrite ?node_17022.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17024 (s : N.State) (i : N.Inputs) :
  R.v17024 (state s) (inputs i) = Zmod.unsigned (N.v17024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17024 s i)) at 1.
  unfold R.v17024, N.v17024.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17025 (s : N.State) (i : N.Inputs) :
  R.v17025 (state s) (inputs i) = Zmod.unsigned (N.v17025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17025 s i)) at 1.
  unfold R.v17025, N.v17025.
  unfold R.v16463, N.v16463.
  rewrite !state_r72_nr_5F72.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r72_nr_5F72 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17026 (s : N.State) (i : N.Inputs) :
  R.v17026 (state s) (inputs i) = Zmod.unsigned (N.v17026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17026 s i)) at 1.
  unfold R.v17026, N.v17026.
  unfold R.v6, N.v6.
  rewrite !state_r71_nr_5F71.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r71_nr_5F71 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17027 (s : N.State) (i : N.Inputs) :
  R.v17027 (state s) (inputs i) = Zmod.unsigned (N.v17027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17027 s i)) at 1.
  unfold R.v17027, N.v17027.
  unfold R.v6, N.v6.
  rewrite !state_r70_nr_5F70.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r70_nr_5F70 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17028 (s : N.State) (i : N.Inputs) :
  R.v17028 (state s) (inputs i) = Zmod.unsigned (N.v17028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17028 s i)) at 1.
  unfold R.v17028, N.v17028.
  rewrite ?node_17026.
  rewrite ?node_17027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17029 (s : N.State) (i : N.Inputs) :
  R.v17029 (state s) (inputs i) = Zmod.unsigned (N.v17029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17029 s i)) at 1.
  unfold R.v17029, N.v17029.
  unfold R.v16484, N.v16484.
  rewrite ?node_17028.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17030 (s : N.State) (i : N.Inputs) :
  R.v17030 (state s) (inputs i) = Zmod.unsigned (N.v17030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17030 s i)) at 1.
  unfold R.v17030, N.v17030.
  rewrite ?node_17025.
  rewrite ?node_17029.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17031 (s : N.State) (i : N.Inputs) :
  R.v17031 (state s) (inputs i) = Zmod.unsigned (N.v17031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17031 s i)) at 1.
  unfold R.v17031, N.v17031.
  unfold R.v6, N.v6.
  rewrite ?node_17030.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17032 (s : N.State) (i : N.Inputs) :
  R.v17032 (state s) (inputs i) = Zmod.unsigned (N.v17032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17032 s i)) at 1.
  unfold R.v17032, N.v17032.
  rewrite ?node_5384.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17033 (s : N.State) (i : N.Inputs) :
  R.v17033 (state s) (inputs i) = Zmod.unsigned (N.v17033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17033 s i)) at 1.
  unfold R.v17033, N.v17033.
  unfold R.v6, N.v6.
  rewrite ?node_5427.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17034 (s : N.State) (i : N.Inputs) :
  R.v17034 (state s) (inputs i) = Zmod.unsigned (N.v17034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17034 s i)) at 1.
  unfold R.v17034, N.v17034.
  rewrite ?node_17032.
  rewrite ?node_17033.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17035 (s : N.State) (i : N.Inputs) :
  R.v17035 (state s) (inputs i) = Zmod.unsigned (N.v17035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17035 s i)) at 1.
  unfold R.v17035, N.v17035.
  rewrite ?node_17031.
  rewrite ?node_17034.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17036 (s : N.State) (i : N.Inputs) :
  R.v17036 (state s) (inputs i) = Zmod.unsigned (N.v17036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17036 s i)) at 1.
  unfold R.v17036, N.v17036.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17037 (s : N.State) (i : N.Inputs) :
  R.v17037 (state s) (inputs i) = Zmod.unsigned (N.v17037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17037 s i)) at 1.
  unfold R.v17037, N.v17037.
  rewrite ?node_5388.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17038 (s : N.State) (i : N.Inputs) :
  R.v17038 (state s) (inputs i) = Zmod.unsigned (N.v17038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17038 s i)) at 1.
  unfold R.v17038, N.v17038.
  unfold R.v6, N.v6.
  rewrite !state_r73_nr_5F73.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r73_nr_5F73 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17039 (s : N.State) (i : N.Inputs) :
  R.v17039 (state s) (inputs i) = Zmod.unsigned (N.v17039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17039 s i)) at 1.
  unfold R.v17039, N.v17039.
  unfold R.v6, N.v6.
  rewrite ?node_5384.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17040 (s : N.State) (i : N.Inputs) :
  R.v17040 (state s) (inputs i) = Zmod.unsigned (N.v17040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17040 s i)) at 1.
  unfold R.v17040, N.v17040.
  rewrite ?node_17038.
  rewrite ?node_17039.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17041 (s : N.State) (i : N.Inputs) :
  R.v17041 (state s) (inputs i) = Zmod.unsigned (N.v17041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17041 s i)) at 1.
  unfold R.v17041, N.v17041.
  unfold R.v16484, N.v16484.
  rewrite ?node_17040.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17042 (s : N.State) (i : N.Inputs) :
  R.v17042 (state s) (inputs i) = Zmod.unsigned (N.v17042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17042 s i)) at 1.
  unfold R.v17042, N.v17042.
  rewrite ?node_17037.
  rewrite ?node_17041.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17043 (s : N.State) (i : N.Inputs) :
  R.v17043 (state s) (inputs i) = Zmod.unsigned (N.v17043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17043 s i)) at 1.
  unfold R.v17043, N.v17043.
  unfold R.v6, N.v6.
  rewrite ?node_17042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17044 (s : N.State) (i : N.Inputs) :
  R.v17044 (state s) (inputs i) = Zmod.unsigned (N.v17044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17044 s i)) at 1.
  unfold R.v17044, N.v17044.
  rewrite ?node_5389.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17045 (s : N.State) (i : N.Inputs) :
  R.v17045 (state s) (inputs i) = Zmod.unsigned (N.v17045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17045 s i)) at 1.
  unfold R.v17045, N.v17045.
  unfold R.v6, N.v6.
  rewrite ?node_5440.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17046 (s : N.State) (i : N.Inputs) :
  R.v17046 (state s) (inputs i) = Zmod.unsigned (N.v17046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17046 s i)) at 1.
  unfold R.v17046, N.v17046.
  rewrite ?node_17044.
  rewrite ?node_17045.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17047 (s : N.State) (i : N.Inputs) :
  R.v17047 (state s) (inputs i) = Zmod.unsigned (N.v17047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17047 s i)) at 1.
  unfold R.v17047, N.v17047.
  rewrite ?node_17043.
  rewrite ?node_17046.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17048 (s : N.State) (i : N.Inputs) :
  R.v17048 (state s) (inputs i) = Zmod.unsigned (N.v17048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17048 s i)) at 1.
  unfold R.v17048, N.v17048.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17049 (s : N.State) (i : N.Inputs) :
  R.v17049 (state s) (inputs i) = Zmod.unsigned (N.v17049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17049 s i)) at 1.
  unfold R.v17049, N.v17049.
  rewrite ?node_5395.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17050 (s : N.State) (i : N.Inputs) :
  R.v17050 (state s) (inputs i) = Zmod.unsigned (N.v17050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17050 s i)) at 1.
  unfold R.v17050, N.v17050.
  unfold R.v16463, N.v16463.
  rewrite !state_r77_nr_5F77.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r77_nr_5F77 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17051 (s : N.State) (i : N.Inputs) :
  R.v17051 (state s) (inputs i) = Zmod.unsigned (N.v17051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17051 s i)) at 1.
  unfold R.v17051, N.v17051.
  unfold R.v16463, N.v16463.
  rewrite !state_r76_nr_5F76.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r76_nr_5F76 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17052 (s : N.State) (i : N.Inputs) :
  R.v17052 (state s) (inputs i) = Zmod.unsigned (N.v17052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17052 s i)) at 1.
  unfold R.v17052, N.v17052.
  unfold R.v6, N.v6.
  rewrite !state_r75_nr_5F75.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r75_nr_5F75 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17053 (s : N.State) (i : N.Inputs) :
  R.v17053 (state s) (inputs i) = Zmod.unsigned (N.v17053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17053 s i)) at 1.
  unfold R.v17053, N.v17053.
  unfold R.v6, N.v6.
  rewrite !state_r74_nr_5F74.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r74_nr_5F74 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17054 (s : N.State) (i : N.Inputs) :
  R.v17054 (state s) (inputs i) = Zmod.unsigned (N.v17054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17054 s i)) at 1.
  unfold R.v17054, N.v17054.
  rewrite ?node_17052.
  rewrite ?node_17053.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17055 (s : N.State) (i : N.Inputs) :
  R.v17055 (state s) (inputs i) = Zmod.unsigned (N.v17055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17055 s i)) at 1.
  unfold R.v17055, N.v17055.
  unfold R.v16484, N.v16484.
  rewrite ?node_17054.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17056 (s : N.State) (i : N.Inputs) :
  R.v17056 (state s) (inputs i) = Zmod.unsigned (N.v17056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17056 s i)) at 1.
  unfold R.v17056, N.v17056.
  rewrite ?node_17049.
  rewrite ?node_17050.
  rewrite ?node_17051.
  rewrite ?node_17055.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17057 (s : N.State) (i : N.Inputs) :
  R.v17057 (state s) (inputs i) = Zmod.unsigned (N.v17057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17057 s i)) at 1.
  unfold R.v17057, N.v17057.
  unfold R.v6, N.v6.
  rewrite ?node_17056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17058 (s : N.State) (i : N.Inputs) :
  R.v17058 (state s) (inputs i) = Zmod.unsigned (N.v17058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17058 s i)) at 1.
  unfold R.v17058, N.v17058.
  rewrite ?node_5396.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17059 (s : N.State) (i : N.Inputs) :
  R.v17059 (state s) (inputs i) = Zmod.unsigned (N.v17059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17059 s i)) at 1.
  unfold R.v17059, N.v17059.
  unfold R.v6, N.v6.
  rewrite ?node_5434.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17060 (s : N.State) (i : N.Inputs) :
  R.v17060 (state s) (inputs i) = Zmod.unsigned (N.v17060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17060 s i)) at 1.
  unfold R.v17060, N.v17060.
  unfold R.v6, N.v6.
  rewrite ?node_5448.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17061 (s : N.State) (i : N.Inputs) :
  R.v17061 (state s) (inputs i) = Zmod.unsigned (N.v17061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17061 s i)) at 1.
  unfold R.v17061, N.v17061.
  rewrite ?node_17058.
  rewrite ?node_17059.
  rewrite ?node_17060.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17062 (s : N.State) (i : N.Inputs) :
  R.v17062 (state s) (inputs i) = Zmod.unsigned (N.v17062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17062 s i)) at 1.
  unfold R.v17062, N.v17062.
  rewrite ?node_17057.
  rewrite ?node_17061.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17063 (s : N.State) (i : N.Inputs) :
  R.v17063 (state s) (inputs i) = Zmod.unsigned (N.v17063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17063 s i)) at 1.
  unfold R.v17063, N.v17063.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17064 (s : N.State) (i : N.Inputs) :
  R.v17064 (state s) (inputs i) = Zmod.unsigned (N.v17064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17064 s i)) at 1.
  unfold R.v17064, N.v17064.
  unfold R.v16463, N.v16463.
  rewrite !state_r76_nr_5F76.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r76_nr_5F76 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17065 (s : N.State) (i : N.Inputs) :
  R.v17065 (state s) (inputs i) = Zmod.unsigned (N.v17065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17065 s i)) at 1.
  unfold R.v17065, N.v17065.
  unfold R.v6, N.v6.
  rewrite !state_r75_nr_5F75.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r75_nr_5F75 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17066 (s : N.State) (i : N.Inputs) :
  R.v17066 (state s) (inputs i) = Zmod.unsigned (N.v17066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17066 s i)) at 1.
  unfold R.v17066, N.v17066.
  unfold R.v6, N.v6.
  rewrite !state_r74_nr_5F74.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r74_nr_5F74 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17067 (s : N.State) (i : N.Inputs) :
  R.v17067 (state s) (inputs i) = Zmod.unsigned (N.v17067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17067 s i)) at 1.
  unfold R.v17067, N.v17067.
  rewrite ?node_17065.
  rewrite ?node_17066.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17068 (s : N.State) (i : N.Inputs) :
  R.v17068 (state s) (inputs i) = Zmod.unsigned (N.v17068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17068 s i)) at 1.
  unfold R.v17068, N.v17068.
  unfold R.v16484, N.v16484.
  rewrite ?node_17067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17069 (s : N.State) (i : N.Inputs) :
  R.v17069 (state s) (inputs i) = Zmod.unsigned (N.v17069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17069 s i)) at 1.
  unfold R.v17069, N.v17069.
  rewrite ?node_17064.
  rewrite ?node_17068.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17070 (s : N.State) (i : N.Inputs) :
  R.v17070 (state s) (inputs i) = Zmod.unsigned (N.v17070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17070 s i)) at 1.
  unfold R.v17070, N.v17070.
  unfold R.v6, N.v6.
  rewrite ?node_17069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17071 (s : N.State) (i : N.Inputs) :
  R.v17071 (state s) (inputs i) = Zmod.unsigned (N.v17071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17071 s i)) at 1.
  unfold R.v17071, N.v17071.
  rewrite ?node_5391.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17072 (s : N.State) (i : N.Inputs) :
  R.v17072 (state s) (inputs i) = Zmod.unsigned (N.v17072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17072 s i)) at 1.
  unfold R.v17072, N.v17072.
  unfold R.v6, N.v6.
  rewrite ?node_5434.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17073 (s : N.State) (i : N.Inputs) :
  R.v17073 (state s) (inputs i) = Zmod.unsigned (N.v17073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17073 s i)) at 1.
  unfold R.v17073, N.v17073.
  rewrite ?node_17071.
  rewrite ?node_17072.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17074 (s : N.State) (i : N.Inputs) :
  R.v17074 (state s) (inputs i) = Zmod.unsigned (N.v17074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17074 s i)) at 1.
  unfold R.v17074, N.v17074.
  rewrite ?node_17070.
  rewrite ?node_17073.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17075 (s : N.State) (i : N.Inputs) :
  R.v17075 (state s) (inputs i) = Zmod.unsigned (N.v17075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17075 s i)) at 1.
  unfold R.v17075, N.v17075.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17076 (s : N.State) (i : N.Inputs) :
  R.v17076 (state s) (inputs i) = Zmod.unsigned (N.v17076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17076 s i)) at 1.
  unfold R.v17076, N.v17076.
  rewrite ?node_5395.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17077 (s : N.State) (i : N.Inputs) :
  R.v17077 (state s) (inputs i) = Zmod.unsigned (N.v17077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17077 s i)) at 1.
  unfold R.v17077, N.v17077.
  unfold R.v6, N.v6.
  rewrite !state_r77_nr_5F77.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r77_nr_5F77 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17078 (s : N.State) (i : N.Inputs) :
  R.v17078 (state s) (inputs i) = Zmod.unsigned (N.v17078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17078 s i)) at 1.
  unfold R.v17078, N.v17078.
  unfold R.v6, N.v6.
  rewrite ?node_5391.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17079 (s : N.State) (i : N.Inputs) :
  R.v17079 (state s) (inputs i) = Zmod.unsigned (N.v17079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17079 s i)) at 1.
  unfold R.v17079, N.v17079.
  rewrite ?node_17077.
  rewrite ?node_17078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17080 (s : N.State) (i : N.Inputs) :
  R.v17080 (state s) (inputs i) = Zmod.unsigned (N.v17080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17080 s i)) at 1.
  unfold R.v17080, N.v17080.
  unfold R.v16484, N.v16484.
  rewrite ?node_17079.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17081 (s : N.State) (i : N.Inputs) :
  R.v17081 (state s) (inputs i) = Zmod.unsigned (N.v17081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17081 s i)) at 1.
  unfold R.v17081, N.v17081.
  rewrite ?node_17076.
  rewrite ?node_17080.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17082 (s : N.State) (i : N.Inputs) :
  R.v17082 (state s) (inputs i) = Zmod.unsigned (N.v17082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17082 s i)) at 1.
  unfold R.v17082, N.v17082.
  unfold R.v6, N.v6.
  rewrite ?node_17081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17083 (s : N.State) (i : N.Inputs) :
  R.v17083 (state s) (inputs i) = Zmod.unsigned (N.v17083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17083 s i)) at 1.
  unfold R.v17083, N.v17083.
  rewrite ?node_5396.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17084 (s : N.State) (i : N.Inputs) :
  R.v17084 (state s) (inputs i) = Zmod.unsigned (N.v17084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17084 s i)) at 1.
  unfold R.v17084, N.v17084.
  unfold R.v6, N.v6.
  rewrite ?node_5448.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17085 (s : N.State) (i : N.Inputs) :
  R.v17085 (state s) (inputs i) = Zmod.unsigned (N.v17085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17085 s i)) at 1.
  unfold R.v17085, N.v17085.
  rewrite ?node_17083.
  rewrite ?node_17084.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17086 (s : N.State) (i : N.Inputs) :
  R.v17086 (state s) (inputs i) = Zmod.unsigned (N.v17086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17086 s i)) at 1.
  unfold R.v17086, N.v17086.
  rewrite ?node_17082.
  rewrite ?node_17085.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17087 (s : N.State) (i : N.Inputs) :
  R.v17087 (state s) (inputs i) = Zmod.unsigned (N.v17087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17087 s i)) at 1.
  unfold R.v17087, N.v17087.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17088 (s : N.State) (i : N.Inputs) :
  R.v17088 (state s) (inputs i) = Zmod.unsigned (N.v17088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17088 s i)) at 1.
  unfold R.v17088, N.v17088.
  rewrite ?node_5427.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17089 (s : N.State) (i : N.Inputs) :
  R.v17089 (state s) (inputs i) = Zmod.unsigned (N.v17089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17089 s i)) at 1.
  unfold R.v17089, N.v17089.
  unfold R.v16463, N.v16463.
  rewrite !state_r82_nr_5F82.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r82_nr_5F82 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17090 (s : N.State) (i : N.Inputs) :
  R.v17090 (state s) (inputs i) = Zmod.unsigned (N.v17090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17090 s i)) at 1.
  unfold R.v17090, N.v17090.
  unfold R.v16463, N.v16463.
  rewrite !state_r81_nr_5F81.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r81_nr_5F81 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17091 (s : N.State) (i : N.Inputs) :
  R.v17091 (state s) (inputs i) = Zmod.unsigned (N.v17091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17091 s i)) at 1.
  unfold R.v17091, N.v17091.
  unfold R.v6, N.v6.
  rewrite !state_r80_nr_5F80.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r80_nr_5F80 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17092 (s : N.State) (i : N.Inputs) :
  R.v17092 (state s) (inputs i) = Zmod.unsigned (N.v17092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17092 s i)) at 1.
  unfold R.v17092, N.v17092.
  unfold R.v6, N.v6.
  rewrite !state_r79_nr_5F79.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r79_nr_5F79 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17093 (s : N.State) (i : N.Inputs) :
  R.v17093 (state s) (inputs i) = Zmod.unsigned (N.v17093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17093 s i)) at 1.
  unfold R.v17093, N.v17093.
  rewrite ?node_17091.
  rewrite ?node_17092.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17094 (s : N.State) (i : N.Inputs) :
  R.v17094 (state s) (inputs i) = Zmod.unsigned (N.v17094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17094 s i)) at 1.
  unfold R.v17094, N.v17094.
  unfold R.v16484, N.v16484.
  rewrite ?node_17093.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17095 (s : N.State) (i : N.Inputs) :
  R.v17095 (state s) (inputs i) = Zmod.unsigned (N.v17095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17095 s i)) at 1.
  unfold R.v17095, N.v17095.
  rewrite ?node_17088.
  rewrite ?node_17089.
  rewrite ?node_17090.
  rewrite ?node_17094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17096 (s : N.State) (i : N.Inputs) :
  R.v17096 (state s) (inputs i) = Zmod.unsigned (N.v17096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17096 s i)) at 1.
  unfold R.v17096, N.v17096.
  unfold R.v6, N.v6.
  rewrite ?node_17095.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17097 (s : N.State) (i : N.Inputs) :
  R.v17097 (state s) (inputs i) = Zmod.unsigned (N.v17097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17097 s i)) at 1.
  unfold R.v17097, N.v17097.
  rewrite ?node_5428.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17098 (s : N.State) (i : N.Inputs) :
  R.v17098 (state s) (inputs i) = Zmod.unsigned (N.v17098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17098 s i)) at 1.
  unfold R.v17098, N.v17098.
  unfold R.v6, N.v6.
  rewrite ?node_5468.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17099 (s : N.State) (i : N.Inputs) :
  R.v17099 (state s) (inputs i) = Zmod.unsigned (N.v17099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17099 s i)) at 1.
  unfold R.v17099, N.v17099.
  unfold R.v6, N.v6.
  rewrite ?node_5482.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17100 (s : N.State) (i : N.Inputs) :
  R.v17100 (state s) (inputs i) = Zmod.unsigned (N.v17100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17100 s i)) at 1.
  unfold R.v17100, N.v17100.
  rewrite ?node_17097.
  rewrite ?node_17098.
  rewrite ?node_17099.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17101 (s : N.State) (i : N.Inputs) :
  R.v17101 (state s) (inputs i) = Zmod.unsigned (N.v17101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17101 s i)) at 1.
  unfold R.v17101, N.v17101.
  rewrite ?node_17096.
  rewrite ?node_17100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17102 (s : N.State) (i : N.Inputs) :
  R.v17102 (state s) (inputs i) = Zmod.unsigned (N.v17102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17102 s i)) at 1.
  unfold R.v17102, N.v17102.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17103 (s : N.State) (i : N.Inputs) :
  R.v17103 (state s) (inputs i) = Zmod.unsigned (N.v17103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17103 s i)) at 1.
  unfold R.v17103, N.v17103.
  unfold R.v16463, N.v16463.
  rewrite !state_r81_nr_5F81.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r81_nr_5F81 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17104 (s : N.State) (i : N.Inputs) :
  R.v17104 (state s) (inputs i) = Zmod.unsigned (N.v17104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17104 s i)) at 1.
  unfold R.v17104, N.v17104.
  unfold R.v6, N.v6.
  rewrite !state_r80_nr_5F80.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r80_nr_5F80 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17105 (s : N.State) (i : N.Inputs) :
  R.v17105 (state s) (inputs i) = Zmod.unsigned (N.v17105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17105 s i)) at 1.
  unfold R.v17105, N.v17105.
  unfold R.v6, N.v6.
  rewrite !state_r79_nr_5F79.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r79_nr_5F79 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17106 (s : N.State) (i : N.Inputs) :
  R.v17106 (state s) (inputs i) = Zmod.unsigned (N.v17106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17106 s i)) at 1.
  unfold R.v17106, N.v17106.
  rewrite ?node_17104.
  rewrite ?node_17105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17107 (s : N.State) (i : N.Inputs) :
  R.v17107 (state s) (inputs i) = Zmod.unsigned (N.v17107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17107 s i)) at 1.
  unfold R.v17107, N.v17107.
  unfold R.v16484, N.v16484.
  rewrite ?node_17106.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17108 (s : N.State) (i : N.Inputs) :
  R.v17108 (state s) (inputs i) = Zmod.unsigned (N.v17108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17108 s i)) at 1.
  unfold R.v17108, N.v17108.
  rewrite ?node_17103.
  rewrite ?node_17107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17109 (s : N.State) (i : N.Inputs) :
  R.v17109 (state s) (inputs i) = Zmod.unsigned (N.v17109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17109 s i)) at 1.
  unfold R.v17109, N.v17109.
  unfold R.v6, N.v6.
  rewrite ?node_17108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17110 (s : N.State) (i : N.Inputs) :
  R.v17110 (state s) (inputs i) = Zmod.unsigned (N.v17110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17110 s i)) at 1.
  unfold R.v17110, N.v17110.
  rewrite ?node_5423.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17111 (s : N.State) (i : N.Inputs) :
  R.v17111 (state s) (inputs i) = Zmod.unsigned (N.v17111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17111 s i)) at 1.
  unfold R.v17111, N.v17111.
  unfold R.v6, N.v6.
  rewrite ?node_5468.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17112 (s : N.State) (i : N.Inputs) :
  R.v17112 (state s) (inputs i) = Zmod.unsigned (N.v17112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17112 s i)) at 1.
  unfold R.v17112, N.v17112.
  rewrite ?node_17110.
  rewrite ?node_17111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17113 (s : N.State) (i : N.Inputs) :
  R.v17113 (state s) (inputs i) = Zmod.unsigned (N.v17113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17113 s i)) at 1.
  unfold R.v17113, N.v17113.
  rewrite ?node_17109.
  rewrite ?node_17112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17114 (s : N.State) (i : N.Inputs) :
  R.v17114 (state s) (inputs i) = Zmod.unsigned (N.v17114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17114 s i)) at 1.
  unfold R.v17114, N.v17114.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17115 (s : N.State) (i : N.Inputs) :
  R.v17115 (state s) (inputs i) = Zmod.unsigned (N.v17115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17115 s i)) at 1.
  unfold R.v17115, N.v17115.
  rewrite ?node_5427.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17116 (s : N.State) (i : N.Inputs) :
  R.v17116 (state s) (inputs i) = Zmod.unsigned (N.v17116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17116 s i)) at 1.
  unfold R.v17116, N.v17116.
  unfold R.v6, N.v6.
  rewrite !state_r82_nr_5F82.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r82_nr_5F82 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17117 (s : N.State) (i : N.Inputs) :
  R.v17117 (state s) (inputs i) = Zmod.unsigned (N.v17117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17117 s i)) at 1.
  unfold R.v17117, N.v17117.
  unfold R.v6, N.v6.
  rewrite ?node_5423.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17118 (s : N.State) (i : N.Inputs) :
  R.v17118 (state s) (inputs i) = Zmod.unsigned (N.v17118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17118 s i)) at 1.
  unfold R.v17118, N.v17118.
  rewrite ?node_17116.
  rewrite ?node_17117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17119 (s : N.State) (i : N.Inputs) :
  R.v17119 (state s) (inputs i) = Zmod.unsigned (N.v17119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17119 s i)) at 1.
  unfold R.v17119, N.v17119.
  unfold R.v16484, N.v16484.
  rewrite ?node_17118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17120 (s : N.State) (i : N.Inputs) :
  R.v17120 (state s) (inputs i) = Zmod.unsigned (N.v17120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17120 s i)) at 1.
  unfold R.v17120, N.v17120.
  rewrite ?node_17115.
  rewrite ?node_17119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17121 (s : N.State) (i : N.Inputs) :
  R.v17121 (state s) (inputs i) = Zmod.unsigned (N.v17121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17121 s i)) at 1.
  unfold R.v17121, N.v17121.
  unfold R.v6, N.v6.
  rewrite ?node_17120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17122 (s : N.State) (i : N.Inputs) :
  R.v17122 (state s) (inputs i) = Zmod.unsigned (N.v17122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17122 s i)) at 1.
  unfold R.v17122, N.v17122.
  rewrite ?node_5428.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17123 (s : N.State) (i : N.Inputs) :
  R.v17123 (state s) (inputs i) = Zmod.unsigned (N.v17123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17123 s i)) at 1.
  unfold R.v17123, N.v17123.
  unfold R.v6, N.v6.
  rewrite ?node_5482.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17124 (s : N.State) (i : N.Inputs) :
  R.v17124 (state s) (inputs i) = Zmod.unsigned (N.v17124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17124 s i)) at 1.
  unfold R.v17124, N.v17124.
  rewrite ?node_17122.
  rewrite ?node_17123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17125 (s : N.State) (i : N.Inputs) :
  R.v17125 (state s) (inputs i) = Zmod.unsigned (N.v17125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17125 s i)) at 1.
  unfold R.v17125, N.v17125.
  rewrite ?node_17121.
  rewrite ?node_17124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17126 (s : N.State) (i : N.Inputs) :
  R.v17126 (state s) (inputs i) = Zmod.unsigned (N.v17126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17126 s i)) at 1.
  unfold R.v17126, N.v17126.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17127 (s : N.State) (i : N.Inputs) :
  R.v17127 (state s) (inputs i) = Zmod.unsigned (N.v17127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17127 s i)) at 1.
  unfold R.v17127, N.v17127.
  rewrite ?node_5434.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17128 (s : N.State) (i : N.Inputs) :
  R.v17128 (state s) (inputs i) = Zmod.unsigned (N.v17128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17128 s i)) at 1.
  unfold R.v17128, N.v17128.
  unfold R.v16463, N.v16463.
  rewrite !state_r86_nr_5F86.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r86_nr_5F86 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17129 (s : N.State) (i : N.Inputs) :
  R.v17129 (state s) (inputs i) = Zmod.unsigned (N.v17129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17129 s i)) at 1.
  unfold R.v17129, N.v17129.
  unfold R.v16463, N.v16463.
  rewrite !state_r85_nr_5F85.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r85_nr_5F85 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17130 (s : N.State) (i : N.Inputs) :
  R.v17130 (state s) (inputs i) = Zmod.unsigned (N.v17130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17130 s i)) at 1.
  unfold R.v17130, N.v17130.
  unfold R.v6, N.v6.
  rewrite !state_r84_nr_5F84.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r84_nr_5F84 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17131 (s : N.State) (i : N.Inputs) :
  R.v17131 (state s) (inputs i) = Zmod.unsigned (N.v17131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17131 s i)) at 1.
  unfold R.v17131, N.v17131.
  unfold R.v6, N.v6.
  rewrite !state_r83_nr_5F83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r83_nr_5F83 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17132 (s : N.State) (i : N.Inputs) :
  R.v17132 (state s) (inputs i) = Zmod.unsigned (N.v17132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17132 s i)) at 1.
  unfold R.v17132, N.v17132.
  rewrite ?node_17130.
  rewrite ?node_17131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17133 (s : N.State) (i : N.Inputs) :
  R.v17133 (state s) (inputs i) = Zmod.unsigned (N.v17133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17133 s i)) at 1.
  unfold R.v17133, N.v17133.
  unfold R.v16484, N.v16484.
  rewrite ?node_17132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17134 (s : N.State) (i : N.Inputs) :
  R.v17134 (state s) (inputs i) = Zmod.unsigned (N.v17134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17134 s i)) at 1.
  unfold R.v17134, N.v17134.
  rewrite ?node_17127.
  rewrite ?node_17128.
  rewrite ?node_17129.
  rewrite ?node_17133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17135 (s : N.State) (i : N.Inputs) :
  R.v17135 (state s) (inputs i) = Zmod.unsigned (N.v17135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17135 s i)) at 1.
  unfold R.v17135, N.v17135.
  unfold R.v6, N.v6.
  rewrite ?node_17134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17136 (s : N.State) (i : N.Inputs) :
  R.v17136 (state s) (inputs i) = Zmod.unsigned (N.v17136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17136 s i)) at 1.
  unfold R.v17136, N.v17136.
  rewrite ?node_5435.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17137 (s : N.State) (i : N.Inputs) :
  R.v17137 (state s) (inputs i) = Zmod.unsigned (N.v17137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17137 s i)) at 1.
  unfold R.v17137, N.v17137.
  unfold R.v6, N.v6.
  rewrite ?node_5475.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17138 (s : N.State) (i : N.Inputs) :
  R.v17138 (state s) (inputs i) = Zmod.unsigned (N.v17138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17138 s i)) at 1.
  unfold R.v17138, N.v17138.
  unfold R.v6, N.v6.
  rewrite ?node_5490.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17139 (s : N.State) (i : N.Inputs) :
  R.v17139 (state s) (inputs i) = Zmod.unsigned (N.v17139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17139 s i)) at 1.
  unfold R.v17139, N.v17139.
  rewrite ?node_17136.
  rewrite ?node_17137.
  rewrite ?node_17138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17140 (s : N.State) (i : N.Inputs) :
  R.v17140 (state s) (inputs i) = Zmod.unsigned (N.v17140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17140 s i)) at 1.
  unfold R.v17140, N.v17140.
  rewrite ?node_17135.
  rewrite ?node_17139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17141 (s : N.State) (i : N.Inputs) :
  R.v17141 (state s) (inputs i) = Zmod.unsigned (N.v17141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17141 s i)) at 1.
  unfold R.v17141, N.v17141.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17142 (s : N.State) (i : N.Inputs) :
  R.v17142 (state s) (inputs i) = Zmod.unsigned (N.v17142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17142 s i)) at 1.
  unfold R.v17142, N.v17142.
  unfold R.v16463, N.v16463.
  rewrite !state_r85_nr_5F85.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r85_nr_5F85 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17143 (s : N.State) (i : N.Inputs) :
  R.v17143 (state s) (inputs i) = Zmod.unsigned (N.v17143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17143 s i)) at 1.
  unfold R.v17143, N.v17143.
  unfold R.v6, N.v6.
  rewrite !state_r84_nr_5F84.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r84_nr_5F84 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17144 (s : N.State) (i : N.Inputs) :
  R.v17144 (state s) (inputs i) = Zmod.unsigned (N.v17144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17144 s i)) at 1.
  unfold R.v17144, N.v17144.
  unfold R.v6, N.v6.
  rewrite !state_r83_nr_5F83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r83_nr_5F83 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17145 (s : N.State) (i : N.Inputs) :
  R.v17145 (state s) (inputs i) = Zmod.unsigned (N.v17145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17145 s i)) at 1.
  unfold R.v17145, N.v17145.
  rewrite ?node_17143.
  rewrite ?node_17144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17146 (s : N.State) (i : N.Inputs) :
  R.v17146 (state s) (inputs i) = Zmod.unsigned (N.v17146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17146 s i)) at 1.
  unfold R.v17146, N.v17146.
  unfold R.v16484, N.v16484.
  rewrite ?node_17145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17147 (s : N.State) (i : N.Inputs) :
  R.v17147 (state s) (inputs i) = Zmod.unsigned (N.v17147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17147 s i)) at 1.
  unfold R.v17147, N.v17147.
  rewrite ?node_17142.
  rewrite ?node_17146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17148 (s : N.State) (i : N.Inputs) :
  R.v17148 (state s) (inputs i) = Zmod.unsigned (N.v17148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17148 s i)) at 1.
  unfold R.v17148, N.v17148.
  unfold R.v6, N.v6.
  rewrite ?node_17147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17149 (s : N.State) (i : N.Inputs) :
  R.v17149 (state s) (inputs i) = Zmod.unsigned (N.v17149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17149 s i)) at 1.
  unfold R.v17149, N.v17149.
  rewrite ?node_5430.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17150 (s : N.State) (i : N.Inputs) :
  R.v17150 (state s) (inputs i) = Zmod.unsigned (N.v17150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17150 s i)) at 1.
  unfold R.v17150, N.v17150.
  unfold R.v6, N.v6.
  rewrite ?node_5475.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17151 (s : N.State) (i : N.Inputs) :
  R.v17151 (state s) (inputs i) = Zmod.unsigned (N.v17151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17151 s i)) at 1.
  unfold R.v17151, N.v17151.
  rewrite ?node_17149.
  rewrite ?node_17150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17152 (s : N.State) (i : N.Inputs) :
  R.v17152 (state s) (inputs i) = Zmod.unsigned (N.v17152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17152 s i)) at 1.
  unfold R.v17152, N.v17152.
  rewrite ?node_17148.
  rewrite ?node_17151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17153 (s : N.State) (i : N.Inputs) :
  R.v17153 (state s) (inputs i) = Zmod.unsigned (N.v17153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17153 s i)) at 1.
  unfold R.v17153, N.v17153.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17154 (s : N.State) (i : N.Inputs) :
  R.v17154 (state s) (inputs i) = Zmod.unsigned (N.v17154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17154 s i)) at 1.
  unfold R.v17154, N.v17154.
  rewrite ?node_5434.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17155 (s : N.State) (i : N.Inputs) :
  R.v17155 (state s) (inputs i) = Zmod.unsigned (N.v17155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17155 s i)) at 1.
  unfold R.v17155, N.v17155.
  unfold R.v6, N.v6.
  rewrite !state_r86_nr_5F86.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r86_nr_5F86 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17156 (s : N.State) (i : N.Inputs) :
  R.v17156 (state s) (inputs i) = Zmod.unsigned (N.v17156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17156 s i)) at 1.
  unfold R.v17156, N.v17156.
  unfold R.v6, N.v6.
  rewrite ?node_5430.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17157 (s : N.State) (i : N.Inputs) :
  R.v17157 (state s) (inputs i) = Zmod.unsigned (N.v17157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17157 s i)) at 1.
  unfold R.v17157, N.v17157.
  rewrite ?node_17155.
  rewrite ?node_17156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17158 (s : N.State) (i : N.Inputs) :
  R.v17158 (state s) (inputs i) = Zmod.unsigned (N.v17158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17158 s i)) at 1.
  unfold R.v17158, N.v17158.
  unfold R.v16484, N.v16484.
  rewrite ?node_17157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17159 (s : N.State) (i : N.Inputs) :
  R.v17159 (state s) (inputs i) = Zmod.unsigned (N.v17159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17159 s i)) at 1.
  unfold R.v17159, N.v17159.
  rewrite ?node_17154.
  rewrite ?node_17158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17160 (s : N.State) (i : N.Inputs) :
  R.v17160 (state s) (inputs i) = Zmod.unsigned (N.v17160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17160 s i)) at 1.
  unfold R.v17160, N.v17160.
  unfold R.v6, N.v6.
  rewrite ?node_17159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17161 (s : N.State) (i : N.Inputs) :
  R.v17161 (state s) (inputs i) = Zmod.unsigned (N.v17161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17161 s i)) at 1.
  unfold R.v17161, N.v17161.
  rewrite ?node_5435.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17162 (s : N.State) (i : N.Inputs) :
  R.v17162 (state s) (inputs i) = Zmod.unsigned (N.v17162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17162 s i)) at 1.
  unfold R.v17162, N.v17162.
  unfold R.v6, N.v6.
  rewrite ?node_5490.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17163 (s : N.State) (i : N.Inputs) :
  R.v17163 (state s) (inputs i) = Zmod.unsigned (N.v17163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17163 s i)) at 1.
  unfold R.v17163, N.v17163.
  rewrite ?node_17161.
  rewrite ?node_17162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17164 (s : N.State) (i : N.Inputs) :
  R.v17164 (state s) (inputs i) = Zmod.unsigned (N.v17164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17164 s i)) at 1.
  unfold R.v17164, N.v17164.
  rewrite ?node_17160.
  rewrite ?node_17163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17165 (s : N.State) (i : N.Inputs) :
  R.v17165 (state s) (inputs i) = Zmod.unsigned (N.v17165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17165 s i)) at 1.
  unfold R.v17165, N.v17165.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17166 (s : N.State) (i : N.Inputs) :
  R.v17166 (state s) (inputs i) = Zmod.unsigned (N.v17166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17166 s i)) at 1.
  unfold R.v17166, N.v17166.
  rewrite ?node_5468.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17167 (s : N.State) (i : N.Inputs) :
  R.v17167 (state s) (inputs i) = Zmod.unsigned (N.v17167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17167 s i)) at 1.
  unfold R.v17167, N.v17167.
  unfold R.v16463, N.v16463.
  rewrite !state_r91_nr_5F91.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r91_nr_5F91 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17168 (s : N.State) (i : N.Inputs) :
  R.v17168 (state s) (inputs i) = Zmod.unsigned (N.v17168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17168 s i)) at 1.
  unfold R.v17168, N.v17168.
  unfold R.v16463, N.v16463.
  rewrite !state_r90_nr_5F90.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r90_nr_5F90 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17169 (s : N.State) (i : N.Inputs) :
  R.v17169 (state s) (inputs i) = Zmod.unsigned (N.v17169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17169 s i)) at 1.
  unfold R.v17169, N.v17169.
  unfold R.v6, N.v6.
  rewrite !state_r89_nr_5F89.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r89_nr_5F89 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17170 (s : N.State) (i : N.Inputs) :
  R.v17170 (state s) (inputs i) = Zmod.unsigned (N.v17170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17170 s i)) at 1.
  unfold R.v17170, N.v17170.
  unfold R.v6, N.v6.
  rewrite !state_r88_nr_5F88.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r88_nr_5F88 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17171 (s : N.State) (i : N.Inputs) :
  R.v17171 (state s) (inputs i) = Zmod.unsigned (N.v17171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17171 s i)) at 1.
  unfold R.v17171, N.v17171.
  rewrite ?node_17169.
  rewrite ?node_17170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17172 (s : N.State) (i : N.Inputs) :
  R.v17172 (state s) (inputs i) = Zmod.unsigned (N.v17172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17172 s i)) at 1.
  unfold R.v17172, N.v17172.
  unfold R.v16484, N.v16484.
  rewrite ?node_17171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17173 (s : N.State) (i : N.Inputs) :
  R.v17173 (state s) (inputs i) = Zmod.unsigned (N.v17173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17173 s i)) at 1.
  unfold R.v17173, N.v17173.
  rewrite ?node_17166.
  rewrite ?node_17167.
  rewrite ?node_17168.
  rewrite ?node_17172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17174 (s : N.State) (i : N.Inputs) :
  R.v17174 (state s) (inputs i) = Zmod.unsigned (N.v17174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17174 s i)) at 1.
  unfold R.v17174, N.v17174.
  unfold R.v6, N.v6.
  rewrite ?node_17173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17175 (s : N.State) (i : N.Inputs) :
  R.v17175 (state s) (inputs i) = Zmod.unsigned (N.v17175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17175 s i)) at 1.
  unfold R.v17175, N.v17175.
  rewrite ?node_5469.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17176 (s : N.State) (i : N.Inputs) :
  R.v17176 (state s) (inputs i) = Zmod.unsigned (N.v17176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17176 s i)) at 1.
  unfold R.v17176, N.v17176.
  unfold R.v6, N.v6.
  rewrite ?node_5510.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17177 (s : N.State) (i : N.Inputs) :
  R.v17177 (state s) (inputs i) = Zmod.unsigned (N.v17177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17177 s i)) at 1.
  unfold R.v17177, N.v17177.
  unfold R.v6, N.v6.
  rewrite ?node_5524.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17178 (s : N.State) (i : N.Inputs) :
  R.v17178 (state s) (inputs i) = Zmod.unsigned (N.v17178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17178 s i)) at 1.
  unfold R.v17178, N.v17178.
  rewrite ?node_17175.
  rewrite ?node_17176.
  rewrite ?node_17177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17179 (s : N.State) (i : N.Inputs) :
  R.v17179 (state s) (inputs i) = Zmod.unsigned (N.v17179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17179 s i)) at 1.
  unfold R.v17179, N.v17179.
  rewrite ?node_17174.
  rewrite ?node_17178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17180 (s : N.State) (i : N.Inputs) :
  R.v17180 (state s) (inputs i) = Zmod.unsigned (N.v17180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17180 s i)) at 1.
  unfold R.v17180, N.v17180.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17181 (s : N.State) (i : N.Inputs) :
  R.v17181 (state s) (inputs i) = Zmod.unsigned (N.v17181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17181 s i)) at 1.
  unfold R.v17181, N.v17181.
  unfold R.v16463, N.v16463.
  rewrite !state_r90_nr_5F90.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r90_nr_5F90 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17182 (s : N.State) (i : N.Inputs) :
  R.v17182 (state s) (inputs i) = Zmod.unsigned (N.v17182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17182 s i)) at 1.
  unfold R.v17182, N.v17182.
  unfold R.v6, N.v6.
  rewrite !state_r89_nr_5F89.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r89_nr_5F89 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17183 (s : N.State) (i : N.Inputs) :
  R.v17183 (state s) (inputs i) = Zmod.unsigned (N.v17183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17183 s i)) at 1.
  unfold R.v17183, N.v17183.
  unfold R.v6, N.v6.
  rewrite !state_r88_nr_5F88.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r88_nr_5F88 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17184 (s : N.State) (i : N.Inputs) :
  R.v17184 (state s) (inputs i) = Zmod.unsigned (N.v17184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17184 s i)) at 1.
  unfold R.v17184, N.v17184.
  rewrite ?node_17182.
  rewrite ?node_17183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17185 (s : N.State) (i : N.Inputs) :
  R.v17185 (state s) (inputs i) = Zmod.unsigned (N.v17185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17185 s i)) at 1.
  unfold R.v17185, N.v17185.
  unfold R.v16484, N.v16484.
  rewrite ?node_17184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17186 (s : N.State) (i : N.Inputs) :
  R.v17186 (state s) (inputs i) = Zmod.unsigned (N.v17186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17186 s i)) at 1.
  unfold R.v17186, N.v17186.
  rewrite ?node_17181.
  rewrite ?node_17185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17187 (s : N.State) (i : N.Inputs) :
  R.v17187 (state s) (inputs i) = Zmod.unsigned (N.v17187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17187 s i)) at 1.
  unfold R.v17187, N.v17187.
  unfold R.v6, N.v6.
  rewrite ?node_17186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17188 (s : N.State) (i : N.Inputs) :
  R.v17188 (state s) (inputs i) = Zmod.unsigned (N.v17188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17188 s i)) at 1.
  unfold R.v17188, N.v17188.
  rewrite ?node_5464.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17189 (s : N.State) (i : N.Inputs) :
  R.v17189 (state s) (inputs i) = Zmod.unsigned (N.v17189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17189 s i)) at 1.
  unfold R.v17189, N.v17189.
  unfold R.v6, N.v6.
  rewrite ?node_5510.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17190 (s : N.State) (i : N.Inputs) :
  R.v17190 (state s) (inputs i) = Zmod.unsigned (N.v17190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17190 s i)) at 1.
  unfold R.v17190, N.v17190.
  rewrite ?node_17188.
  rewrite ?node_17189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17191 (s : N.State) (i : N.Inputs) :
  R.v17191 (state s) (inputs i) = Zmod.unsigned (N.v17191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17191 s i)) at 1.
  unfold R.v17191, N.v17191.
  rewrite ?node_17187.
  rewrite ?node_17190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17192 (s : N.State) (i : N.Inputs) :
  R.v17192 (state s) (inputs i) = Zmod.unsigned (N.v17192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17192 s i)) at 1.
  unfold R.v17192, N.v17192.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17193 (s : N.State) (i : N.Inputs) :
  R.v17193 (state s) (inputs i) = Zmod.unsigned (N.v17193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17193 s i)) at 1.
  unfold R.v17193, N.v17193.
  rewrite ?node_5468.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17194 (s : N.State) (i : N.Inputs) :
  R.v17194 (state s) (inputs i) = Zmod.unsigned (N.v17194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17194 s i)) at 1.
  unfold R.v17194, N.v17194.
  unfold R.v6, N.v6.
  rewrite !state_r91_nr_5F91.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r91_nr_5F91 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17195 (s : N.State) (i : N.Inputs) :
  R.v17195 (state s) (inputs i) = Zmod.unsigned (N.v17195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17195 s i)) at 1.
  unfold R.v17195, N.v17195.
  unfold R.v6, N.v6.
  rewrite ?node_5464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17196 (s : N.State) (i : N.Inputs) :
  R.v17196 (state s) (inputs i) = Zmod.unsigned (N.v17196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17196 s i)) at 1.
  unfold R.v17196, N.v17196.
  rewrite ?node_17194.
  rewrite ?node_17195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17197 (s : N.State) (i : N.Inputs) :
  R.v17197 (state s) (inputs i) = Zmod.unsigned (N.v17197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17197 s i)) at 1.
  unfold R.v17197, N.v17197.
  unfold R.v16484, N.v16484.
  rewrite ?node_17196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17198 (s : N.State) (i : N.Inputs) :
  R.v17198 (state s) (inputs i) = Zmod.unsigned (N.v17198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17198 s i)) at 1.
  unfold R.v17198, N.v17198.
  rewrite ?node_17193.
  rewrite ?node_17197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17199 (s : N.State) (i : N.Inputs) :
  R.v17199 (state s) (inputs i) = Zmod.unsigned (N.v17199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17199 s i)) at 1.
  unfold R.v17199, N.v17199.
  unfold R.v6, N.v6.
  rewrite ?node_17198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17200 (s : N.State) (i : N.Inputs) :
  R.v17200 (state s) (inputs i) = Zmod.unsigned (N.v17200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17200 s i)) at 1.
  unfold R.v17200, N.v17200.
  rewrite ?node_5469.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17201 (s : N.State) (i : N.Inputs) :
  R.v17201 (state s) (inputs i) = Zmod.unsigned (N.v17201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17201 s i)) at 1.
  unfold R.v17201, N.v17201.
  unfold R.v6, N.v6.
  rewrite ?node_5524.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17202 (s : N.State) (i : N.Inputs) :
  R.v17202 (state s) (inputs i) = Zmod.unsigned (N.v17202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17202 s i)) at 1.
  unfold R.v17202, N.v17202.
  rewrite ?node_17200.
  rewrite ?node_17201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17203 (s : N.State) (i : N.Inputs) :
  R.v17203 (state s) (inputs i) = Zmod.unsigned (N.v17203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17203 s i)) at 1.
  unfold R.v17203, N.v17203.
  rewrite ?node_17199.
  rewrite ?node_17202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17204 (s : N.State) (i : N.Inputs) :
  R.v17204 (state s) (inputs i) = Zmod.unsigned (N.v17204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17204 s i)) at 1.
  unfold R.v17204, N.v17204.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17205 (s : N.State) (i : N.Inputs) :
  R.v17205 (state s) (inputs i) = Zmod.unsigned (N.v17205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17205 s i)) at 1.
  unfold R.v17205, N.v17205.
  rewrite ?node_5475.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17206 (s : N.State) (i : N.Inputs) :
  R.v17206 (state s) (inputs i) = Zmod.unsigned (N.v17206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17206 s i)) at 1.
  unfold R.v17206, N.v17206.
  unfold R.v16463, N.v16463.
  rewrite !state_r95_nr_5F95.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r95_nr_5F95 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17207 (s : N.State) (i : N.Inputs) :
  R.v17207 (state s) (inputs i) = Zmod.unsigned (N.v17207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17207 s i)) at 1.
  unfold R.v17207, N.v17207.
  unfold R.v16463, N.v16463.
  rewrite !state_r94_nr_5F94.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r94_nr_5F94 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17208 (s : N.State) (i : N.Inputs) :
  R.v17208 (state s) (inputs i) = Zmod.unsigned (N.v17208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17208 s i)) at 1.
  unfold R.v17208, N.v17208.
  unfold R.v6, N.v6.
  rewrite !state_r93_nr_5F93.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r93_nr_5F93 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17209 (s : N.State) (i : N.Inputs) :
  R.v17209 (state s) (inputs i) = Zmod.unsigned (N.v17209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17209 s i)) at 1.
  unfold R.v17209, N.v17209.
  unfold R.v6, N.v6.
  rewrite !state_r92_nr_5F92.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r92_nr_5F92 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17210 (s : N.State) (i : N.Inputs) :
  R.v17210 (state s) (inputs i) = Zmod.unsigned (N.v17210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17210 s i)) at 1.
  unfold R.v17210, N.v17210.
  rewrite ?node_17208.
  rewrite ?node_17209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17211 (s : N.State) (i : N.Inputs) :
  R.v17211 (state s) (inputs i) = Zmod.unsigned (N.v17211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17211 s i)) at 1.
  unfold R.v17211, N.v17211.
  unfold R.v16484, N.v16484.
  rewrite ?node_17210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17212 (s : N.State) (i : N.Inputs) :
  R.v17212 (state s) (inputs i) = Zmod.unsigned (N.v17212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17212 s i)) at 1.
  unfold R.v17212, N.v17212.
  rewrite ?node_17205.
  rewrite ?node_17206.
  rewrite ?node_17207.
  rewrite ?node_17211.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17213 (s : N.State) (i : N.Inputs) :
  R.v17213 (state s) (inputs i) = Zmod.unsigned (N.v17213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17213 s i)) at 1.
  unfold R.v17213, N.v17213.
  unfold R.v6, N.v6.
  rewrite ?node_17212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17214 (s : N.State) (i : N.Inputs) :
  R.v17214 (state s) (inputs i) = Zmod.unsigned (N.v17214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17214 s i)) at 1.
  unfold R.v17214, N.v17214.
  rewrite ?node_5476.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17215 (s : N.State) (i : N.Inputs) :
  R.v17215 (state s) (inputs i) = Zmod.unsigned (N.v17215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17215 s i)) at 1.
  unfold R.v17215, N.v17215.
  unfold R.v6, N.v6.
  rewrite ?node_5517.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17216 (s : N.State) (i : N.Inputs) :
  R.v17216 (state s) (inputs i) = Zmod.unsigned (N.v17216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17216 s i)) at 1.
  unfold R.v17216, N.v17216.
  unfold R.v6, N.v6.
  rewrite ?node_5532.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17217 (s : N.State) (i : N.Inputs) :
  R.v17217 (state s) (inputs i) = Zmod.unsigned (N.v17217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17217 s i)) at 1.
  unfold R.v17217, N.v17217.
  rewrite ?node_17214.
  rewrite ?node_17215.
  rewrite ?node_17216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17218 (s : N.State) (i : N.Inputs) :
  R.v17218 (state s) (inputs i) = Zmod.unsigned (N.v17218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17218 s i)) at 1.
  unfold R.v17218, N.v17218.
  rewrite ?node_17213.
  rewrite ?node_17217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17219 (s : N.State) (i : N.Inputs) :
  R.v17219 (state s) (inputs i) = Zmod.unsigned (N.v17219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17219 s i)) at 1.
  unfold R.v17219, N.v17219.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17220 (s : N.State) (i : N.Inputs) :
  R.v17220 (state s) (inputs i) = Zmod.unsigned (N.v17220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17220 s i)) at 1.
  unfold R.v17220, N.v17220.
  unfold R.v16463, N.v16463.
  rewrite !state_r94_nr_5F94.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r94_nr_5F94 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17221 (s : N.State) (i : N.Inputs) :
  R.v17221 (state s) (inputs i) = Zmod.unsigned (N.v17221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17221 s i)) at 1.
  unfold R.v17221, N.v17221.
  unfold R.v6, N.v6.
  rewrite !state_r93_nr_5F93.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r93_nr_5F93 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17222 (s : N.State) (i : N.Inputs) :
  R.v17222 (state s) (inputs i) = Zmod.unsigned (N.v17222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17222 s i)) at 1.
  unfold R.v17222, N.v17222.
  unfold R.v6, N.v6.
  rewrite !state_r92_nr_5F92.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r92_nr_5F92 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17223 (s : N.State) (i : N.Inputs) :
  R.v17223 (state s) (inputs i) = Zmod.unsigned (N.v17223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17223 s i)) at 1.
  unfold R.v17223, N.v17223.
  rewrite ?node_17221.
  rewrite ?node_17222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17224 (s : N.State) (i : N.Inputs) :
  R.v17224 (state s) (inputs i) = Zmod.unsigned (N.v17224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17224 s i)) at 1.
  unfold R.v17224, N.v17224.
  unfold R.v16484, N.v16484.
  rewrite ?node_17223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17225 (s : N.State) (i : N.Inputs) :
  R.v17225 (state s) (inputs i) = Zmod.unsigned (N.v17225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17225 s i)) at 1.
  unfold R.v17225, N.v17225.
  rewrite ?node_17220.
  rewrite ?node_17224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17226 (s : N.State) (i : N.Inputs) :
  R.v17226 (state s) (inputs i) = Zmod.unsigned (N.v17226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17226 s i)) at 1.
  unfold R.v17226, N.v17226.
  unfold R.v6, N.v6.
  rewrite ?node_17225.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17227 (s : N.State) (i : N.Inputs) :
  R.v17227 (state s) (inputs i) = Zmod.unsigned (N.v17227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17227 s i)) at 1.
  unfold R.v17227, N.v17227.
  rewrite ?node_5471.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17228 (s : N.State) (i : N.Inputs) :
  R.v17228 (state s) (inputs i) = Zmod.unsigned (N.v17228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17228 s i)) at 1.
  unfold R.v17228, N.v17228.
  unfold R.v6, N.v6.
  rewrite ?node_5517.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17229 (s : N.State) (i : N.Inputs) :
  R.v17229 (state s) (inputs i) = Zmod.unsigned (N.v17229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17229 s i)) at 1.
  unfold R.v17229, N.v17229.
  rewrite ?node_17227.
  rewrite ?node_17228.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17230 (s : N.State) (i : N.Inputs) :
  R.v17230 (state s) (inputs i) = Zmod.unsigned (N.v17230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17230 s i)) at 1.
  unfold R.v17230, N.v17230.
  rewrite ?node_17226.
  rewrite ?node_17229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17231 (s : N.State) (i : N.Inputs) :
  R.v17231 (state s) (inputs i) = Zmod.unsigned (N.v17231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17231 s i)) at 1.
  unfold R.v17231, N.v17231.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17232 (s : N.State) (i : N.Inputs) :
  R.v17232 (state s) (inputs i) = Zmod.unsigned (N.v17232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17232 s i)) at 1.
  unfold R.v17232, N.v17232.
  rewrite ?node_5475.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17233 (s : N.State) (i : N.Inputs) :
  R.v17233 (state s) (inputs i) = Zmod.unsigned (N.v17233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17233 s i)) at 1.
  unfold R.v17233, N.v17233.
  unfold R.v6, N.v6.
  rewrite !state_r95_nr_5F95.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r95_nr_5F95 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17234 (s : N.State) (i : N.Inputs) :
  R.v17234 (state s) (inputs i) = Zmod.unsigned (N.v17234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17234 s i)) at 1.
  unfold R.v17234, N.v17234.
  unfold R.v6, N.v6.
  rewrite ?node_5471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17235 (s : N.State) (i : N.Inputs) :
  R.v17235 (state s) (inputs i) = Zmod.unsigned (N.v17235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17235 s i)) at 1.
  unfold R.v17235, N.v17235.
  rewrite ?node_17233.
  rewrite ?node_17234.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17236 (s : N.State) (i : N.Inputs) :
  R.v17236 (state s) (inputs i) = Zmod.unsigned (N.v17236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17236 s i)) at 1.
  unfold R.v17236, N.v17236.
  unfold R.v16484, N.v16484.
  rewrite ?node_17235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17237 (s : N.State) (i : N.Inputs) :
  R.v17237 (state s) (inputs i) = Zmod.unsigned (N.v17237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17237 s i)) at 1.
  unfold R.v17237, N.v17237.
  rewrite ?node_17232.
  rewrite ?node_17236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17238 (s : N.State) (i : N.Inputs) :
  R.v17238 (state s) (inputs i) = Zmod.unsigned (N.v17238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17238 s i)) at 1.
  unfold R.v17238, N.v17238.
  unfold R.v6, N.v6.
  rewrite ?node_17237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17239 (s : N.State) (i : N.Inputs) :
  R.v17239 (state s) (inputs i) = Zmod.unsigned (N.v17239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17239 s i)) at 1.
  unfold R.v17239, N.v17239.
  rewrite ?node_5476.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17240 (s : N.State) (i : N.Inputs) :
  R.v17240 (state s) (inputs i) = Zmod.unsigned (N.v17240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17240 s i)) at 1.
  unfold R.v17240, N.v17240.
  unfold R.v6, N.v6.
  rewrite ?node_5532.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17241 (s : N.State) (i : N.Inputs) :
  R.v17241 (state s) (inputs i) = Zmod.unsigned (N.v17241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17241 s i)) at 1.
  unfold R.v17241, N.v17241.
  rewrite ?node_17239.
  rewrite ?node_17240.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17242 (s : N.State) (i : N.Inputs) :
  R.v17242 (state s) (inputs i) = Zmod.unsigned (N.v17242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17242 s i)) at 1.
  unfold R.v17242, N.v17242.
  rewrite ?node_17238.
  rewrite ?node_17241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17243 (s : N.State) (i : N.Inputs) :
  R.v17243 (state s) (inputs i) = Zmod.unsigned (N.v17243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17243 s i)) at 1.
  unfold R.v17243, N.v17243.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17244 (s : N.State) (i : N.Inputs) :
  R.v17244 (state s) (inputs i) = Zmod.unsigned (N.v17244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17244 s i)) at 1.
  unfold R.v17244, N.v17244.
  unfold R.v6, N.v6.
  rewrite !state_r97_nr_5F97.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r97_nr_5F97 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17245 (s : N.State) (i : N.Inputs) :
  R.v17245 (state s) (inputs i) = Zmod.unsigned (N.v17245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17245 s i)) at 1.
  unfold R.v17245, N.v17245.
  unfold R.v6, N.v6.
  rewrite !state_r96_nr_5F96.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r96_nr_5F96 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17246 (s : N.State) (i : N.Inputs) :
  R.v17246 (state s) (inputs i) = Zmod.unsigned (N.v17246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17246 s i)) at 1.
  unfold R.v17246, N.v17246.
  rewrite ?node_17244.
  rewrite ?node_17245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17247 (s : N.State) (i : N.Inputs) :
  R.v17247 (state s) (inputs i) = Zmod.unsigned (N.v17247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17247 s i)) at 1.
  unfold R.v17247, N.v17247.
  unfold R.v16463, N.v16463.
  rewrite ?node_17246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17248 (s : N.State) (i : N.Inputs) :
  R.v17248 (state s) (inputs i) = Zmod.unsigned (N.v17248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17248 s i)) at 1.
  unfold R.v17248, N.v17248.
  rewrite ?node_5478.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17249 (s : N.State) (i : N.Inputs) :
  R.v17249 (state s) (inputs i) = Zmod.unsigned (N.v17249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17249 s i)) at 1.
  unfold R.v17249, N.v17249.
  unfold R.v6, N.v6.
  rewrite ?node_5533.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17250 (s : N.State) (i : N.Inputs) :
  R.v17250 (state s) (inputs i) = Zmod.unsigned (N.v17250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17250 s i)) at 1.
  unfold R.v17250, N.v17250.
  rewrite ?node_17248.
  rewrite ?node_17249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17251 (s : N.State) (i : N.Inputs) :
  R.v17251 (state s) (inputs i) = Zmod.unsigned (N.v17251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17251 s i)) at 1.
  unfold R.v17251, N.v17251.
  rewrite ?node_17247.
  rewrite ?node_17250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17252 (s : N.State) (i : N.Inputs) :
  R.v17252 (state s) (inputs i) = Zmod.unsigned (N.v17252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17252 s i)) at 1.
  unfold R.v17252, N.v17252.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17253 (s : N.State) (i : N.Inputs) :
  R.v17253 (state s) (inputs i) = Zmod.unsigned (N.v17253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17253 s i)) at 1.
  unfold R.v17253, N.v17253.
  rewrite ?node_5510.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17254 (s : N.State) (i : N.Inputs) :
  R.v17254 (state s) (inputs i) = Zmod.unsigned (N.v17254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17254 s i)) at 1.
  unfold R.v17254, N.v17254.
  unfold R.v16463, N.v16463.
  rewrite !state_r101_nr_5F101.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r101_nr_5F101 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17255 (s : N.State) (i : N.Inputs) :
  R.v17255 (state s) (inputs i) = Zmod.unsigned (N.v17255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17255 s i)) at 1.
  unfold R.v17255, N.v17255.
  unfold R.v16463, N.v16463.
  rewrite !state_r100_nr_5F100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r100_nr_5F100 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17256 (s : N.State) (i : N.Inputs) :
  R.v17256 (state s) (inputs i) = Zmod.unsigned (N.v17256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17256 s i)) at 1.
  unfold R.v17256, N.v17256.
  unfold R.v6, N.v6.
  rewrite !state_r99_nr_5F99.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r99_nr_5F99 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17257 (s : N.State) (i : N.Inputs) :
  R.v17257 (state s) (inputs i) = Zmod.unsigned (N.v17257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17257 s i)) at 1.
  unfold R.v17257, N.v17257.
  unfold R.v6, N.v6.
  rewrite !state_r98_nr_5F98.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r98_nr_5F98 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17258 (s : N.State) (i : N.Inputs) :
  R.v17258 (state s) (inputs i) = Zmod.unsigned (N.v17258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17258 s i)) at 1.
  unfold R.v17258, N.v17258.
  rewrite ?node_17256.
  rewrite ?node_17257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17259 (s : N.State) (i : N.Inputs) :
  R.v17259 (state s) (inputs i) = Zmod.unsigned (N.v17259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17259 s i)) at 1.
  unfold R.v17259, N.v17259.
  unfold R.v16484, N.v16484.
  rewrite ?node_17258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17260 (s : N.State) (i : N.Inputs) :
  R.v17260 (state s) (inputs i) = Zmod.unsigned (N.v17260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17260 s i)) at 1.
  unfold R.v17260, N.v17260.
  rewrite ?node_17253.
  rewrite ?node_17254.
  rewrite ?node_17255.
  rewrite ?node_17259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17261 (s : N.State) (i : N.Inputs) :
  R.v17261 (state s) (inputs i) = Zmod.unsigned (N.v17261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17261 s i)) at 1.
  unfold R.v17261, N.v17261.
  unfold R.v6, N.v6.
  rewrite ?node_17260.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17262 (s : N.State) (i : N.Inputs) :
  R.v17262 (state s) (inputs i) = Zmod.unsigned (N.v17262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17262 s i)) at 1.
  unfold R.v17262, N.v17262.
  rewrite ?node_5511.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17263 (s : N.State) (i : N.Inputs) :
  R.v17263 (state s) (inputs i) = Zmod.unsigned (N.v17263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17263 s i)) at 1.
  unfold R.v17263, N.v17263.
  unfold R.v6, N.v6.
  rewrite ?node_5554.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17264 (s : N.State) (i : N.Inputs) :
  R.v17264 (state s) (inputs i) = Zmod.unsigned (N.v17264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17264 s i)) at 1.
  unfold R.v17264, N.v17264.
  unfold R.v6, N.v6.
  rewrite ?node_5569.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17265 (s : N.State) (i : N.Inputs) :
  R.v17265 (state s) (inputs i) = Zmod.unsigned (N.v17265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17265 s i)) at 1.
  unfold R.v17265, N.v17265.
  rewrite ?node_17262.
  rewrite ?node_17263.
  rewrite ?node_17264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17266 (s : N.State) (i : N.Inputs) :
  R.v17266 (state s) (inputs i) = Zmod.unsigned (N.v17266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17266 s i)) at 1.
  unfold R.v17266, N.v17266.
  rewrite ?node_17261.
  rewrite ?node_17265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17267 (s : N.State) (i : N.Inputs) :
  R.v17267 (state s) (inputs i) = Zmod.unsigned (N.v17267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17267 s i)) at 1.
  unfold R.v17267, N.v17267.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17268 (s : N.State) (i : N.Inputs) :
  R.v17268 (state s) (inputs i) = Zmod.unsigned (N.v17268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17268 s i)) at 1.
  unfold R.v17268, N.v17268.
  unfold R.v16463, N.v16463.
  rewrite !state_r100_nr_5F100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r100_nr_5F100 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17269 (s : N.State) (i : N.Inputs) :
  R.v17269 (state s) (inputs i) = Zmod.unsigned (N.v17269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17269 s i)) at 1.
  unfold R.v17269, N.v17269.
  unfold R.v6, N.v6.
  rewrite !state_r99_nr_5F99.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r99_nr_5F99 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17270 (s : N.State) (i : N.Inputs) :
  R.v17270 (state s) (inputs i) = Zmod.unsigned (N.v17270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17270 s i)) at 1.
  unfold R.v17270, N.v17270.
  unfold R.v6, N.v6.
  rewrite !state_r98_nr_5F98.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r98_nr_5F98 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17271 (s : N.State) (i : N.Inputs) :
  R.v17271 (state s) (inputs i) = Zmod.unsigned (N.v17271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17271 s i)) at 1.
  unfold R.v17271, N.v17271.
  rewrite ?node_17269.
  rewrite ?node_17270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17272 (s : N.State) (i : N.Inputs) :
  R.v17272 (state s) (inputs i) = Zmod.unsigned (N.v17272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17272 s i)) at 1.
  unfold R.v17272, N.v17272.
  unfold R.v16484, N.v16484.
  rewrite ?node_17271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17273 (s : N.State) (i : N.Inputs) :
  R.v17273 (state s) (inputs i) = Zmod.unsigned (N.v17273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17273 s i)) at 1.
  unfold R.v17273, N.v17273.
  rewrite ?node_17268.
  rewrite ?node_17272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17274 (s : N.State) (i : N.Inputs) :
  R.v17274 (state s) (inputs i) = Zmod.unsigned (N.v17274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17274 s i)) at 1.
  unfold R.v17274, N.v17274.
  unfold R.v6, N.v6.
  rewrite ?node_17273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17275 (s : N.State) (i : N.Inputs) :
  R.v17275 (state s) (inputs i) = Zmod.unsigned (N.v17275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17275 s i)) at 1.
  unfold R.v17275, N.v17275.
  rewrite ?node_5506.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17276 (s : N.State) (i : N.Inputs) :
  R.v17276 (state s) (inputs i) = Zmod.unsigned (N.v17276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17276 s i)) at 1.
  unfold R.v17276, N.v17276.
  unfold R.v6, N.v6.
  rewrite ?node_5554.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17277 (s : N.State) (i : N.Inputs) :
  R.v17277 (state s) (inputs i) = Zmod.unsigned (N.v17277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17277 s i)) at 1.
  unfold R.v17277, N.v17277.
  rewrite ?node_17275.
  rewrite ?node_17276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17278 (s : N.State) (i : N.Inputs) :
  R.v17278 (state s) (inputs i) = Zmod.unsigned (N.v17278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17278 s i)) at 1.
  unfold R.v17278, N.v17278.
  rewrite ?node_17274.
  rewrite ?node_17277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17279 (s : N.State) (i : N.Inputs) :
  R.v17279 (state s) (inputs i) = Zmod.unsigned (N.v17279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17279 s i)) at 1.
  unfold R.v17279, N.v17279.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17280 (s : N.State) (i : N.Inputs) :
  R.v17280 (state s) (inputs i) = Zmod.unsigned (N.v17280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17280 s i)) at 1.
  unfold R.v17280, N.v17280.
  rewrite ?node_5510.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17281 (s : N.State) (i : N.Inputs) :
  R.v17281 (state s) (inputs i) = Zmod.unsigned (N.v17281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17281 s i)) at 1.
  unfold R.v17281, N.v17281.
  unfold R.v6, N.v6.
  rewrite !state_r101_nr_5F101.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r101_nr_5F101 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17282 (s : N.State) (i : N.Inputs) :
  R.v17282 (state s) (inputs i) = Zmod.unsigned (N.v17282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17282 s i)) at 1.
  unfold R.v17282, N.v17282.
  unfold R.v6, N.v6.
  rewrite ?node_5506.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17283 (s : N.State) (i : N.Inputs) :
  R.v17283 (state s) (inputs i) = Zmod.unsigned (N.v17283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17283 s i)) at 1.
  unfold R.v17283, N.v17283.
  rewrite ?node_17281.
  rewrite ?node_17282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17284 (s : N.State) (i : N.Inputs) :
  R.v17284 (state s) (inputs i) = Zmod.unsigned (N.v17284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17284 s i)) at 1.
  unfold R.v17284, N.v17284.
  unfold R.v16484, N.v16484.
  rewrite ?node_17283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17285 (s : N.State) (i : N.Inputs) :
  R.v17285 (state s) (inputs i) = Zmod.unsigned (N.v17285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17285 s i)) at 1.
  unfold R.v17285, N.v17285.
  rewrite ?node_17280.
  rewrite ?node_17284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17286 (s : N.State) (i : N.Inputs) :
  R.v17286 (state s) (inputs i) = Zmod.unsigned (N.v17286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17286 s i)) at 1.
  unfold R.v17286, N.v17286.
  unfold R.v6, N.v6.
  rewrite ?node_17285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17287 (s : N.State) (i : N.Inputs) :
  R.v17287 (state s) (inputs i) = Zmod.unsigned (N.v17287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17287 s i)) at 1.
  unfold R.v17287, N.v17287.
  rewrite ?node_5511.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17288 (s : N.State) (i : N.Inputs) :
  R.v17288 (state s) (inputs i) = Zmod.unsigned (N.v17288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17288 s i)) at 1.
  unfold R.v17288, N.v17288.
  unfold R.v6, N.v6.
  rewrite ?node_5569.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17289 (s : N.State) (i : N.Inputs) :
  R.v17289 (state s) (inputs i) = Zmod.unsigned (N.v17289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17289 s i)) at 1.
  unfold R.v17289, N.v17289.
  rewrite ?node_17287.
  rewrite ?node_17288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17290 (s : N.State) (i : N.Inputs) :
  R.v17290 (state s) (inputs i) = Zmod.unsigned (N.v17290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17290 s i)) at 1.
  unfold R.v17290, N.v17290.
  rewrite ?node_17286.
  rewrite ?node_17289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17291 (s : N.State) (i : N.Inputs) :
  R.v17291 (state s) (inputs i) = Zmod.unsigned (N.v17291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17291 s i)) at 1.
  unfold R.v17291, N.v17291.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17292 (s : N.State) (i : N.Inputs) :
  R.v17292 (state s) (inputs i) = Zmod.unsigned (N.v17292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17292 s i)) at 1.
  unfold R.v17292, N.v17292.
  rewrite ?node_5517.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17293 (s : N.State) (i : N.Inputs) :
  R.v17293 (state s) (inputs i) = Zmod.unsigned (N.v17293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17293 s i)) at 1.
  unfold R.v17293, N.v17293.
  unfold R.v16463, N.v16463.
  rewrite !state_r105_nr_5F105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r105_nr_5F105 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17294 (s : N.State) (i : N.Inputs) :
  R.v17294 (state s) (inputs i) = Zmod.unsigned (N.v17294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17294 s i)) at 1.
  unfold R.v17294, N.v17294.
  unfold R.v16463, N.v16463.
  rewrite !state_r104_nr_5F104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r104_nr_5F104 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17295 (s : N.State) (i : N.Inputs) :
  R.v17295 (state s) (inputs i) = Zmod.unsigned (N.v17295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17295 s i)) at 1.
  unfold R.v17295, N.v17295.
  unfold R.v6, N.v6.
  rewrite !state_r103_nr_5F103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r103_nr_5F103 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17296 (s : N.State) (i : N.Inputs) :
  R.v17296 (state s) (inputs i) = Zmod.unsigned (N.v17296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17296 s i)) at 1.
  unfold R.v17296, N.v17296.
  unfold R.v6, N.v6.
  rewrite !state_r102_nr_5F102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r102_nr_5F102 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17297 (s : N.State) (i : N.Inputs) :
  R.v17297 (state s) (inputs i) = Zmod.unsigned (N.v17297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17297 s i)) at 1.
  unfold R.v17297, N.v17297.
  rewrite ?node_17295.
  rewrite ?node_17296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17298 (s : N.State) (i : N.Inputs) :
  R.v17298 (state s) (inputs i) = Zmod.unsigned (N.v17298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17298 s i)) at 1.
  unfold R.v17298, N.v17298.
  unfold R.v16484, N.v16484.
  rewrite ?node_17297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17299 (s : N.State) (i : N.Inputs) :
  R.v17299 (state s) (inputs i) = Zmod.unsigned (N.v17299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17299 s i)) at 1.
  unfold R.v17299, N.v17299.
  rewrite ?node_17292.
  rewrite ?node_17293.
  rewrite ?node_17294.
  rewrite ?node_17298.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17300 (s : N.State) (i : N.Inputs) :
  R.v17300 (state s) (inputs i) = Zmod.unsigned (N.v17300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17300 s i)) at 1.
  unfold R.v17300, N.v17300.
  unfold R.v6, N.v6.
  rewrite ?node_17299.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17301 (s : N.State) (i : N.Inputs) :
  R.v17301 (state s) (inputs i) = Zmod.unsigned (N.v17301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17301 s i)) at 1.
  unfold R.v17301, N.v17301.
  rewrite ?node_5518.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17302 (s : N.State) (i : N.Inputs) :
  R.v17302 (state s) (inputs i) = Zmod.unsigned (N.v17302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17302 s i)) at 1.
  unfold R.v17302, N.v17302.
  unfold R.v6, N.v6.
  rewrite ?node_5561.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17303 (s : N.State) (i : N.Inputs) :
  R.v17303 (state s) (inputs i) = Zmod.unsigned (N.v17303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17303 s i)) at 1.
  unfold R.v17303, N.v17303.
  unfold R.v6, N.v6.
  rewrite ?node_5577.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17304 (s : N.State) (i : N.Inputs) :
  R.v17304 (state s) (inputs i) = Zmod.unsigned (N.v17304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17304 s i)) at 1.
  unfold R.v17304, N.v17304.
  rewrite ?node_17301.
  rewrite ?node_17302.
  rewrite ?node_17303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17305 (s : N.State) (i : N.Inputs) :
  R.v17305 (state s) (inputs i) = Zmod.unsigned (N.v17305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17305 s i)) at 1.
  unfold R.v17305, N.v17305.
  rewrite ?node_17300.
  rewrite ?node_17304.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17306 (s : N.State) (i : N.Inputs) :
  R.v17306 (state s) (inputs i) = Zmod.unsigned (N.v17306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17306 s i)) at 1.
  unfold R.v17306, N.v17306.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17307 (s : N.State) (i : N.Inputs) :
  R.v17307 (state s) (inputs i) = Zmod.unsigned (N.v17307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17307 s i)) at 1.
  unfold R.v17307, N.v17307.
  unfold R.v16463, N.v16463.
  rewrite !state_r104_nr_5F104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r104_nr_5F104 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17308 (s : N.State) (i : N.Inputs) :
  R.v17308 (state s) (inputs i) = Zmod.unsigned (N.v17308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17308 s i)) at 1.
  unfold R.v17308, N.v17308.
  unfold R.v6, N.v6.
  rewrite !state_r103_nr_5F103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r103_nr_5F103 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17309 (s : N.State) (i : N.Inputs) :
  R.v17309 (state s) (inputs i) = Zmod.unsigned (N.v17309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17309 s i)) at 1.
  unfold R.v17309, N.v17309.
  unfold R.v6, N.v6.
  rewrite !state_r102_nr_5F102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r102_nr_5F102 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17310 (s : N.State) (i : N.Inputs) :
  R.v17310 (state s) (inputs i) = Zmod.unsigned (N.v17310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17310 s i)) at 1.
  unfold R.v17310, N.v17310.
  rewrite ?node_17308.
  rewrite ?node_17309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17311 (s : N.State) (i : N.Inputs) :
  R.v17311 (state s) (inputs i) = Zmod.unsigned (N.v17311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17311 s i)) at 1.
  unfold R.v17311, N.v17311.
  unfold R.v16484, N.v16484.
  rewrite ?node_17310.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17312 (s : N.State) (i : N.Inputs) :
  R.v17312 (state s) (inputs i) = Zmod.unsigned (N.v17312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17312 s i)) at 1.
  unfold R.v17312, N.v17312.
  rewrite ?node_17307.
  rewrite ?node_17311.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17313 (s : N.State) (i : N.Inputs) :
  R.v17313 (state s) (inputs i) = Zmod.unsigned (N.v17313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17313 s i)) at 1.
  unfold R.v17313, N.v17313.
  unfold R.v6, N.v6.
  rewrite ?node_17312.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17314 (s : N.State) (i : N.Inputs) :
  R.v17314 (state s) (inputs i) = Zmod.unsigned (N.v17314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17314 s i)) at 1.
  unfold R.v17314, N.v17314.
  rewrite ?node_5513.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17315 (s : N.State) (i : N.Inputs) :
  R.v17315 (state s) (inputs i) = Zmod.unsigned (N.v17315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17315 s i)) at 1.
  unfold R.v17315, N.v17315.
  unfold R.v6, N.v6.
  rewrite ?node_5561.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17316 (s : N.State) (i : N.Inputs) :
  R.v17316 (state s) (inputs i) = Zmod.unsigned (N.v17316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17316 s i)) at 1.
  unfold R.v17316, N.v17316.
  rewrite ?node_17314.
  rewrite ?node_17315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17317 (s : N.State) (i : N.Inputs) :
  R.v17317 (state s) (inputs i) = Zmod.unsigned (N.v17317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17317 s i)) at 1.
  unfold R.v17317, N.v17317.
  rewrite ?node_17313.
  rewrite ?node_17316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17318 (s : N.State) (i : N.Inputs) :
  R.v17318 (state s) (inputs i) = Zmod.unsigned (N.v17318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17318 s i)) at 1.
  unfold R.v17318, N.v17318.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17319 (s : N.State) (i : N.Inputs) :
  R.v17319 (state s) (inputs i) = Zmod.unsigned (N.v17319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17319 s i)) at 1.
  unfold R.v17319, N.v17319.
  rewrite ?node_5517.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17320 (s : N.State) (i : N.Inputs) :
  R.v17320 (state s) (inputs i) = Zmod.unsigned (N.v17320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17320 s i)) at 1.
  unfold R.v17320, N.v17320.
  unfold R.v6, N.v6.
  rewrite !state_r105_nr_5F105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r105_nr_5F105 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17321 (s : N.State) (i : N.Inputs) :
  R.v17321 (state s) (inputs i) = Zmod.unsigned (N.v17321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17321 s i)) at 1.
  unfold R.v17321, N.v17321.
  unfold R.v6, N.v6.
  rewrite ?node_5513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17322 (s : N.State) (i : N.Inputs) :
  R.v17322 (state s) (inputs i) = Zmod.unsigned (N.v17322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17322 s i)) at 1.
  unfold R.v17322, N.v17322.
  rewrite ?node_17320.
  rewrite ?node_17321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17323 (s : N.State) (i : N.Inputs) :
  R.v17323 (state s) (inputs i) = Zmod.unsigned (N.v17323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17323 s i)) at 1.
  unfold R.v17323, N.v17323.
  unfold R.v16484, N.v16484.
  rewrite ?node_17322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17324 (s : N.State) (i : N.Inputs) :
  R.v17324 (state s) (inputs i) = Zmod.unsigned (N.v17324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17324 s i)) at 1.
  unfold R.v17324, N.v17324.
  rewrite ?node_17319.
  rewrite ?node_17323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17325 (s : N.State) (i : N.Inputs) :
  R.v17325 (state s) (inputs i) = Zmod.unsigned (N.v17325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17325 s i)) at 1.
  unfold R.v17325, N.v17325.
  unfold R.v6, N.v6.
  rewrite ?node_17324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17326 (s : N.State) (i : N.Inputs) :
  R.v17326 (state s) (inputs i) = Zmod.unsigned (N.v17326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17326 s i)) at 1.
  unfold R.v17326, N.v17326.
  rewrite ?node_5518.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17327 (s : N.State) (i : N.Inputs) :
  R.v17327 (state s) (inputs i) = Zmod.unsigned (N.v17327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17327 s i)) at 1.
  unfold R.v17327, N.v17327.
  unfold R.v6, N.v6.
  rewrite ?node_5577.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17328 (s : N.State) (i : N.Inputs) :
  R.v17328 (state s) (inputs i) = Zmod.unsigned (N.v17328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17328 s i)) at 1.
  unfold R.v17328, N.v17328.
  rewrite ?node_17326.
  rewrite ?node_17327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17329 (s : N.State) (i : N.Inputs) :
  R.v17329 (state s) (inputs i) = Zmod.unsigned (N.v17329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17329 s i)) at 1.
  unfold R.v17329, N.v17329.
  rewrite ?node_17325.
  rewrite ?node_17328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17330 (s : N.State) (i : N.Inputs) :
  R.v17330 (state s) (inputs i) = Zmod.unsigned (N.v17330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17330 s i)) at 1.
  unfold R.v17330, N.v17330.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17331 (s : N.State) (i : N.Inputs) :
  R.v17331 (state s) (inputs i) = Zmod.unsigned (N.v17331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17331 s i)) at 1.
  unfold R.v17331, N.v17331.
  unfold R.v6, N.v6.
  rewrite !state_r107_nr_5F107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r107_nr_5F107 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17332 (s : N.State) (i : N.Inputs) :
  R.v17332 (state s) (inputs i) = Zmod.unsigned (N.v17332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17332 s i)) at 1.
  unfold R.v17332, N.v17332.
  unfold R.v6, N.v6.
  rewrite !state_r106_nr_5F106.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r106_nr_5F106 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17333 (s : N.State) (i : N.Inputs) :
  R.v17333 (state s) (inputs i) = Zmod.unsigned (N.v17333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17333 s i)) at 1.
  unfold R.v17333, N.v17333.
  rewrite ?node_17331.
  rewrite ?node_17332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17334 (s : N.State) (i : N.Inputs) :
  R.v17334 (state s) (inputs i) = Zmod.unsigned (N.v17334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17334 s i)) at 1.
  unfold R.v17334, N.v17334.
  unfold R.v16463, N.v16463.
  rewrite ?node_17333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17335 (s : N.State) (i : N.Inputs) :
  R.v17335 (state s) (inputs i) = Zmod.unsigned (N.v17335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17335 s i)) at 1.
  unfold R.v17335, N.v17335.
  rewrite ?node_5520.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17336 (s : N.State) (i : N.Inputs) :
  R.v17336 (state s) (inputs i) = Zmod.unsigned (N.v17336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17336 s i)) at 1.
  unfold R.v17336, N.v17336.
  unfold R.v6, N.v6.
  rewrite ?node_5578.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17337 (s : N.State) (i : N.Inputs) :
  R.v17337 (state s) (inputs i) = Zmod.unsigned (N.v17337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17337 s i)) at 1.
  unfold R.v17337, N.v17337.
  rewrite ?node_17335.
  rewrite ?node_17336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17338 (s : N.State) (i : N.Inputs) :
  R.v17338 (state s) (inputs i) = Zmod.unsigned (N.v17338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17338 s i)) at 1.
  unfold R.v17338, N.v17338.
  rewrite ?node_17334.
  rewrite ?node_17337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17339 (s : N.State) (i : N.Inputs) :
  R.v17339 (state s) (inputs i) = Zmod.unsigned (N.v17339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17339 s i)) at 1.
  unfold R.v17339, N.v17339.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17340 (s : N.State) (i : N.Inputs) :
  R.v17340 (state s) (inputs i) = Zmod.unsigned (N.v17340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17340 s i)) at 1.
  unfold R.v17340, N.v17340.
  rewrite ?node_5554.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17341 (s : N.State) (i : N.Inputs) :
  R.v17341 (state s) (inputs i) = Zmod.unsigned (N.v17341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17341 s i)) at 1.
  unfold R.v17341, N.v17341.
  unfold R.v16463, N.v16463.
  rewrite !state_r111_nr_5F111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r111_nr_5F111 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17342 (s : N.State) (i : N.Inputs) :
  R.v17342 (state s) (inputs i) = Zmod.unsigned (N.v17342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17342 s i)) at 1.
  unfold R.v17342, N.v17342.
  unfold R.v16463, N.v16463.
  rewrite !state_r110_nr_5F110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r110_nr_5F110 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17343 (s : N.State) (i : N.Inputs) :
  R.v17343 (state s) (inputs i) = Zmod.unsigned (N.v17343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17343 s i)) at 1.
  unfold R.v17343, N.v17343.
  unfold R.v6, N.v6.
  rewrite !state_r109_nr_5F109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r109_nr_5F109 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17344 (s : N.State) (i : N.Inputs) :
  R.v17344 (state s) (inputs i) = Zmod.unsigned (N.v17344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17344 s i)) at 1.
  unfold R.v17344, N.v17344.
  unfold R.v6, N.v6.
  rewrite !state_r108_nr_5F108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r108_nr_5F108 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17345 (s : N.State) (i : N.Inputs) :
  R.v17345 (state s) (inputs i) = Zmod.unsigned (N.v17345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17345 s i)) at 1.
  unfold R.v17345, N.v17345.
  rewrite ?node_17343.
  rewrite ?node_17344.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17346 (s : N.State) (i : N.Inputs) :
  R.v17346 (state s) (inputs i) = Zmod.unsigned (N.v17346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17346 s i)) at 1.
  unfold R.v17346, N.v17346.
  unfold R.v16484, N.v16484.
  rewrite ?node_17345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17347 (s : N.State) (i : N.Inputs) :
  R.v17347 (state s) (inputs i) = Zmod.unsigned (N.v17347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17347 s i)) at 1.
  unfold R.v17347, N.v17347.
  rewrite ?node_17340.
  rewrite ?node_17341.
  rewrite ?node_17342.
  rewrite ?node_17346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17348 (s : N.State) (i : N.Inputs) :
  R.v17348 (state s) (inputs i) = Zmod.unsigned (N.v17348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17348 s i)) at 1.
  unfold R.v17348, N.v17348.
  unfold R.v6, N.v6.
  rewrite ?node_17347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17349 (s : N.State) (i : N.Inputs) :
  R.v17349 (state s) (inputs i) = Zmod.unsigned (N.v17349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17349 s i)) at 1.
  unfold R.v17349, N.v17349.
  rewrite ?node_5555.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17350 (s : N.State) (i : N.Inputs) :
  R.v17350 (state s) (inputs i) = Zmod.unsigned (N.v17350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17350 s i)) at 1.
  unfold R.v17350, N.v17350.
  unfold R.v6, N.v6.
  rewrite ?node_5601.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17351 (s : N.State) (i : N.Inputs) :
  R.v17351 (state s) (inputs i) = Zmod.unsigned (N.v17351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17351 s i)) at 1.
  unfold R.v17351, N.v17351.
  unfold R.v6, N.v6.
  rewrite ?node_5616.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17352 (s : N.State) (i : N.Inputs) :
  R.v17352 (state s) (inputs i) = Zmod.unsigned (N.v17352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17352 s i)) at 1.
  unfold R.v17352, N.v17352.
  rewrite ?node_17349.
  rewrite ?node_17350.
  rewrite ?node_17351.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17353 (s : N.State) (i : N.Inputs) :
  R.v17353 (state s) (inputs i) = Zmod.unsigned (N.v17353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17353 s i)) at 1.
  unfold R.v17353, N.v17353.
  rewrite ?node_17348.
  rewrite ?node_17352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17354 (s : N.State) (i : N.Inputs) :
  R.v17354 (state s) (inputs i) = Zmod.unsigned (N.v17354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17354 s i)) at 1.
  unfold R.v17354, N.v17354.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17355 (s : N.State) (i : N.Inputs) :
  R.v17355 (state s) (inputs i) = Zmod.unsigned (N.v17355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17355 s i)) at 1.
  unfold R.v17355, N.v17355.
  unfold R.v16463, N.v16463.
  rewrite !state_r110_nr_5F110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r110_nr_5F110 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17356 (s : N.State) (i : N.Inputs) :
  R.v17356 (state s) (inputs i) = Zmod.unsigned (N.v17356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17356 s i)) at 1.
  unfold R.v17356, N.v17356.
  unfold R.v6, N.v6.
  rewrite !state_r109_nr_5F109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r109_nr_5F109 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17357 (s : N.State) (i : N.Inputs) :
  R.v17357 (state s) (inputs i) = Zmod.unsigned (N.v17357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17357 s i)) at 1.
  unfold R.v17357, N.v17357.
  unfold R.v6, N.v6.
  rewrite !state_r108_nr_5F108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r108_nr_5F108 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17358 (s : N.State) (i : N.Inputs) :
  R.v17358 (state s) (inputs i) = Zmod.unsigned (N.v17358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17358 s i)) at 1.
  unfold R.v17358, N.v17358.
  rewrite ?node_17356.
  rewrite ?node_17357.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17359 (s : N.State) (i : N.Inputs) :
  R.v17359 (state s) (inputs i) = Zmod.unsigned (N.v17359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17359 s i)) at 1.
  unfold R.v17359, N.v17359.
  unfold R.v16484, N.v16484.
  rewrite ?node_17358.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17360 (s : N.State) (i : N.Inputs) :
  R.v17360 (state s) (inputs i) = Zmod.unsigned (N.v17360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17360 s i)) at 1.
  unfold R.v17360, N.v17360.
  rewrite ?node_17355.
  rewrite ?node_17359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17361 (s : N.State) (i : N.Inputs) :
  R.v17361 (state s) (inputs i) = Zmod.unsigned (N.v17361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17361 s i)) at 1.
  unfold R.v17361, N.v17361.
  unfold R.v6, N.v6.
  rewrite ?node_17360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17362 (s : N.State) (i : N.Inputs) :
  R.v17362 (state s) (inputs i) = Zmod.unsigned (N.v17362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17362 s i)) at 1.
  unfold R.v17362, N.v17362.
  rewrite ?node_5550.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17363 (s : N.State) (i : N.Inputs) :
  R.v17363 (state s) (inputs i) = Zmod.unsigned (N.v17363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17363 s i)) at 1.
  unfold R.v17363, N.v17363.
  unfold R.v6, N.v6.
  rewrite ?node_5601.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17364 (s : N.State) (i : N.Inputs) :
  R.v17364 (state s) (inputs i) = Zmod.unsigned (N.v17364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17364 s i)) at 1.
  unfold R.v17364, N.v17364.
  rewrite ?node_17362.
  rewrite ?node_17363.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17365 (s : N.State) (i : N.Inputs) :
  R.v17365 (state s) (inputs i) = Zmod.unsigned (N.v17365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17365 s i)) at 1.
  unfold R.v17365, N.v17365.
  rewrite ?node_17361.
  rewrite ?node_17364.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17366 (s : N.State) (i : N.Inputs) :
  R.v17366 (state s) (inputs i) = Zmod.unsigned (N.v17366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17366 s i)) at 1.
  unfold R.v17366, N.v17366.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17367 (s : N.State) (i : N.Inputs) :
  R.v17367 (state s) (inputs i) = Zmod.unsigned (N.v17367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17367 s i)) at 1.
  unfold R.v17367, N.v17367.
  rewrite ?node_5554.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17368 (s : N.State) (i : N.Inputs) :
  R.v17368 (state s) (inputs i) = Zmod.unsigned (N.v17368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17368 s i)) at 1.
  unfold R.v17368, N.v17368.
  unfold R.v6, N.v6.
  rewrite !state_r111_nr_5F111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r111_nr_5F111 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17369 (s : N.State) (i : N.Inputs) :
  R.v17369 (state s) (inputs i) = Zmod.unsigned (N.v17369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17369 s i)) at 1.
  unfold R.v17369, N.v17369.
  unfold R.v6, N.v6.
  rewrite ?node_5550.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17370 (s : N.State) (i : N.Inputs) :
  R.v17370 (state s) (inputs i) = Zmod.unsigned (N.v17370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17370 s i)) at 1.
  unfold R.v17370, N.v17370.
  rewrite ?node_17368.
  rewrite ?node_17369.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17371 (s : N.State) (i : N.Inputs) :
  R.v17371 (state s) (inputs i) = Zmod.unsigned (N.v17371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17371 s i)) at 1.
  unfold R.v17371, N.v17371.
  unfold R.v16484, N.v16484.
  rewrite ?node_17370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17372 (s : N.State) (i : N.Inputs) :
  R.v17372 (state s) (inputs i) = Zmod.unsigned (N.v17372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17372 s i)) at 1.
  unfold R.v17372, N.v17372.
  rewrite ?node_17367.
  rewrite ?node_17371.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17373 (s : N.State) (i : N.Inputs) :
  R.v17373 (state s) (inputs i) = Zmod.unsigned (N.v17373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17373 s i)) at 1.
  unfold R.v17373, N.v17373.
  unfold R.v6, N.v6.
  rewrite ?node_17372.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17374 (s : N.State) (i : N.Inputs) :
  R.v17374 (state s) (inputs i) = Zmod.unsigned (N.v17374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17374 s i)) at 1.
  unfold R.v17374, N.v17374.
  rewrite ?node_5555.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17375 (s : N.State) (i : N.Inputs) :
  R.v17375 (state s) (inputs i) = Zmod.unsigned (N.v17375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17375 s i)) at 1.
  unfold R.v17375, N.v17375.
  unfold R.v6, N.v6.
  rewrite ?node_5616.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17376 (s : N.State) (i : N.Inputs) :
  R.v17376 (state s) (inputs i) = Zmod.unsigned (N.v17376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17376 s i)) at 1.
  unfold R.v17376, N.v17376.
  rewrite ?node_17374.
  rewrite ?node_17375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17377 (s : N.State) (i : N.Inputs) :
  R.v17377 (state s) (inputs i) = Zmod.unsigned (N.v17377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17377 s i)) at 1.
  unfold R.v17377, N.v17377.
  rewrite ?node_17373.
  rewrite ?node_17376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17378 (s : N.State) (i : N.Inputs) :
  R.v17378 (state s) (inputs i) = Zmod.unsigned (N.v17378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17378 s i)) at 1.
  unfold R.v17378, N.v17378.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17379 (s : N.State) (i : N.Inputs) :
  R.v17379 (state s) (inputs i) = Zmod.unsigned (N.v17379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17379 s i)) at 1.
  unfold R.v17379, N.v17379.
  rewrite ?node_5561.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17380 (s : N.State) (i : N.Inputs) :
  R.v17380 (state s) (inputs i) = Zmod.unsigned (N.v17380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17380 s i)) at 1.
  unfold R.v17380, N.v17380.
  unfold R.v16463, N.v16463.
  rewrite !state_r115_nr_5F115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r115_nr_5F115 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17381 (s : N.State) (i : N.Inputs) :
  R.v17381 (state s) (inputs i) = Zmod.unsigned (N.v17381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17381 s i)) at 1.
  unfold R.v17381, N.v17381.
  unfold R.v16463, N.v16463.
  rewrite !state_r114_nr_5F114.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r114_nr_5F114 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17382 (s : N.State) (i : N.Inputs) :
  R.v17382 (state s) (inputs i) = Zmod.unsigned (N.v17382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17382 s i)) at 1.
  unfold R.v17382, N.v17382.
  unfold R.v6, N.v6.
  rewrite !state_r113_nr_5F113.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r113_nr_5F113 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17383 (s : N.State) (i : N.Inputs) :
  R.v17383 (state s) (inputs i) = Zmod.unsigned (N.v17383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17383 s i)) at 1.
  unfold R.v17383, N.v17383.
  unfold R.v6, N.v6.
  rewrite !state_r112_nr_5F112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r112_nr_5F112 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17384 (s : N.State) (i : N.Inputs) :
  R.v17384 (state s) (inputs i) = Zmod.unsigned (N.v17384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17384 s i)) at 1.
  unfold R.v17384, N.v17384.
  rewrite ?node_17382.
  rewrite ?node_17383.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17385 (s : N.State) (i : N.Inputs) :
  R.v17385 (state s) (inputs i) = Zmod.unsigned (N.v17385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17385 s i)) at 1.
  unfold R.v17385, N.v17385.
  unfold R.v16484, N.v16484.
  rewrite ?node_17384.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17386 (s : N.State) (i : N.Inputs) :
  R.v17386 (state s) (inputs i) = Zmod.unsigned (N.v17386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17386 s i)) at 1.
  unfold R.v17386, N.v17386.
  rewrite ?node_17379.
  rewrite ?node_17380.
  rewrite ?node_17381.
  rewrite ?node_17385.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17387 (s : N.State) (i : N.Inputs) :
  R.v17387 (state s) (inputs i) = Zmod.unsigned (N.v17387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17387 s i)) at 1.
  unfold R.v17387, N.v17387.
  unfold R.v6, N.v6.
  rewrite ?node_17386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17388 (s : N.State) (i : N.Inputs) :
  R.v17388 (state s) (inputs i) = Zmod.unsigned (N.v17388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17388 s i)) at 1.
  unfold R.v17388, N.v17388.
  rewrite ?node_5562.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17389 (s : N.State) (i : N.Inputs) :
  R.v17389 (state s) (inputs i) = Zmod.unsigned (N.v17389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17389 s i)) at 1.
  unfold R.v17389, N.v17389.
  unfold R.v6, N.v6.
  rewrite ?node_5608.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17390 (s : N.State) (i : N.Inputs) :
  R.v17390 (state s) (inputs i) = Zmod.unsigned (N.v17390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17390 s i)) at 1.
  unfold R.v17390, N.v17390.
  unfold R.v6, N.v6.
  rewrite ?node_5624.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17391 (s : N.State) (i : N.Inputs) :
  R.v17391 (state s) (inputs i) = Zmod.unsigned (N.v17391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17391 s i)) at 1.
  unfold R.v17391, N.v17391.
  rewrite ?node_17388.
  rewrite ?node_17389.
  rewrite ?node_17390.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17392 (s : N.State) (i : N.Inputs) :
  R.v17392 (state s) (inputs i) = Zmod.unsigned (N.v17392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17392 s i)) at 1.
  unfold R.v17392, N.v17392.
  rewrite ?node_17387.
  rewrite ?node_17391.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17393 (s : N.State) (i : N.Inputs) :
  R.v17393 (state s) (inputs i) = Zmod.unsigned (N.v17393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17393 s i)) at 1.
  unfold R.v17393, N.v17393.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17394 (s : N.State) (i : N.Inputs) :
  R.v17394 (state s) (inputs i) = Zmod.unsigned (N.v17394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17394 s i)) at 1.
  unfold R.v17394, N.v17394.
  unfold R.v16463, N.v16463.
  rewrite !state_r114_nr_5F114.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r114_nr_5F114 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17395 (s : N.State) (i : N.Inputs) :
  R.v17395 (state s) (inputs i) = Zmod.unsigned (N.v17395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17395 s i)) at 1.
  unfold R.v17395, N.v17395.
  unfold R.v6, N.v6.
  rewrite !state_r113_nr_5F113.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r113_nr_5F113 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17396 (s : N.State) (i : N.Inputs) :
  R.v17396 (state s) (inputs i) = Zmod.unsigned (N.v17396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17396 s i)) at 1.
  unfold R.v17396, N.v17396.
  unfold R.v6, N.v6.
  rewrite !state_r112_nr_5F112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r112_nr_5F112 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17397 (s : N.State) (i : N.Inputs) :
  R.v17397 (state s) (inputs i) = Zmod.unsigned (N.v17397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17397 s i)) at 1.
  unfold R.v17397, N.v17397.
  rewrite ?node_17395.
  rewrite ?node_17396.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17398 (s : N.State) (i : N.Inputs) :
  R.v17398 (state s) (inputs i) = Zmod.unsigned (N.v17398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17398 s i)) at 1.
  unfold R.v17398, N.v17398.
  unfold R.v16484, N.v16484.
  rewrite ?node_17397.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17399 (s : N.State) (i : N.Inputs) :
  R.v17399 (state s) (inputs i) = Zmod.unsigned (N.v17399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17399 s i)) at 1.
  unfold R.v17399, N.v17399.
  rewrite ?node_17394.
  rewrite ?node_17398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17400 (s : N.State) (i : N.Inputs) :
  R.v17400 (state s) (inputs i) = Zmod.unsigned (N.v17400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17400 s i)) at 1.
  unfold R.v17400, N.v17400.
  unfold R.v6, N.v6.
  rewrite ?node_17399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17401 (s : N.State) (i : N.Inputs) :
  R.v17401 (state s) (inputs i) = Zmod.unsigned (N.v17401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17401 s i)) at 1.
  unfold R.v17401, N.v17401.
  rewrite ?node_5557.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17402 (s : N.State) (i : N.Inputs) :
  R.v17402 (state s) (inputs i) = Zmod.unsigned (N.v17402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17402 s i)) at 1.
  unfold R.v17402, N.v17402.
  unfold R.v6, N.v6.
  rewrite ?node_5608.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17403 (s : N.State) (i : N.Inputs) :
  R.v17403 (state s) (inputs i) = Zmod.unsigned (N.v17403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17403 s i)) at 1.
  unfold R.v17403, N.v17403.
  rewrite ?node_17401.
  rewrite ?node_17402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17404 (s : N.State) (i : N.Inputs) :
  R.v17404 (state s) (inputs i) = Zmod.unsigned (N.v17404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17404 s i)) at 1.
  unfold R.v17404, N.v17404.
  rewrite ?node_17400.
  rewrite ?node_17403.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17405 (s : N.State) (i : N.Inputs) :
  R.v17405 (state s) (inputs i) = Zmod.unsigned (N.v17405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17405 s i)) at 1.
  unfold R.v17405, N.v17405.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17406 (s : N.State) (i : N.Inputs) :
  R.v17406 (state s) (inputs i) = Zmod.unsigned (N.v17406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17406 s i)) at 1.
  unfold R.v17406, N.v17406.
  rewrite ?node_5561.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17407 (s : N.State) (i : N.Inputs) :
  R.v17407 (state s) (inputs i) = Zmod.unsigned (N.v17407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17407 s i)) at 1.
  unfold R.v17407, N.v17407.
  unfold R.v6, N.v6.
  rewrite !state_r115_nr_5F115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r115_nr_5F115 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17408 (s : N.State) (i : N.Inputs) :
  R.v17408 (state s) (inputs i) = Zmod.unsigned (N.v17408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17408 s i)) at 1.
  unfold R.v17408, N.v17408.
  unfold R.v6, N.v6.
  rewrite ?node_5557.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17409 (s : N.State) (i : N.Inputs) :
  R.v17409 (state s) (inputs i) = Zmod.unsigned (N.v17409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17409 s i)) at 1.
  unfold R.v17409, N.v17409.
  rewrite ?node_17407.
  rewrite ?node_17408.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17410 (s : N.State) (i : N.Inputs) :
  R.v17410 (state s) (inputs i) = Zmod.unsigned (N.v17410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17410 s i)) at 1.
  unfold R.v17410, N.v17410.
  unfold R.v16484, N.v16484.
  rewrite ?node_17409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17411 (s : N.State) (i : N.Inputs) :
  R.v17411 (state s) (inputs i) = Zmod.unsigned (N.v17411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17411 s i)) at 1.
  unfold R.v17411, N.v17411.
  rewrite ?node_17406.
  rewrite ?node_17410.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17412 (s : N.State) (i : N.Inputs) :
  R.v17412 (state s) (inputs i) = Zmod.unsigned (N.v17412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17412 s i)) at 1.
  unfold R.v17412, N.v17412.
  unfold R.v6, N.v6.
  rewrite ?node_17411.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17413 (s : N.State) (i : N.Inputs) :
  R.v17413 (state s) (inputs i) = Zmod.unsigned (N.v17413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17413 s i)) at 1.
  unfold R.v17413, N.v17413.
  rewrite ?node_5562.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17414 (s : N.State) (i : N.Inputs) :
  R.v17414 (state s) (inputs i) = Zmod.unsigned (N.v17414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17414 s i)) at 1.
  unfold R.v17414, N.v17414.
  unfold R.v6, N.v6.
  rewrite ?node_5624.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17415 (s : N.State) (i : N.Inputs) :
  R.v17415 (state s) (inputs i) = Zmod.unsigned (N.v17415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17415 s i)) at 1.
  unfold R.v17415, N.v17415.
  rewrite ?node_17413.
  rewrite ?node_17414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17416 (s : N.State) (i : N.Inputs) :
  R.v17416 (state s) (inputs i) = Zmod.unsigned (N.v17416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17416 s i)) at 1.
  unfold R.v17416, N.v17416.
  rewrite ?node_17412.
  rewrite ?node_17415.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17417 (s : N.State) (i : N.Inputs) :
  R.v17417 (state s) (inputs i) = Zmod.unsigned (N.v17417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17417 s i)) at 1.
  unfold R.v17417, N.v17417.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17418 (s : N.State) (i : N.Inputs) :
  R.v17418 (state s) (inputs i) = Zmod.unsigned (N.v17418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17418 s i)) at 1.
  unfold R.v17418, N.v17418.
  unfold R.v16463, N.v16463.
  rewrite !state_r118_nr_5F118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r118_nr_5F118 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17419 (s : N.State) (i : N.Inputs) :
  R.v17419 (state s) (inputs i) = Zmod.unsigned (N.v17419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17419 s i)) at 1.
  unfold R.v17419, N.v17419.
  unfold R.v6, N.v6.
  rewrite !state_r117_nr_5F117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r117_nr_5F117 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17420 (s : N.State) (i : N.Inputs) :
  R.v17420 (state s) (inputs i) = Zmod.unsigned (N.v17420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17420 s i)) at 1.
  unfold R.v17420, N.v17420.
  unfold R.v6, N.v6.
  rewrite !state_r116_nr_5F116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r116_nr_5F116 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17421 (s : N.State) (i : N.Inputs) :
  R.v17421 (state s) (inputs i) = Zmod.unsigned (N.v17421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17421 s i)) at 1.
  unfold R.v17421, N.v17421.
  rewrite ?node_17419.
  rewrite ?node_17420.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17422 (s : N.State) (i : N.Inputs) :
  R.v17422 (state s) (inputs i) = Zmod.unsigned (N.v17422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17422 s i)) at 1.
  unfold R.v17422, N.v17422.
  unfold R.v16484, N.v16484.
  rewrite ?node_17421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17423 (s : N.State) (i : N.Inputs) :
  R.v17423 (state s) (inputs i) = Zmod.unsigned (N.v17423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17423 s i)) at 1.
  unfold R.v17423, N.v17423.
  rewrite ?node_17418.
  rewrite ?node_17422.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17424 (s : N.State) (i : N.Inputs) :
  R.v17424 (state s) (inputs i) = Zmod.unsigned (N.v17424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17424 s i)) at 1.
  unfold R.v17424, N.v17424.
  unfold R.v6, N.v6.
  rewrite ?node_17423.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17425 (s : N.State) (i : N.Inputs) :
  R.v17425 (state s) (inputs i) = Zmod.unsigned (N.v17425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17425 s i)) at 1.
  unfold R.v17425, N.v17425.
  rewrite ?node_5565.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17426 (s : N.State) (i : N.Inputs) :
  R.v17426 (state s) (inputs i) = Zmod.unsigned (N.v17426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17426 s i)) at 1.
  unfold R.v17426, N.v17426.
  unfold R.v6, N.v6.
  rewrite ?node_5627.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17427 (s : N.State) (i : N.Inputs) :
  R.v17427 (state s) (inputs i) = Zmod.unsigned (N.v17427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17427 s i)) at 1.
  unfold R.v17427, N.v17427.
  rewrite ?node_17425.
  rewrite ?node_17426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17428 (s : N.State) (i : N.Inputs) :
  R.v17428 (state s) (inputs i) = Zmod.unsigned (N.v17428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17428 s i)) at 1.
  unfold R.v17428, N.v17428.
  rewrite ?node_17424.
  rewrite ?node_17427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17429 (s : N.State) (i : N.Inputs) :
  R.v17429 (state s) (inputs i) = Zmod.unsigned (N.v17429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17429 s i)) at 1.
  unfold R.v17429, N.v17429.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17430 (s : N.State) (i : N.Inputs) :
  R.v17430 (state s) (inputs i) = Zmod.unsigned (N.v17430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17430 s i)) at 1.
  unfold R.v17430, N.v17430.
  rewrite ?node_5601.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17431 (s : N.State) (i : N.Inputs) :
  R.v17431 (state s) (inputs i) = Zmod.unsigned (N.v17431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17431 s i)) at 1.
  unfold R.v17431, N.v17431.
  unfold R.v16463, N.v16463.
  rewrite !state_r122_nr_5F122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r122_nr_5F122 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17432 (s : N.State) (i : N.Inputs) :
  R.v17432 (state s) (inputs i) = Zmod.unsigned (N.v17432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17432 s i)) at 1.
  unfold R.v17432, N.v17432.
  unfold R.v16463, N.v16463.
  rewrite !state_r121_nr_5F121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r121_nr_5F121 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17433 (s : N.State) (i : N.Inputs) :
  R.v17433 (state s) (inputs i) = Zmod.unsigned (N.v17433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17433 s i)) at 1.
  unfold R.v17433, N.v17433.
  unfold R.v6, N.v6.
  rewrite !state_r120_nr_5F120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r120_nr_5F120 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17434 (s : N.State) (i : N.Inputs) :
  R.v17434 (state s) (inputs i) = Zmod.unsigned (N.v17434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17434 s i)) at 1.
  unfold R.v17434, N.v17434.
  unfold R.v6, N.v6.
  rewrite !state_r119_nr_5F119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r119_nr_5F119 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17435 (s : N.State) (i : N.Inputs) :
  R.v17435 (state s) (inputs i) = Zmod.unsigned (N.v17435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17435 s i)) at 1.
  unfold R.v17435, N.v17435.
  rewrite ?node_17433.
  rewrite ?node_17434.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17436 (s : N.State) (i : N.Inputs) :
  R.v17436 (state s) (inputs i) = Zmod.unsigned (N.v17436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17436 s i)) at 1.
  unfold R.v17436, N.v17436.
  unfold R.v16484, N.v16484.
  rewrite ?node_17435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17437 (s : N.State) (i : N.Inputs) :
  R.v17437 (state s) (inputs i) = Zmod.unsigned (N.v17437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17437 s i)) at 1.
  unfold R.v17437, N.v17437.
  rewrite ?node_17430.
  rewrite ?node_17431.
  rewrite ?node_17432.
  rewrite ?node_17436.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17438 (s : N.State) (i : N.Inputs) :
  R.v17438 (state s) (inputs i) = Zmod.unsigned (N.v17438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17438 s i)) at 1.
  unfold R.v17438, N.v17438.
  unfold R.v6, N.v6.
  rewrite ?node_17437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17439 (s : N.State) (i : N.Inputs) :
  R.v17439 (state s) (inputs i) = Zmod.unsigned (N.v17439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17439 s i)) at 1.
  unfold R.v17439, N.v17439.
  rewrite ?node_5602.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17440 (s : N.State) (i : N.Inputs) :
  R.v17440 (state s) (inputs i) = Zmod.unsigned (N.v17440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17440 s i)) at 1.
  unfold R.v17440, N.v17440.
  unfold R.v6, N.v6.
  rewrite ?node_5652.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17441 (s : N.State) (i : N.Inputs) :
  R.v17441 (state s) (inputs i) = Zmod.unsigned (N.v17441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17441 s i)) at 1.
  unfold R.v17441, N.v17441.
  unfold R.v6, N.v6.
  rewrite ?node_5668.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17442 (s : N.State) (i : N.Inputs) :
  R.v17442 (state s) (inputs i) = Zmod.unsigned (N.v17442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17442 s i)) at 1.
  unfold R.v17442, N.v17442.
  rewrite ?node_17439.
  rewrite ?node_17440.
  rewrite ?node_17441.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17443 (s : N.State) (i : N.Inputs) :
  R.v17443 (state s) (inputs i) = Zmod.unsigned (N.v17443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17443 s i)) at 1.
  unfold R.v17443, N.v17443.
  rewrite ?node_17438.
  rewrite ?node_17442.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17444 (s : N.State) (i : N.Inputs) :
  R.v17444 (state s) (inputs i) = Zmod.unsigned (N.v17444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17444 s i)) at 1.
  unfold R.v17444, N.v17444.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17445 (s : N.State) (i : N.Inputs) :
  R.v17445 (state s) (inputs i) = Zmod.unsigned (N.v17445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17445 s i)) at 1.
  unfold R.v17445, N.v17445.
  unfold R.v16463, N.v16463.
  rewrite !state_r121_nr_5F121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r121_nr_5F121 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17446 (s : N.State) (i : N.Inputs) :
  R.v17446 (state s) (inputs i) = Zmod.unsigned (N.v17446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17446 s i)) at 1.
  unfold R.v17446, N.v17446.
  unfold R.v6, N.v6.
  rewrite !state_r120_nr_5F120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r120_nr_5F120 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17447 (s : N.State) (i : N.Inputs) :
  R.v17447 (state s) (inputs i) = Zmod.unsigned (N.v17447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17447 s i)) at 1.
  unfold R.v17447, N.v17447.
  unfold R.v6, N.v6.
  rewrite !state_r119_nr_5F119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r119_nr_5F119 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17448 (s : N.State) (i : N.Inputs) :
  R.v17448 (state s) (inputs i) = Zmod.unsigned (N.v17448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17448 s i)) at 1.
  unfold R.v17448, N.v17448.
  rewrite ?node_17446.
  rewrite ?node_17447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17449 (s : N.State) (i : N.Inputs) :
  R.v17449 (state s) (inputs i) = Zmod.unsigned (N.v17449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17449 s i)) at 1.
  unfold R.v17449, N.v17449.
  unfold R.v16484, N.v16484.
  rewrite ?node_17448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17450 (s : N.State) (i : N.Inputs) :
  R.v17450 (state s) (inputs i) = Zmod.unsigned (N.v17450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17450 s i)) at 1.
  unfold R.v17450, N.v17450.
  rewrite ?node_17445.
  rewrite ?node_17449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17451 (s : N.State) (i : N.Inputs) :
  R.v17451 (state s) (inputs i) = Zmod.unsigned (N.v17451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17451 s i)) at 1.
  unfold R.v17451, N.v17451.
  unfold R.v6, N.v6.
  rewrite ?node_17450.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17452 (s : N.State) (i : N.Inputs) :
  R.v17452 (state s) (inputs i) = Zmod.unsigned (N.v17452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17452 s i)) at 1.
  unfold R.v17452, N.v17452.
  rewrite ?node_5597.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17453 (s : N.State) (i : N.Inputs) :
  R.v17453 (state s) (inputs i) = Zmod.unsigned (N.v17453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17453 s i)) at 1.
  unfold R.v17453, N.v17453.
  unfold R.v6, N.v6.
  rewrite ?node_5652.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17454 (s : N.State) (i : N.Inputs) :
  R.v17454 (state s) (inputs i) = Zmod.unsigned (N.v17454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17454 s i)) at 1.
  unfold R.v17454, N.v17454.
  rewrite ?node_17452.
  rewrite ?node_17453.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17455 (s : N.State) (i : N.Inputs) :
  R.v17455 (state s) (inputs i) = Zmod.unsigned (N.v17455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17455 s i)) at 1.
  unfold R.v17455, N.v17455.
  rewrite ?node_17451.
  rewrite ?node_17454.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17456 (s : N.State) (i : N.Inputs) :
  R.v17456 (state s) (inputs i) = Zmod.unsigned (N.v17456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17456 s i)) at 1.
  unfold R.v17456, N.v17456.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17457 (s : N.State) (i : N.Inputs) :
  R.v17457 (state s) (inputs i) = Zmod.unsigned (N.v17457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17457 s i)) at 1.
  unfold R.v17457, N.v17457.
  rewrite ?node_5601.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17458 (s : N.State) (i : N.Inputs) :
  R.v17458 (state s) (inputs i) = Zmod.unsigned (N.v17458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17458 s i)) at 1.
  unfold R.v17458, N.v17458.
  unfold R.v6, N.v6.
  rewrite !state_r122_nr_5F122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r122_nr_5F122 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17459 (s : N.State) (i : N.Inputs) :
  R.v17459 (state s) (inputs i) = Zmod.unsigned (N.v17459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17459 s i)) at 1.
  unfold R.v17459, N.v17459.
  unfold R.v6, N.v6.
  rewrite ?node_5597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17460 (s : N.State) (i : N.Inputs) :
  R.v17460 (state s) (inputs i) = Zmod.unsigned (N.v17460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17460 s i)) at 1.
  unfold R.v17460, N.v17460.
  rewrite ?node_17458.
  rewrite ?node_17459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17461 (s : N.State) (i : N.Inputs) :
  R.v17461 (state s) (inputs i) = Zmod.unsigned (N.v17461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17461 s i)) at 1.
  unfold R.v17461, N.v17461.
  unfold R.v16484, N.v16484.
  rewrite ?node_17460.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17462 (s : N.State) (i : N.Inputs) :
  R.v17462 (state s) (inputs i) = Zmod.unsigned (N.v17462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17462 s i)) at 1.
  unfold R.v17462, N.v17462.
  rewrite ?node_17457.
  rewrite ?node_17461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17463 (s : N.State) (i : N.Inputs) :
  R.v17463 (state s) (inputs i) = Zmod.unsigned (N.v17463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17463 s i)) at 1.
  unfold R.v17463, N.v17463.
  unfold R.v6, N.v6.
  rewrite ?node_17462.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17464 (s : N.State) (i : N.Inputs) :
  R.v17464 (state s) (inputs i) = Zmod.unsigned (N.v17464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17464 s i)) at 1.
  unfold R.v17464, N.v17464.
  rewrite ?node_5602.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17465 (s : N.State) (i : N.Inputs) :
  R.v17465 (state s) (inputs i) = Zmod.unsigned (N.v17465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17465 s i)) at 1.
  unfold R.v17465, N.v17465.
  unfold R.v6, N.v6.
  rewrite ?node_5668.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17466 (s : N.State) (i : N.Inputs) :
  R.v17466 (state s) (inputs i) = Zmod.unsigned (N.v17466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17466 s i)) at 1.
  unfold R.v17466, N.v17466.
  rewrite ?node_17464.
  rewrite ?node_17465.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17467 (s : N.State) (i : N.Inputs) :
  R.v17467 (state s) (inputs i) = Zmod.unsigned (N.v17467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17467 s i)) at 1.
  unfold R.v17467, N.v17467.
  rewrite ?node_17463.
  rewrite ?node_17466.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17468 (s : N.State) (i : N.Inputs) :
  R.v17468 (state s) (inputs i) = Zmod.unsigned (N.v17468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17468 s i)) at 1.
  unfold R.v17468, N.v17468.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17469 (s : N.State) (i : N.Inputs) :
  R.v17469 (state s) (inputs i) = Zmod.unsigned (N.v17469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17469 s i)) at 1.
  unfold R.v17469, N.v17469.
  rewrite ?node_5608.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17470 (s : N.State) (i : N.Inputs) :
  R.v17470 (state s) (inputs i) = Zmod.unsigned (N.v17470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17470 s i)) at 1.
  unfold R.v17470, N.v17470.
  unfold R.v16463, N.v16463.
  rewrite !state_r126_nr_5F126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r126_nr_5F126 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17471 (s : N.State) (i : N.Inputs) :
  R.v17471 (state s) (inputs i) = Zmod.unsigned (N.v17471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17471 s i)) at 1.
  unfold R.v17471, N.v17471.
  unfold R.v16463, N.v16463.
  rewrite !state_r125_nr_5F125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r125_nr_5F125 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17472 (s : N.State) (i : N.Inputs) :
  R.v17472 (state s) (inputs i) = Zmod.unsigned (N.v17472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17472 s i)) at 1.
  unfold R.v17472, N.v17472.
  unfold R.v6, N.v6.
  rewrite !state_r124_nr_5F124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r124_nr_5F124 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17473 (s : N.State) (i : N.Inputs) :
  R.v17473 (state s) (inputs i) = Zmod.unsigned (N.v17473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17473 s i)) at 1.
  unfold R.v17473, N.v17473.
  unfold R.v6, N.v6.
  rewrite !state_r123_nr_5F123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r123_nr_5F123 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17474 (s : N.State) (i : N.Inputs) :
  R.v17474 (state s) (inputs i) = Zmod.unsigned (N.v17474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17474 s i)) at 1.
  unfold R.v17474, N.v17474.
  rewrite ?node_17472.
  rewrite ?node_17473.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17475 (s : N.State) (i : N.Inputs) :
  R.v17475 (state s) (inputs i) = Zmod.unsigned (N.v17475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17475 s i)) at 1.
  unfold R.v17475, N.v17475.
  unfold R.v16484, N.v16484.
  rewrite ?node_17474.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17476 (s : N.State) (i : N.Inputs) :
  R.v17476 (state s) (inputs i) = Zmod.unsigned (N.v17476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17476 s i)) at 1.
  unfold R.v17476, N.v17476.
  rewrite ?node_17469.
  rewrite ?node_17470.
  rewrite ?node_17471.
  rewrite ?node_17475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17477 (s : N.State) (i : N.Inputs) :
  R.v17477 (state s) (inputs i) = Zmod.unsigned (N.v17477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17477 s i)) at 1.
  unfold R.v17477, N.v17477.
  unfold R.v6, N.v6.
  rewrite ?node_17476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17478 (s : N.State) (i : N.Inputs) :
  R.v17478 (state s) (inputs i) = Zmod.unsigned (N.v17478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17478 s i)) at 1.
  unfold R.v17478, N.v17478.
  rewrite ?node_5609.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17479 (s : N.State) (i : N.Inputs) :
  R.v17479 (state s) (inputs i) = Zmod.unsigned (N.v17479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17479 s i)) at 1.
  unfold R.v17479, N.v17479.
  unfold R.v6, N.v6.
  rewrite ?node_5659.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17480 (s : N.State) (i : N.Inputs) :
  R.v17480 (state s) (inputs i) = Zmod.unsigned (N.v17480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17480 s i)) at 1.
  unfold R.v17480, N.v17480.
  unfold R.v6, N.v6.
  rewrite ?node_5676.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17481 (s : N.State) (i : N.Inputs) :
  R.v17481 (state s) (inputs i) = Zmod.unsigned (N.v17481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17481 s i)) at 1.
  unfold R.v17481, N.v17481.
  rewrite ?node_17478.
  rewrite ?node_17479.
  rewrite ?node_17480.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17482 (s : N.State) (i : N.Inputs) :
  R.v17482 (state s) (inputs i) = Zmod.unsigned (N.v17482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17482 s i)) at 1.
  unfold R.v17482, N.v17482.
  rewrite ?node_17477.
  rewrite ?node_17481.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17483 (s : N.State) (i : N.Inputs) :
  R.v17483 (state s) (inputs i) = Zmod.unsigned (N.v17483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17483 s i)) at 1.
  unfold R.v17483, N.v17483.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17484 (s : N.State) (i : N.Inputs) :
  R.v17484 (state s) (inputs i) = Zmod.unsigned (N.v17484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17484 s i)) at 1.
  unfold R.v17484, N.v17484.
  unfold R.v16463, N.v16463.
  rewrite !state_r125_nr_5F125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r125_nr_5F125 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17485 (s : N.State) (i : N.Inputs) :
  R.v17485 (state s) (inputs i) = Zmod.unsigned (N.v17485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17485 s i)) at 1.
  unfold R.v17485, N.v17485.
  unfold R.v6, N.v6.
  rewrite !state_r124_nr_5F124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r124_nr_5F124 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17486 (s : N.State) (i : N.Inputs) :
  R.v17486 (state s) (inputs i) = Zmod.unsigned (N.v17486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17486 s i)) at 1.
  unfold R.v17486, N.v17486.
  unfold R.v6, N.v6.
  rewrite !state_r123_nr_5F123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r123_nr_5F123 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17487 (s : N.State) (i : N.Inputs) :
  R.v17487 (state s) (inputs i) = Zmod.unsigned (N.v17487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17487 s i)) at 1.
  unfold R.v17487, N.v17487.
  rewrite ?node_17485.
  rewrite ?node_17486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17488 (s : N.State) (i : N.Inputs) :
  R.v17488 (state s) (inputs i) = Zmod.unsigned (N.v17488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17488 s i)) at 1.
  unfold R.v17488, N.v17488.
  unfold R.v16484, N.v16484.
  rewrite ?node_17487.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17489 (s : N.State) (i : N.Inputs) :
  R.v17489 (state s) (inputs i) = Zmod.unsigned (N.v17489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17489 s i)) at 1.
  unfold R.v17489, N.v17489.
  rewrite ?node_17484.
  rewrite ?node_17488.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17490 (s : N.State) (i : N.Inputs) :
  R.v17490 (state s) (inputs i) = Zmod.unsigned (N.v17490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17490 s i)) at 1.
  unfold R.v17490, N.v17490.
  unfold R.v6, N.v6.
  rewrite ?node_17489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17491 (s : N.State) (i : N.Inputs) :
  R.v17491 (state s) (inputs i) = Zmod.unsigned (N.v17491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17491 s i)) at 1.
  unfold R.v17491, N.v17491.
  rewrite ?node_5604.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17492 (s : N.State) (i : N.Inputs) :
  R.v17492 (state s) (inputs i) = Zmod.unsigned (N.v17492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17492 s i)) at 1.
  unfold R.v17492, N.v17492.
  unfold R.v6, N.v6.
  rewrite ?node_5659.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17493 (s : N.State) (i : N.Inputs) :
  R.v17493 (state s) (inputs i) = Zmod.unsigned (N.v17493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17493 s i)) at 1.
  unfold R.v17493, N.v17493.
  rewrite ?node_17491.
  rewrite ?node_17492.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17494 (s : N.State) (i : N.Inputs) :
  R.v17494 (state s) (inputs i) = Zmod.unsigned (N.v17494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17494 s i)) at 1.
  unfold R.v17494, N.v17494.
  rewrite ?node_17490.
  rewrite ?node_17493.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17495 (s : N.State) (i : N.Inputs) :
  R.v17495 (state s) (inputs i) = Zmod.unsigned (N.v17495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17495 s i)) at 1.
  unfold R.v17495, N.v17495.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17496 (s : N.State) (i : N.Inputs) :
  R.v17496 (state s) (inputs i) = Zmod.unsigned (N.v17496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17496 s i)) at 1.
  unfold R.v17496, N.v17496.
  rewrite ?node_5608.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17497 (s : N.State) (i : N.Inputs) :
  R.v17497 (state s) (inputs i) = Zmod.unsigned (N.v17497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17497 s i)) at 1.
  unfold R.v17497, N.v17497.
  unfold R.v6, N.v6.
  rewrite !state_r126_nr_5F126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r126_nr_5F126 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17498 (s : N.State) (i : N.Inputs) :
  R.v17498 (state s) (inputs i) = Zmod.unsigned (N.v17498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17498 s i)) at 1.
  unfold R.v17498, N.v17498.
  unfold R.v6, N.v6.
  rewrite ?node_5604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17499 (s : N.State) (i : N.Inputs) :
  R.v17499 (state s) (inputs i) = Zmod.unsigned (N.v17499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17499 s i)) at 1.
  unfold R.v17499, N.v17499.
  rewrite ?node_17497.
  rewrite ?node_17498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17500 (s : N.State) (i : N.Inputs) :
  R.v17500 (state s) (inputs i) = Zmod.unsigned (N.v17500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17500 s i)) at 1.
  unfold R.v17500, N.v17500.
  unfold R.v16484, N.v16484.
  rewrite ?node_17499.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17501 (s : N.State) (i : N.Inputs) :
  R.v17501 (state s) (inputs i) = Zmod.unsigned (N.v17501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17501 s i)) at 1.
  unfold R.v17501, N.v17501.
  rewrite ?node_17496.
  rewrite ?node_17500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17502 (s : N.State) (i : N.Inputs) :
  R.v17502 (state s) (inputs i) = Zmod.unsigned (N.v17502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17502 s i)) at 1.
  unfold R.v17502, N.v17502.
  unfold R.v6, N.v6.
  rewrite ?node_17501.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17503 (s : N.State) (i : N.Inputs) :
  R.v17503 (state s) (inputs i) = Zmod.unsigned (N.v17503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17503 s i)) at 1.
  unfold R.v17503, N.v17503.
  rewrite ?node_5609.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17504 (s : N.State) (i : N.Inputs) :
  R.v17504 (state s) (inputs i) = Zmod.unsigned (N.v17504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17504 s i)) at 1.
  unfold R.v17504, N.v17504.
  unfold R.v6, N.v6.
  rewrite ?node_5676.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17505 (s : N.State) (i : N.Inputs) :
  R.v17505 (state s) (inputs i) = Zmod.unsigned (N.v17505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17505 s i)) at 1.
  unfold R.v17505, N.v17505.
  rewrite ?node_17503.
  rewrite ?node_17504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17506 (s : N.State) (i : N.Inputs) :
  R.v17506 (state s) (inputs i) = Zmod.unsigned (N.v17506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17506 s i)) at 1.
  unfold R.v17506, N.v17506.
  rewrite ?node_17502.
  rewrite ?node_17505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17507 (s : N.State) (i : N.Inputs) :
  R.v17507 (state s) (inputs i) = Zmod.unsigned (N.v17507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17507 s i)) at 1.
  unfold R.v17507, N.v17507.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17508 (s : N.State) (i : N.Inputs) :
  R.v17508 (state s) (inputs i) = Zmod.unsigned (N.v17508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17508 s i)) at 1.
  unfold R.v17508, N.v17508.
  unfold R.v16463, N.v16463.
  rewrite !state_r129_nr_5F129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r129_nr_5F129 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17509 (s : N.State) (i : N.Inputs) :
  R.v17509 (state s) (inputs i) = Zmod.unsigned (N.v17509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17509 s i)) at 1.
  unfold R.v17509, N.v17509.
  unfold R.v6, N.v6.
  rewrite !state_r128_nr_5F128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r128_nr_5F128 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17510 (s : N.State) (i : N.Inputs) :
  R.v17510 (state s) (inputs i) = Zmod.unsigned (N.v17510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17510 s i)) at 1.
  unfold R.v17510, N.v17510.
  unfold R.v6, N.v6.
  rewrite !state_r127_nr_5F127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r127_nr_5F127 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17511 (s : N.State) (i : N.Inputs) :
  R.v17511 (state s) (inputs i) = Zmod.unsigned (N.v17511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17511 s i)) at 1.
  unfold R.v17511, N.v17511.
  rewrite ?node_17509.
  rewrite ?node_17510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17512 (s : N.State) (i : N.Inputs) :
  R.v17512 (state s) (inputs i) = Zmod.unsigned (N.v17512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17512 s i)) at 1.
  unfold R.v17512, N.v17512.
  unfold R.v16484, N.v16484.
  rewrite ?node_17511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17513 (s : N.State) (i : N.Inputs) :
  R.v17513 (state s) (inputs i) = Zmod.unsigned (N.v17513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17513 s i)) at 1.
  unfold R.v17513, N.v17513.
  rewrite ?node_17508.
  rewrite ?node_17512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17514 (s : N.State) (i : N.Inputs) :
  R.v17514 (state s) (inputs i) = Zmod.unsigned (N.v17514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17514 s i)) at 1.
  unfold R.v17514, N.v17514.
  unfold R.v6, N.v6.
  rewrite ?node_17513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17515 (s : N.State) (i : N.Inputs) :
  R.v17515 (state s) (inputs i) = Zmod.unsigned (N.v17515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17515 s i)) at 1.
  unfold R.v17515, N.v17515.
  rewrite ?node_5612.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17516 (s : N.State) (i : N.Inputs) :
  R.v17516 (state s) (inputs i) = Zmod.unsigned (N.v17516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17516 s i)) at 1.
  unfold R.v17516, N.v17516.
  unfold R.v6, N.v6.
  rewrite ?node_5679.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17517 (s : N.State) (i : N.Inputs) :
  R.v17517 (state s) (inputs i) = Zmod.unsigned (N.v17517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17517 s i)) at 1.
  unfold R.v17517, N.v17517.
  rewrite ?node_17515.
  rewrite ?node_17516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17518 (s : N.State) (i : N.Inputs) :
  R.v17518 (state s) (inputs i) = Zmod.unsigned (N.v17518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17518 s i)) at 1.
  unfold R.v17518, N.v17518.
  rewrite ?node_17514.
  rewrite ?node_17517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17519 (s : N.State) (i : N.Inputs) :
  R.v17519 (state s) (inputs i) = Zmod.unsigned (N.v17519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17519 s i)) at 1.
  unfold R.v17519, N.v17519.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17520 (s : N.State) (i : N.Inputs) :
  R.v17520 (state s) (inputs i) = Zmod.unsigned (N.v17520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17520 s i)) at 1.
  unfold R.v17520, N.v17520.
  rewrite ?node_5652.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17521 (s : N.State) (i : N.Inputs) :
  R.v17521 (state s) (inputs i) = Zmod.unsigned (N.v17521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17521 s i)) at 1.
  unfold R.v17521, N.v17521.
  unfold R.v16463, N.v16463.
  rewrite !state_r133_nr_5F133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r133_nr_5F133 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17522 (s : N.State) (i : N.Inputs) :
  R.v17522 (state s) (inputs i) = Zmod.unsigned (N.v17522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17522 s i)) at 1.
  unfold R.v17522, N.v17522.
  unfold R.v16463, N.v16463.
  rewrite !state_r132_nr_5F132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r132_nr_5F132 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17523 (s : N.State) (i : N.Inputs) :
  R.v17523 (state s) (inputs i) = Zmod.unsigned (N.v17523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17523 s i)) at 1.
  unfold R.v17523, N.v17523.
  unfold R.v6, N.v6.
  rewrite !state_r131_nr_5F131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r131_nr_5F131 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17524 (s : N.State) (i : N.Inputs) :
  R.v17524 (state s) (inputs i) = Zmod.unsigned (N.v17524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17524 s i)) at 1.
  unfold R.v17524, N.v17524.
  unfold R.v6, N.v6.
  rewrite !state_r130_nr_5F130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r130_nr_5F130 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17525 (s : N.State) (i : N.Inputs) :
  R.v17525 (state s) (inputs i) = Zmod.unsigned (N.v17525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17525 s i)) at 1.
  unfold R.v17525, N.v17525.
  rewrite ?node_17523.
  rewrite ?node_17524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17526 (s : N.State) (i : N.Inputs) :
  R.v17526 (state s) (inputs i) = Zmod.unsigned (N.v17526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17526 s i)) at 1.
  unfold R.v17526, N.v17526.
  unfold R.v16484, N.v16484.
  rewrite ?node_17525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17527 (s : N.State) (i : N.Inputs) :
  R.v17527 (state s) (inputs i) = Zmod.unsigned (N.v17527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17527 s i)) at 1.
  unfold R.v17527, N.v17527.
  rewrite ?node_17520.
  rewrite ?node_17521.
  rewrite ?node_17522.
  rewrite ?node_17526.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17528 (s : N.State) (i : N.Inputs) :
  R.v17528 (state s) (inputs i) = Zmod.unsigned (N.v17528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17528 s i)) at 1.
  unfold R.v17528, N.v17528.
  unfold R.v6, N.v6.
  rewrite ?node_17527.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17529 (s : N.State) (i : N.Inputs) :
  R.v17529 (state s) (inputs i) = Zmod.unsigned (N.v17529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17529 s i)) at 1.
  unfold R.v17529, N.v17529.
  rewrite ?node_5653.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17530 (s : N.State) (i : N.Inputs) :
  R.v17530 (state s) (inputs i) = Zmod.unsigned (N.v17530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17530 s i)) at 1.
  unfold R.v17530, N.v17530.
  unfold R.v6, N.v6.
  rewrite ?node_5706.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17531 (s : N.State) (i : N.Inputs) :
  R.v17531 (state s) (inputs i) = Zmod.unsigned (N.v17531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17531 s i)) at 1.
  unfold R.v17531, N.v17531.
  unfold R.v6, N.v6.
  rewrite ?node_5726.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17532 (s : N.State) (i : N.Inputs) :
  R.v17532 (state s) (inputs i) = Zmod.unsigned (N.v17532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17532 s i)) at 1.
  unfold R.v17532, N.v17532.
  rewrite ?node_17529.
  rewrite ?node_17530.
  rewrite ?node_17531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17533 (s : N.State) (i : N.Inputs) :
  R.v17533 (state s) (inputs i) = Zmod.unsigned (N.v17533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17533 s i)) at 1.
  unfold R.v17533, N.v17533.
  rewrite ?node_17528.
  rewrite ?node_17532.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17534 (s : N.State) (i : N.Inputs) :
  R.v17534 (state s) (inputs i) = Zmod.unsigned (N.v17534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17534 s i)) at 1.
  unfold R.v17534, N.v17534.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17535 (s : N.State) (i : N.Inputs) :
  R.v17535 (state s) (inputs i) = Zmod.unsigned (N.v17535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17535 s i)) at 1.
  unfold R.v17535, N.v17535.
  unfold R.v16463, N.v16463.
  rewrite !state_r132_nr_5F132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r132_nr_5F132 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17536 (s : N.State) (i : N.Inputs) :
  R.v17536 (state s) (inputs i) = Zmod.unsigned (N.v17536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17536 s i)) at 1.
  unfold R.v17536, N.v17536.
  unfold R.v6, N.v6.
  rewrite !state_r131_nr_5F131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r131_nr_5F131 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17537 (s : N.State) (i : N.Inputs) :
  R.v17537 (state s) (inputs i) = Zmod.unsigned (N.v17537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17537 s i)) at 1.
  unfold R.v17537, N.v17537.
  unfold R.v6, N.v6.
  rewrite !state_r130_nr_5F130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r130_nr_5F130 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17538 (s : N.State) (i : N.Inputs) :
  R.v17538 (state s) (inputs i) = Zmod.unsigned (N.v17538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17538 s i)) at 1.
  unfold R.v17538, N.v17538.
  rewrite ?node_17536.
  rewrite ?node_17537.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17539 (s : N.State) (i : N.Inputs) :
  R.v17539 (state s) (inputs i) = Zmod.unsigned (N.v17539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17539 s i)) at 1.
  unfold R.v17539, N.v17539.
  unfold R.v16484, N.v16484.
  rewrite ?node_17538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17540 (s : N.State) (i : N.Inputs) :
  R.v17540 (state s) (inputs i) = Zmod.unsigned (N.v17540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17540 s i)) at 1.
  unfold R.v17540, N.v17540.
  rewrite ?node_17535.
  rewrite ?node_17539.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17541 (s : N.State) (i : N.Inputs) :
  R.v17541 (state s) (inputs i) = Zmod.unsigned (N.v17541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17541 s i)) at 1.
  unfold R.v17541, N.v17541.
  unfold R.v6, N.v6.
  rewrite ?node_17540.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17542 (s : N.State) (i : N.Inputs) :
  R.v17542 (state s) (inputs i) = Zmod.unsigned (N.v17542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17542 s i)) at 1.
  unfold R.v17542, N.v17542.
  rewrite ?node_5648.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17543 (s : N.State) (i : N.Inputs) :
  R.v17543 (state s) (inputs i) = Zmod.unsigned (N.v17543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17543 s i)) at 1.
  unfold R.v17543, N.v17543.
  unfold R.v6, N.v6.
  rewrite ?node_5706.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17544 (s : N.State) (i : N.Inputs) :
  R.v17544 (state s) (inputs i) = Zmod.unsigned (N.v17544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17544 s i)) at 1.
  unfold R.v17544, N.v17544.
  rewrite ?node_17542.
  rewrite ?node_17543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17545 (s : N.State) (i : N.Inputs) :
  R.v17545 (state s) (inputs i) = Zmod.unsigned (N.v17545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17545 s i)) at 1.
  unfold R.v17545, N.v17545.
  rewrite ?node_17541.
  rewrite ?node_17544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17546 (s : N.State) (i : N.Inputs) :
  R.v17546 (state s) (inputs i) = Zmod.unsigned (N.v17546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17546 s i)) at 1.
  unfold R.v17546, N.v17546.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17547 (s : N.State) (i : N.Inputs) :
  R.v17547 (state s) (inputs i) = Zmod.unsigned (N.v17547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17547 s i)) at 1.
  unfold R.v17547, N.v17547.
  rewrite ?node_5652.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17548 (s : N.State) (i : N.Inputs) :
  R.v17548 (state s) (inputs i) = Zmod.unsigned (N.v17548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17548 s i)) at 1.
  unfold R.v17548, N.v17548.
  unfold R.v6, N.v6.
  rewrite !state_r133_nr_5F133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r133_nr_5F133 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17549 (s : N.State) (i : N.Inputs) :
  R.v17549 (state s) (inputs i) = Zmod.unsigned (N.v17549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17549 s i)) at 1.
  unfold R.v17549, N.v17549.
  unfold R.v6, N.v6.
  rewrite ?node_5648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17550 (s : N.State) (i : N.Inputs) :
  R.v17550 (state s) (inputs i) = Zmod.unsigned (N.v17550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17550 s i)) at 1.
  unfold R.v17550, N.v17550.
  rewrite ?node_17548.
  rewrite ?node_17549.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17551 (s : N.State) (i : N.Inputs) :
  R.v17551 (state s) (inputs i) = Zmod.unsigned (N.v17551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17551 s i)) at 1.
  unfold R.v17551, N.v17551.
  unfold R.v16484, N.v16484.
  rewrite ?node_17550.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17552 (s : N.State) (i : N.Inputs) :
  R.v17552 (state s) (inputs i) = Zmod.unsigned (N.v17552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17552 s i)) at 1.
  unfold R.v17552, N.v17552.
  rewrite ?node_17547.
  rewrite ?node_17551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17553 (s : N.State) (i : N.Inputs) :
  R.v17553 (state s) (inputs i) = Zmod.unsigned (N.v17553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17553 s i)) at 1.
  unfold R.v17553, N.v17553.
  unfold R.v6, N.v6.
  rewrite ?node_17552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17554 (s : N.State) (i : N.Inputs) :
  R.v17554 (state s) (inputs i) = Zmod.unsigned (N.v17554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17554 s i)) at 1.
  unfold R.v17554, N.v17554.
  rewrite ?node_5653.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17555 (s : N.State) (i : N.Inputs) :
  R.v17555 (state s) (inputs i) = Zmod.unsigned (N.v17555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17555 s i)) at 1.
  unfold R.v17555, N.v17555.
  unfold R.v6, N.v6.
  rewrite ?node_5726.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17556 (s : N.State) (i : N.Inputs) :
  R.v17556 (state s) (inputs i) = Zmod.unsigned (N.v17556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17556 s i)) at 1.
  unfold R.v17556, N.v17556.
  rewrite ?node_17554.
  rewrite ?node_17555.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17557 (s : N.State) (i : N.Inputs) :
  R.v17557 (state s) (inputs i) = Zmod.unsigned (N.v17557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17557 s i)) at 1.
  unfold R.v17557, N.v17557.
  rewrite ?node_17553.
  rewrite ?node_17556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17558 (s : N.State) (i : N.Inputs) :
  R.v17558 (state s) (inputs i) = Zmod.unsigned (N.v17558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17558 s i)) at 1.
  unfold R.v17558, N.v17558.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17559 (s : N.State) (i : N.Inputs) :
  R.v17559 (state s) (inputs i) = Zmod.unsigned (N.v17559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17559 s i)) at 1.
  unfold R.v17559, N.v17559.
  rewrite ?node_5659.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17560 (s : N.State) (i : N.Inputs) :
  R.v17560 (state s) (inputs i) = Zmod.unsigned (N.v17560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17560 s i)) at 1.
  unfold R.v17560, N.v17560.
  unfold R.v16463, N.v16463.
  rewrite !state_r137_nr_5F137.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r137_nr_5F137 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17561 (s : N.State) (i : N.Inputs) :
  R.v17561 (state s) (inputs i) = Zmod.unsigned (N.v17561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17561 s i)) at 1.
  unfold R.v17561, N.v17561.
  unfold R.v16463, N.v16463.
  rewrite !state_r136_nr_5F136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r136_nr_5F136 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17562 (s : N.State) (i : N.Inputs) :
  R.v17562 (state s) (inputs i) = Zmod.unsigned (N.v17562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17562 s i)) at 1.
  unfold R.v17562, N.v17562.
  unfold R.v6, N.v6.
  rewrite !state_r135_nr_5F135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r135_nr_5F135 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17563 (s : N.State) (i : N.Inputs) :
  R.v17563 (state s) (inputs i) = Zmod.unsigned (N.v17563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17563 s i)) at 1.
  unfold R.v17563, N.v17563.
  unfold R.v6, N.v6.
  rewrite !state_r134_nr_5F134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r134_nr_5F134 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17564 (s : N.State) (i : N.Inputs) :
  R.v17564 (state s) (inputs i) = Zmod.unsigned (N.v17564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17564 s i)) at 1.
  unfold R.v17564, N.v17564.
  rewrite ?node_17562.
  rewrite ?node_17563.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17565 (s : N.State) (i : N.Inputs) :
  R.v17565 (state s) (inputs i) = Zmod.unsigned (N.v17565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17565 s i)) at 1.
  unfold R.v17565, N.v17565.
  unfold R.v16484, N.v16484.
  rewrite ?node_17564.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17566 (s : N.State) (i : N.Inputs) :
  R.v17566 (state s) (inputs i) = Zmod.unsigned (N.v17566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17566 s i)) at 1.
  unfold R.v17566, N.v17566.
  rewrite ?node_17559.
  rewrite ?node_17560.
  rewrite ?node_17561.
  rewrite ?node_17565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17567 (s : N.State) (i : N.Inputs) :
  R.v17567 (state s) (inputs i) = Zmod.unsigned (N.v17567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17567 s i)) at 1.
  unfold R.v17567, N.v17567.
  unfold R.v6, N.v6.
  rewrite ?node_17566.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17568 (s : N.State) (i : N.Inputs) :
  R.v17568 (state s) (inputs i) = Zmod.unsigned (N.v17568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17568 s i)) at 1.
  unfold R.v17568, N.v17568.
  rewrite ?node_5660.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17569 (s : N.State) (i : N.Inputs) :
  R.v17569 (state s) (inputs i) = Zmod.unsigned (N.v17569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17569 s i)) at 1.
  unfold R.v17569, N.v17569.
  unfold R.v6, N.v6.
  rewrite ?node_5713.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17570 (s : N.State) (i : N.Inputs) :
  R.v17570 (state s) (inputs i) = Zmod.unsigned (N.v17570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17570 s i)) at 1.
  unfold R.v17570, N.v17570.
  unfold R.v6, N.v6.
  rewrite ?node_5734.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17571 (s : N.State) (i : N.Inputs) :
  R.v17571 (state s) (inputs i) = Zmod.unsigned (N.v17571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17571 s i)) at 1.
  unfold R.v17571, N.v17571.
  rewrite ?node_17568.
  rewrite ?node_17569.
  rewrite ?node_17570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17572 (s : N.State) (i : N.Inputs) :
  R.v17572 (state s) (inputs i) = Zmod.unsigned (N.v17572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17572 s i)) at 1.
  unfold R.v17572, N.v17572.
  rewrite ?node_17567.
  rewrite ?node_17571.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17573 (s : N.State) (i : N.Inputs) :
  R.v17573 (state s) (inputs i) = Zmod.unsigned (N.v17573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17573 s i)) at 1.
  unfold R.v17573, N.v17573.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17574 (s : N.State) (i : N.Inputs) :
  R.v17574 (state s) (inputs i) = Zmod.unsigned (N.v17574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17574 s i)) at 1.
  unfold R.v17574, N.v17574.
  unfold R.v16463, N.v16463.
  rewrite !state_r136_nr_5F136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r136_nr_5F136 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17575 (s : N.State) (i : N.Inputs) :
  R.v17575 (state s) (inputs i) = Zmod.unsigned (N.v17575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17575 s i)) at 1.
  unfold R.v17575, N.v17575.
  unfold R.v6, N.v6.
  rewrite !state_r135_nr_5F135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r135_nr_5F135 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17576 (s : N.State) (i : N.Inputs) :
  R.v17576 (state s) (inputs i) = Zmod.unsigned (N.v17576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17576 s i)) at 1.
  unfold R.v17576, N.v17576.
  unfold R.v6, N.v6.
  rewrite !state_r134_nr_5F134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r134_nr_5F134 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17577 (s : N.State) (i : N.Inputs) :
  R.v17577 (state s) (inputs i) = Zmod.unsigned (N.v17577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17577 s i)) at 1.
  unfold R.v17577, N.v17577.
  rewrite ?node_17575.
  rewrite ?node_17576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17578 (s : N.State) (i : N.Inputs) :
  R.v17578 (state s) (inputs i) = Zmod.unsigned (N.v17578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17578 s i)) at 1.
  unfold R.v17578, N.v17578.
  unfold R.v16484, N.v16484.
  rewrite ?node_17577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17579 (s : N.State) (i : N.Inputs) :
  R.v17579 (state s) (inputs i) = Zmod.unsigned (N.v17579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17579 s i)) at 1.
  unfold R.v17579, N.v17579.
  rewrite ?node_17574.
  rewrite ?node_17578.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17580 (s : N.State) (i : N.Inputs) :
  R.v17580 (state s) (inputs i) = Zmod.unsigned (N.v17580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17580 s i)) at 1.
  unfold R.v17580, N.v17580.
  unfold R.v6, N.v6.
  rewrite ?node_17579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17581 (s : N.State) (i : N.Inputs) :
  R.v17581 (state s) (inputs i) = Zmod.unsigned (N.v17581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17581 s i)) at 1.
  unfold R.v17581, N.v17581.
  rewrite ?node_5655.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17582 (s : N.State) (i : N.Inputs) :
  R.v17582 (state s) (inputs i) = Zmod.unsigned (N.v17582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17582 s i)) at 1.
  unfold R.v17582, N.v17582.
  unfold R.v6, N.v6.
  rewrite ?node_5713.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17583 (s : N.State) (i : N.Inputs) :
  R.v17583 (state s) (inputs i) = Zmod.unsigned (N.v17583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17583 s i)) at 1.
  unfold R.v17583, N.v17583.
  rewrite ?node_17581.
  rewrite ?node_17582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17584 (s : N.State) (i : N.Inputs) :
  R.v17584 (state s) (inputs i) = Zmod.unsigned (N.v17584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17584 s i)) at 1.
  unfold R.v17584, N.v17584.
  rewrite ?node_17580.
  rewrite ?node_17583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17585 (s : N.State) (i : N.Inputs) :
  R.v17585 (state s) (inputs i) = Zmod.unsigned (N.v17585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17585 s i)) at 1.
  unfold R.v17585, N.v17585.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17586 (s : N.State) (i : N.Inputs) :
  R.v17586 (state s) (inputs i) = Zmod.unsigned (N.v17586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17586 s i)) at 1.
  unfold R.v17586, N.v17586.
  rewrite ?node_5659.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17587 (s : N.State) (i : N.Inputs) :
  R.v17587 (state s) (inputs i) = Zmod.unsigned (N.v17587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17587 s i)) at 1.
  unfold R.v17587, N.v17587.
  unfold R.v6, N.v6.
  rewrite !state_r137_nr_5F137.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r137_nr_5F137 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17588 (s : N.State) (i : N.Inputs) :
  R.v17588 (state s) (inputs i) = Zmod.unsigned (N.v17588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17588 s i)) at 1.
  unfold R.v17588, N.v17588.
  unfold R.v6, N.v6.
  rewrite ?node_5655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17589 (s : N.State) (i : N.Inputs) :
  R.v17589 (state s) (inputs i) = Zmod.unsigned (N.v17589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17589 s i)) at 1.
  unfold R.v17589, N.v17589.
  rewrite ?node_17587.
  rewrite ?node_17588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17590 (s : N.State) (i : N.Inputs) :
  R.v17590 (state s) (inputs i) = Zmod.unsigned (N.v17590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17590 s i)) at 1.
  unfold R.v17590, N.v17590.
  unfold R.v16484, N.v16484.
  rewrite ?node_17589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17591 (s : N.State) (i : N.Inputs) :
  R.v17591 (state s) (inputs i) = Zmod.unsigned (N.v17591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17591 s i)) at 1.
  unfold R.v17591, N.v17591.
  rewrite ?node_17586.
  rewrite ?node_17590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17592 (s : N.State) (i : N.Inputs) :
  R.v17592 (state s) (inputs i) = Zmod.unsigned (N.v17592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17592 s i)) at 1.
  unfold R.v17592, N.v17592.
  unfold R.v6, N.v6.
  rewrite ?node_17591.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17593 (s : N.State) (i : N.Inputs) :
  R.v17593 (state s) (inputs i) = Zmod.unsigned (N.v17593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17593 s i)) at 1.
  unfold R.v17593, N.v17593.
  rewrite ?node_5660.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17594 (s : N.State) (i : N.Inputs) :
  R.v17594 (state s) (inputs i) = Zmod.unsigned (N.v17594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17594 s i)) at 1.
  unfold R.v17594, N.v17594.
  unfold R.v6, N.v6.
  rewrite ?node_5734.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17595 (s : N.State) (i : N.Inputs) :
  R.v17595 (state s) (inputs i) = Zmod.unsigned (N.v17595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17595 s i)) at 1.
  unfold R.v17595, N.v17595.
  rewrite ?node_17593.
  rewrite ?node_17594.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17596 (s : N.State) (i : N.Inputs) :
  R.v17596 (state s) (inputs i) = Zmod.unsigned (N.v17596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17596 s i)) at 1.
  unfold R.v17596, N.v17596.
  rewrite ?node_17592.
  rewrite ?node_17595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17597 (s : N.State) (i : N.Inputs) :
  R.v17597 (state s) (inputs i) = Zmod.unsigned (N.v17597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17597 s i)) at 1.
  unfold R.v17597, N.v17597.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17598 (s : N.State) (i : N.Inputs) :
  R.v17598 (state s) (inputs i) = Zmod.unsigned (N.v17598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17598 s i)) at 1.
  unfold R.v17598, N.v17598.
  unfold R.v16463, N.v16463.
  rewrite !state_r141_nr_5F141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r141_nr_5F141 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17599 (s : N.State) (i : N.Inputs) :
  R.v17599 (state s) (inputs i) = Zmod.unsigned (N.v17599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17599 s i)) at 1.
  unfold R.v17599, N.v17599.
  unfold R.v16463, N.v16463.
  rewrite !state_r140_nr_5F140.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r140_nr_5F140 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17600 (s : N.State) (i : N.Inputs) :
  R.v17600 (state s) (inputs i) = Zmod.unsigned (N.v17600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17600 s i)) at 1.
  unfold R.v17600, N.v17600.
  unfold R.v6, N.v6.
  rewrite !state_r139_nr_5F139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r139_nr_5F139 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17601 (s : N.State) (i : N.Inputs) :
  R.v17601 (state s) (inputs i) = Zmod.unsigned (N.v17601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17601 s i)) at 1.
  unfold R.v17601, N.v17601.
  unfold R.v6, N.v6.
  rewrite !state_r138_nr_5F138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r138_nr_5F138 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17602 (s : N.State) (i : N.Inputs) :
  R.v17602 (state s) (inputs i) = Zmod.unsigned (N.v17602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17602 s i)) at 1.
  unfold R.v17602, N.v17602.
  rewrite ?node_17600.
  rewrite ?node_17601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17603 (s : N.State) (i : N.Inputs) :
  R.v17603 (state s) (inputs i) = Zmod.unsigned (N.v17603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17603 s i)) at 1.
  unfold R.v17603, N.v17603.
  unfold R.v16484, N.v16484.
  rewrite ?node_17602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17604 (s : N.State) (i : N.Inputs) :
  R.v17604 (state s) (inputs i) = Zmod.unsigned (N.v17604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17604 s i)) at 1.
  unfold R.v17604, N.v17604.
  rewrite ?node_17598.
  rewrite ?node_17599.
  rewrite ?node_17603.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17605 (s : N.State) (i : N.Inputs) :
  R.v17605 (state s) (inputs i) = Zmod.unsigned (N.v17605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17605 s i)) at 1.
  unfold R.v17605, N.v17605.
  unfold R.v6, N.v6.
  rewrite ?node_17604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17606 (s : N.State) (i : N.Inputs) :
  R.v17606 (state s) (inputs i) = Zmod.unsigned (N.v17606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17606 s i)) at 1.
  unfold R.v17606, N.v17606.
  rewrite ?node_5664.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17607 (s : N.State) (i : N.Inputs) :
  R.v17607 (state s) (inputs i) = Zmod.unsigned (N.v17607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17607 s i)) at 1.
  unfold R.v17607, N.v17607.
  unfold R.v6, N.v6.
  rewrite ?node_5721.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17608 (s : N.State) (i : N.Inputs) :
  R.v17608 (state s) (inputs i) = Zmod.unsigned (N.v17608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17608 s i)) at 1.
  unfold R.v17608, N.v17608.
  unfold R.v6, N.v6.
  rewrite ?node_5735.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17609 (s : N.State) (i : N.Inputs) :
  R.v17609 (state s) (inputs i) = Zmod.unsigned (N.v17609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17609 s i)) at 1.
  unfold R.v17609, N.v17609.
  rewrite ?node_17606.
  rewrite ?node_17607.
  rewrite ?node_17608.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17610 (s : N.State) (i : N.Inputs) :
  R.v17610 (state s) (inputs i) = Zmod.unsigned (N.v17610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17610 s i)) at 1.
  unfold R.v17610, N.v17610.
  rewrite ?node_17605.
  rewrite ?node_17609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17611 (s : N.State) (i : N.Inputs) :
  R.v17611 (state s) (inputs i) = Zmod.unsigned (N.v17611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17611 s i)) at 1.
  unfold R.v17611, N.v17611.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17612 (s : N.State) (i : N.Inputs) :
  R.v17612 (state s) (inputs i) = Zmod.unsigned (N.v17612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17612 s i)) at 1.
  unfold R.v17612, N.v17612.
  unfold R.v16463, N.v16463.
  rewrite !state_r140_nr_5F140.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r140_nr_5F140 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17613 (s : N.State) (i : N.Inputs) :
  R.v17613 (state s) (inputs i) = Zmod.unsigned (N.v17613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17613 s i)) at 1.
  unfold R.v17613, N.v17613.
  unfold R.v6, N.v6.
  rewrite !state_r139_nr_5F139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r139_nr_5F139 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17614 (s : N.State) (i : N.Inputs) :
  R.v17614 (state s) (inputs i) = Zmod.unsigned (N.v17614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17614 s i)) at 1.
  unfold R.v17614, N.v17614.
  unfold R.v6, N.v6.
  rewrite !state_r138_nr_5F138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r138_nr_5F138 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17615 (s : N.State) (i : N.Inputs) :
  R.v17615 (state s) (inputs i) = Zmod.unsigned (N.v17615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17615 s i)) at 1.
  unfold R.v17615, N.v17615.
  rewrite ?node_17613.
  rewrite ?node_17614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17616 (s : N.State) (i : N.Inputs) :
  R.v17616 (state s) (inputs i) = Zmod.unsigned (N.v17616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17616 s i)) at 1.
  unfold R.v17616, N.v17616.
  unfold R.v16484, N.v16484.
  rewrite ?node_17615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17617 (s : N.State) (i : N.Inputs) :
  R.v17617 (state s) (inputs i) = Zmod.unsigned (N.v17617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17617 s i)) at 1.
  unfold R.v17617, N.v17617.
  rewrite ?node_17612.
  rewrite ?node_17616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17618 (s : N.State) (i : N.Inputs) :
  R.v17618 (state s) (inputs i) = Zmod.unsigned (N.v17618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17618 s i)) at 1.
  unfold R.v17618, N.v17618.
  unfold R.v6, N.v6.
  rewrite ?node_17617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17619 (s : N.State) (i : N.Inputs) :
  R.v17619 (state s) (inputs i) = Zmod.unsigned (N.v17619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17619 s i)) at 1.
  unfold R.v17619, N.v17619.
  rewrite ?node_5663.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17620 (s : N.State) (i : N.Inputs) :
  R.v17620 (state s) (inputs i) = Zmod.unsigned (N.v17620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17620 s i)) at 1.
  unfold R.v17620, N.v17620.
  unfold R.v6, N.v6.
  rewrite ?node_5721.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17621 (s : N.State) (i : N.Inputs) :
  R.v17621 (state s) (inputs i) = Zmod.unsigned (N.v17621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17621 s i)) at 1.
  unfold R.v17621, N.v17621.
  rewrite ?node_17619.
  rewrite ?node_17620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17622 (s : N.State) (i : N.Inputs) :
  R.v17622 (state s) (inputs i) = Zmod.unsigned (N.v17622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17622 s i)) at 1.
  unfold R.v17622, N.v17622.
  rewrite ?node_17618.
  rewrite ?node_17621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17623 (s : N.State) (i : N.Inputs) :
  R.v17623 (state s) (inputs i) = Zmod.unsigned (N.v17623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17623 s i)) at 1.
  unfold R.v17623, N.v17623.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17624 (s : N.State) (i : N.Inputs) :
  R.v17624 (state s) (inputs i) = Zmod.unsigned (N.v17624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17624 s i)) at 1.
  unfold R.v17624, N.v17624.
  unfold R.v6, N.v6.
  rewrite !state_r141_nr_5F141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r141_nr_5F141 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17625 (s : N.State) (i : N.Inputs) :
  R.v17625 (state s) (inputs i) = Zmod.unsigned (N.v17625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17625 s i)) at 1.
  unfold R.v17625, N.v17625.
  unfold R.v6, N.v6.
  rewrite ?node_5663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17626 (s : N.State) (i : N.Inputs) :
  R.v17626 (state s) (inputs i) = Zmod.unsigned (N.v17626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17626 s i)) at 1.
  unfold R.v17626, N.v17626.
  rewrite ?node_17624.
  rewrite ?node_17625.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17627 (s : N.State) (i : N.Inputs) :
  R.v17627 (state s) (inputs i) = Zmod.unsigned (N.v17627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17627 s i)) at 1.
  unfold R.v17627, N.v17627.
  unfold R.v16463, N.v16463.
  rewrite ?node_17626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17628 (s : N.State) (i : N.Inputs) :
  R.v17628 (state s) (inputs i) = Zmod.unsigned (N.v17628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17628 s i)) at 1.
  unfold R.v17628, N.v17628.
  rewrite ?node_5664.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17629 (s : N.State) (i : N.Inputs) :
  R.v17629 (state s) (inputs i) = Zmod.unsigned (N.v17629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17629 s i)) at 1.
  unfold R.v17629, N.v17629.
  unfold R.v6, N.v6.
  rewrite ?node_5735.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17630 (s : N.State) (i : N.Inputs) :
  R.v17630 (state s) (inputs i) = Zmod.unsigned (N.v17630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17630 s i)) at 1.
  unfold R.v17630, N.v17630.
  rewrite ?node_17628.
  rewrite ?node_17629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17631 (s : N.State) (i : N.Inputs) :
  R.v17631 (state s) (inputs i) = Zmod.unsigned (N.v17631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17631 s i)) at 1.
  unfold R.v17631, N.v17631.
  rewrite ?node_17627.
  rewrite ?node_17630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17632 (s : N.State) (i : N.Inputs) :
  R.v17632 (state s) (inputs i) = Zmod.unsigned (N.v17632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17632 s i)) at 1.
  unfold R.v17632, N.v17632.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17633 (s : N.State) (i : N.Inputs) :
  R.v17633 (state s) (inputs i) = Zmod.unsigned (N.v17633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17633 s i)) at 1.
  unfold R.v17633, N.v17633.
  rewrite ?node_5706.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17634 (s : N.State) (i : N.Inputs) :
  R.v17634 (state s) (inputs i) = Zmod.unsigned (N.v17634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17634 s i)) at 1.
  unfold R.v17634, N.v17634.
  unfold R.v16463, N.v16463.
  rewrite !state_r145_nr_5F145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r145_nr_5F145 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17635 (s : N.State) (i : N.Inputs) :
  R.v17635 (state s) (inputs i) = Zmod.unsigned (N.v17635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17635 s i)) at 1.
  unfold R.v17635, N.v17635.
  unfold R.v16463, N.v16463.
  rewrite !state_r144_nr_5F144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r144_nr_5F144 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17636 (s : N.State) (i : N.Inputs) :
  R.v17636 (state s) (inputs i) = Zmod.unsigned (N.v17636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17636 s i)) at 1.
  unfold R.v17636, N.v17636.
  unfold R.v6, N.v6.
  rewrite !state_r143_nr_5F143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r143_nr_5F143 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17637 (s : N.State) (i : N.Inputs) :
  R.v17637 (state s) (inputs i) = Zmod.unsigned (N.v17637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17637 s i)) at 1.
  unfold R.v17637, N.v17637.
  unfold R.v6, N.v6.
  rewrite !state_r142_nr_5F142.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r142_nr_5F142 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17638 (s : N.State) (i : N.Inputs) :
  R.v17638 (state s) (inputs i) = Zmod.unsigned (N.v17638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17638 s i)) at 1.
  unfold R.v17638, N.v17638.
  rewrite ?node_17636.
  rewrite ?node_17637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17639 (s : N.State) (i : N.Inputs) :
  R.v17639 (state s) (inputs i) = Zmod.unsigned (N.v17639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17639 s i)) at 1.
  unfold R.v17639, N.v17639.
  unfold R.v16484, N.v16484.
  rewrite ?node_17638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17640 (s : N.State) (i : N.Inputs) :
  R.v17640 (state s) (inputs i) = Zmod.unsigned (N.v17640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17640 s i)) at 1.
  unfold R.v17640, N.v17640.
  rewrite ?node_17633.
  rewrite ?node_17634.
  rewrite ?node_17635.
  rewrite ?node_17639.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17641 (s : N.State) (i : N.Inputs) :
  R.v17641 (state s) (inputs i) = Zmod.unsigned (N.v17641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17641 s i)) at 1.
  unfold R.v17641, N.v17641.
  unfold R.v6, N.v6.
  rewrite ?node_17640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17642 (s : N.State) (i : N.Inputs) :
  R.v17642 (state s) (inputs i) = Zmod.unsigned (N.v17642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17642 s i)) at 1.
  unfold R.v17642, N.v17642.
  rewrite ?node_5707.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17643 (s : N.State) (i : N.Inputs) :
  R.v17643 (state s) (inputs i) = Zmod.unsigned (N.v17643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17643 s i)) at 1.
  unfold R.v17643, N.v17643.
  unfold R.v6, N.v6.
  rewrite ?node_5762.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17644 (s : N.State) (i : N.Inputs) :
  R.v17644 (state s) (inputs i) = Zmod.unsigned (N.v17644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17644 s i)) at 1.
  unfold R.v17644, N.v17644.
  unfold R.v6, N.v6.
  rewrite ?node_5787.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17645 (s : N.State) (i : N.Inputs) :
  R.v17645 (state s) (inputs i) = Zmod.unsigned (N.v17645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17645 s i)) at 1.
  unfold R.v17645, N.v17645.
  rewrite ?node_17642.
  rewrite ?node_17643.
  rewrite ?node_17644.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17646 (s : N.State) (i : N.Inputs) :
  R.v17646 (state s) (inputs i) = Zmod.unsigned (N.v17646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17646 s i)) at 1.
  unfold R.v17646, N.v17646.
  rewrite ?node_17641.
  rewrite ?node_17645.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17647 (s : N.State) (i : N.Inputs) :
  R.v17647 (state s) (inputs i) = Zmod.unsigned (N.v17647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17647 s i)) at 1.
  unfold R.v17647, N.v17647.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17648 (s : N.State) (i : N.Inputs) :
  R.v17648 (state s) (inputs i) = Zmod.unsigned (N.v17648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17648 s i)) at 1.
  unfold R.v17648, N.v17648.
  unfold R.v16463, N.v16463.
  rewrite !state_r144_nr_5F144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r144_nr_5F144 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17649 (s : N.State) (i : N.Inputs) :
  R.v17649 (state s) (inputs i) = Zmod.unsigned (N.v17649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17649 s i)) at 1.
  unfold R.v17649, N.v17649.
  unfold R.v6, N.v6.
  rewrite !state_r143_nr_5F143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r143_nr_5F143 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17650 (s : N.State) (i : N.Inputs) :
  R.v17650 (state s) (inputs i) = Zmod.unsigned (N.v17650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17650 s i)) at 1.
  unfold R.v17650, N.v17650.
  unfold R.v6, N.v6.
  rewrite !state_r142_nr_5F142.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r142_nr_5F142 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17651 (s : N.State) (i : N.Inputs) :
  R.v17651 (state s) (inputs i) = Zmod.unsigned (N.v17651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17651 s i)) at 1.
  unfold R.v17651, N.v17651.
  rewrite ?node_17649.
  rewrite ?node_17650.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17652 (s : N.State) (i : N.Inputs) :
  R.v17652 (state s) (inputs i) = Zmod.unsigned (N.v17652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17652 s i)) at 1.
  unfold R.v17652, N.v17652.
  unfold R.v16484, N.v16484.
  rewrite ?node_17651.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17653 (s : N.State) (i : N.Inputs) :
  R.v17653 (state s) (inputs i) = Zmod.unsigned (N.v17653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17653 s i)) at 1.
  unfold R.v17653, N.v17653.
  rewrite ?node_17648.
  rewrite ?node_17652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17654 (s : N.State) (i : N.Inputs) :
  R.v17654 (state s) (inputs i) = Zmod.unsigned (N.v17654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17654 s i)) at 1.
  unfold R.v17654, N.v17654.
  unfold R.v6, N.v6.
  rewrite ?node_17653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17655 (s : N.State) (i : N.Inputs) :
  R.v17655 (state s) (inputs i) = Zmod.unsigned (N.v17655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17655 s i)) at 1.
  unfold R.v17655, N.v17655.
  rewrite ?node_5702.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17656 (s : N.State) (i : N.Inputs) :
  R.v17656 (state s) (inputs i) = Zmod.unsigned (N.v17656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17656 s i)) at 1.
  unfold R.v17656, N.v17656.
  unfold R.v6, N.v6.
  rewrite ?node_5762.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17657 (s : N.State) (i : N.Inputs) :
  R.v17657 (state s) (inputs i) = Zmod.unsigned (N.v17657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17657 s i)) at 1.
  unfold R.v17657, N.v17657.
  rewrite ?node_17655.
  rewrite ?node_17656.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17658 (s : N.State) (i : N.Inputs) :
  R.v17658 (state s) (inputs i) = Zmod.unsigned (N.v17658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17658 s i)) at 1.
  unfold R.v17658, N.v17658.
  rewrite ?node_17654.
  rewrite ?node_17657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17659 (s : N.State) (i : N.Inputs) :
  R.v17659 (state s) (inputs i) = Zmod.unsigned (N.v17659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17659 s i)) at 1.
  unfold R.v17659, N.v17659.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17660 (s : N.State) (i : N.Inputs) :
  R.v17660 (state s) (inputs i) = Zmod.unsigned (N.v17660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17660 s i)) at 1.
  unfold R.v17660, N.v17660.
  rewrite ?node_5706.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17661 (s : N.State) (i : N.Inputs) :
  R.v17661 (state s) (inputs i) = Zmod.unsigned (N.v17661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17661 s i)) at 1.
  unfold R.v17661, N.v17661.
  unfold R.v6, N.v6.
  rewrite !state_r145_nr_5F145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r145_nr_5F145 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17662 (s : N.State) (i : N.Inputs) :
  R.v17662 (state s) (inputs i) = Zmod.unsigned (N.v17662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17662 s i)) at 1.
  unfold R.v17662, N.v17662.
  unfold R.v6, N.v6.
  rewrite ?node_5702.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17663 (s : N.State) (i : N.Inputs) :
  R.v17663 (state s) (inputs i) = Zmod.unsigned (N.v17663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17663 s i)) at 1.
  unfold R.v17663, N.v17663.
  rewrite ?node_17661.
  rewrite ?node_17662.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17664 (s : N.State) (i : N.Inputs) :
  R.v17664 (state s) (inputs i) = Zmod.unsigned (N.v17664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17664 s i)) at 1.
  unfold R.v17664, N.v17664.
  unfold R.v16484, N.v16484.
  rewrite ?node_17663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17665 (s : N.State) (i : N.Inputs) :
  R.v17665 (state s) (inputs i) = Zmod.unsigned (N.v17665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17665 s i)) at 1.
  unfold R.v17665, N.v17665.
  rewrite ?node_17660.
  rewrite ?node_17664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17666 (s : N.State) (i : N.Inputs) :
  R.v17666 (state s) (inputs i) = Zmod.unsigned (N.v17666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17666 s i)) at 1.
  unfold R.v17666, N.v17666.
  unfold R.v6, N.v6.
  rewrite ?node_17665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17667 (s : N.State) (i : N.Inputs) :
  R.v17667 (state s) (inputs i) = Zmod.unsigned (N.v17667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17667 s i)) at 1.
  unfold R.v17667, N.v17667.
  rewrite ?node_5707.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17668 (s : N.State) (i : N.Inputs) :
  R.v17668 (state s) (inputs i) = Zmod.unsigned (N.v17668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17668 s i)) at 1.
  unfold R.v17668, N.v17668.
  unfold R.v6, N.v6.
  rewrite ?node_5787.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17669 (s : N.State) (i : N.Inputs) :
  R.v17669 (state s) (inputs i) = Zmod.unsigned (N.v17669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17669 s i)) at 1.
  unfold R.v17669, N.v17669.
  rewrite ?node_17667.
  rewrite ?node_17668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17670 (s : N.State) (i : N.Inputs) :
  R.v17670 (state s) (inputs i) = Zmod.unsigned (N.v17670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17670 s i)) at 1.
  unfold R.v17670, N.v17670.
  rewrite ?node_17666.
  rewrite ?node_17669.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17671 (s : N.State) (i : N.Inputs) :
  R.v17671 (state s) (inputs i) = Zmod.unsigned (N.v17671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17671 s i)) at 1.
  unfold R.v17671, N.v17671.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17672 (s : N.State) (i : N.Inputs) :
  R.v17672 (state s) (inputs i) = Zmod.unsigned (N.v17672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17672 s i)) at 1.
  unfold R.v17672, N.v17672.
  rewrite ?node_5713.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17673 (s : N.State) (i : N.Inputs) :
  R.v17673 (state s) (inputs i) = Zmod.unsigned (N.v17673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17673 s i)) at 1.
  unfold R.v17673, N.v17673.
  unfold R.v16463, N.v16463.
  rewrite !state_r149_nr_5F149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r149_nr_5F149 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17674 (s : N.State) (i : N.Inputs) :
  R.v17674 (state s) (inputs i) = Zmod.unsigned (N.v17674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17674 s i)) at 1.
  unfold R.v17674, N.v17674.
  unfold R.v16463, N.v16463.
  rewrite !state_r148_nr_5F148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r148_nr_5F148 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17675 (s : N.State) (i : N.Inputs) :
  R.v17675 (state s) (inputs i) = Zmod.unsigned (N.v17675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17675 s i)) at 1.
  unfold R.v17675, N.v17675.
  unfold R.v6, N.v6.
  rewrite !state_r147_nr_5F147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r147_nr_5F147 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17676 (s : N.State) (i : N.Inputs) :
  R.v17676 (state s) (inputs i) = Zmod.unsigned (N.v17676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17676 s i)) at 1.
  unfold R.v17676, N.v17676.
  unfold R.v6, N.v6.
  rewrite !state_r146_nr_5F146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r146_nr_5F146 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17677 (s : N.State) (i : N.Inputs) :
  R.v17677 (state s) (inputs i) = Zmod.unsigned (N.v17677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17677 s i)) at 1.
  unfold R.v17677, N.v17677.
  rewrite ?node_17675.
  rewrite ?node_17676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17678 (s : N.State) (i : N.Inputs) :
  R.v17678 (state s) (inputs i) = Zmod.unsigned (N.v17678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17678 s i)) at 1.
  unfold R.v17678, N.v17678.
  unfold R.v16484, N.v16484.
  rewrite ?node_17677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17679 (s : N.State) (i : N.Inputs) :
  R.v17679 (state s) (inputs i) = Zmod.unsigned (N.v17679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17679 s i)) at 1.
  unfold R.v17679, N.v17679.
  rewrite ?node_17672.
  rewrite ?node_17673.
  rewrite ?node_17674.
  rewrite ?node_17678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17680 (s : N.State) (i : N.Inputs) :
  R.v17680 (state s) (inputs i) = Zmod.unsigned (N.v17680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17680 s i)) at 1.
  unfold R.v17680, N.v17680.
  unfold R.v6, N.v6.
  rewrite ?node_17679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17681 (s : N.State) (i : N.Inputs) :
  R.v17681 (state s) (inputs i) = Zmod.unsigned (N.v17681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17681 s i)) at 1.
  unfold R.v17681, N.v17681.
  rewrite ?node_5714.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17682 (s : N.State) (i : N.Inputs) :
  R.v17682 (state s) (inputs i) = Zmod.unsigned (N.v17682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17682 s i)) at 1.
  unfold R.v17682, N.v17682.
  unfold R.v6, N.v6.
  rewrite ?node_5769.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17683 (s : N.State) (i : N.Inputs) :
  R.v17683 (state s) (inputs i) = Zmod.unsigned (N.v17683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17683 s i)) at 1.
  unfold R.v17683, N.v17683.
  unfold R.v6, N.v6.
  rewrite ?node_5790.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17684 (s : N.State) (i : N.Inputs) :
  R.v17684 (state s) (inputs i) = Zmod.unsigned (N.v17684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17684 s i)) at 1.
  unfold R.v17684, N.v17684.
  rewrite ?node_17681.
  rewrite ?node_17682.
  rewrite ?node_17683.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17685 (s : N.State) (i : N.Inputs) :
  R.v17685 (state s) (inputs i) = Zmod.unsigned (N.v17685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17685 s i)) at 1.
  unfold R.v17685, N.v17685.
  rewrite ?node_17680.
  rewrite ?node_17684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17686 (s : N.State) (i : N.Inputs) :
  R.v17686 (state s) (inputs i) = Zmod.unsigned (N.v17686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17686 s i)) at 1.
  unfold R.v17686, N.v17686.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17687 (s : N.State) (i : N.Inputs) :
  R.v17687 (state s) (inputs i) = Zmod.unsigned (N.v17687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17687 s i)) at 1.
  unfold R.v17687, N.v17687.
  unfold R.v16463, N.v16463.
  rewrite !state_r148_nr_5F148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r148_nr_5F148 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17688 (s : N.State) (i : N.Inputs) :
  R.v17688 (state s) (inputs i) = Zmod.unsigned (N.v17688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17688 s i)) at 1.
  unfold R.v17688, N.v17688.
  unfold R.v6, N.v6.
  rewrite !state_r147_nr_5F147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r147_nr_5F147 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17689 (s : N.State) (i : N.Inputs) :
  R.v17689 (state s) (inputs i) = Zmod.unsigned (N.v17689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17689 s i)) at 1.
  unfold R.v17689, N.v17689.
  unfold R.v6, N.v6.
  rewrite !state_r146_nr_5F146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r146_nr_5F146 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17690 (s : N.State) (i : N.Inputs) :
  R.v17690 (state s) (inputs i) = Zmod.unsigned (N.v17690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17690 s i)) at 1.
  unfold R.v17690, N.v17690.
  rewrite ?node_17688.
  rewrite ?node_17689.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17691 (s : N.State) (i : N.Inputs) :
  R.v17691 (state s) (inputs i) = Zmod.unsigned (N.v17691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17691 s i)) at 1.
  unfold R.v17691, N.v17691.
  unfold R.v16484, N.v16484.
  rewrite ?node_17690.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17692 (s : N.State) (i : N.Inputs) :
  R.v17692 (state s) (inputs i) = Zmod.unsigned (N.v17692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17692 s i)) at 1.
  unfold R.v17692, N.v17692.
  rewrite ?node_17687.
  rewrite ?node_17691.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17693 (s : N.State) (i : N.Inputs) :
  R.v17693 (state s) (inputs i) = Zmod.unsigned (N.v17693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17693 s i)) at 1.
  unfold R.v17693, N.v17693.
  unfold R.v6, N.v6.
  rewrite ?node_17692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17694 (s : N.State) (i : N.Inputs) :
  R.v17694 (state s) (inputs i) = Zmod.unsigned (N.v17694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17694 s i)) at 1.
  unfold R.v17694, N.v17694.
  rewrite ?node_5709.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17695 (s : N.State) (i : N.Inputs) :
  R.v17695 (state s) (inputs i) = Zmod.unsigned (N.v17695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17695 s i)) at 1.
  unfold R.v17695, N.v17695.
  unfold R.v6, N.v6.
  rewrite ?node_5769.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17696 (s : N.State) (i : N.Inputs) :
  R.v17696 (state s) (inputs i) = Zmod.unsigned (N.v17696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17696 s i)) at 1.
  unfold R.v17696, N.v17696.
  rewrite ?node_17694.
  rewrite ?node_17695.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17697 (s : N.State) (i : N.Inputs) :
  R.v17697 (state s) (inputs i) = Zmod.unsigned (N.v17697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17697 s i)) at 1.
  unfold R.v17697, N.v17697.
  rewrite ?node_17693.
  rewrite ?node_17696.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17698 (s : N.State) (i : N.Inputs) :
  R.v17698 (state s) (inputs i) = Zmod.unsigned (N.v17698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17698 s i)) at 1.
  unfold R.v17698, N.v17698.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17699 (s : N.State) (i : N.Inputs) :
  R.v17699 (state s) (inputs i) = Zmod.unsigned (N.v17699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17699 s i)) at 1.
  unfold R.v17699, N.v17699.
  rewrite ?node_5713.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17700 (s : N.State) (i : N.Inputs) :
  R.v17700 (state s) (inputs i) = Zmod.unsigned (N.v17700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17700 s i)) at 1.
  unfold R.v17700, N.v17700.
  unfold R.v6, N.v6.
  rewrite !state_r149_nr_5F149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r149_nr_5F149 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17701 (s : N.State) (i : N.Inputs) :
  R.v17701 (state s) (inputs i) = Zmod.unsigned (N.v17701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17701 s i)) at 1.
  unfold R.v17701, N.v17701.
  unfold R.v6, N.v6.
  rewrite ?node_5709.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17702 (s : N.State) (i : N.Inputs) :
  R.v17702 (state s) (inputs i) = Zmod.unsigned (N.v17702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17702 s i)) at 1.
  unfold R.v17702, N.v17702.
  rewrite ?node_17700.
  rewrite ?node_17701.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17703 (s : N.State) (i : N.Inputs) :
  R.v17703 (state s) (inputs i) = Zmod.unsigned (N.v17703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17703 s i)) at 1.
  unfold R.v17703, N.v17703.
  unfold R.v16484, N.v16484.
  rewrite ?node_17702.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17704 (s : N.State) (i : N.Inputs) :
  R.v17704 (state s) (inputs i) = Zmod.unsigned (N.v17704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17704 s i)) at 1.
  unfold R.v17704, N.v17704.
  rewrite ?node_17699.
  rewrite ?node_17703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17705 (s : N.State) (i : N.Inputs) :
  R.v17705 (state s) (inputs i) = Zmod.unsigned (N.v17705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17705 s i)) at 1.
  unfold R.v17705, N.v17705.
  unfold R.v6, N.v6.
  rewrite ?node_17704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17706 (s : N.State) (i : N.Inputs) :
  R.v17706 (state s) (inputs i) = Zmod.unsigned (N.v17706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17706 s i)) at 1.
  unfold R.v17706, N.v17706.
  rewrite ?node_5714.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17707 (s : N.State) (i : N.Inputs) :
  R.v17707 (state s) (inputs i) = Zmod.unsigned (N.v17707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17707 s i)) at 1.
  unfold R.v17707, N.v17707.
  unfold R.v6, N.v6.
  rewrite ?node_5790.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17708 (s : N.State) (i : N.Inputs) :
  R.v17708 (state s) (inputs i) = Zmod.unsigned (N.v17708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17708 s i)) at 1.
  unfold R.v17708, N.v17708.
  rewrite ?node_17706.
  rewrite ?node_17707.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17709 (s : N.State) (i : N.Inputs) :
  R.v17709 (state s) (inputs i) = Zmod.unsigned (N.v17709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17709 s i)) at 1.
  unfold R.v17709, N.v17709.
  rewrite ?node_17705.
  rewrite ?node_17708.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17710 (s : N.State) (i : N.Inputs) :
  R.v17710 (state s) (inputs i) = Zmod.unsigned (N.v17710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17710 s i)) at 1.
  unfold R.v17710, N.v17710.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17711 (s : N.State) (i : N.Inputs) :
  R.v17711 (state s) (inputs i) = Zmod.unsigned (N.v17711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17711 s i)) at 1.
  unfold R.v17711, N.v17711.
  rewrite ?node_5721.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17712 (s : N.State) (i : N.Inputs) :
  R.v17712 (state s) (inputs i) = Zmod.unsigned (N.v17712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17712 s i)) at 1.
  unfold R.v17712, N.v17712.
  unfold R.v16463, N.v16463.
  rewrite !state_r153_nr_5F153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r153_nr_5F153 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17713 (s : N.State) (i : N.Inputs) :
  R.v17713 (state s) (inputs i) = Zmod.unsigned (N.v17713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17713 s i)) at 1.
  unfold R.v17713, N.v17713.
  unfold R.v16463, N.v16463.
  rewrite !state_r152_nr_5F152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r152_nr_5F152 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17714 (s : N.State) (i : N.Inputs) :
  R.v17714 (state s) (inputs i) = Zmod.unsigned (N.v17714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17714 s i)) at 1.
  unfold R.v17714, N.v17714.
  unfold R.v6, N.v6.
  rewrite !state_r151_nr_5F151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r151_nr_5F151 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17715 (s : N.State) (i : N.Inputs) :
  R.v17715 (state s) (inputs i) = Zmod.unsigned (N.v17715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17715 s i)) at 1.
  unfold R.v17715, N.v17715.
  unfold R.v6, N.v6.
  rewrite !state_r150_nr_5F150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r150_nr_5F150 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17716 (s : N.State) (i : N.Inputs) :
  R.v17716 (state s) (inputs i) = Zmod.unsigned (N.v17716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17716 s i)) at 1.
  unfold R.v17716, N.v17716.
  rewrite ?node_17714.
  rewrite ?node_17715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17717 (s : N.State) (i : N.Inputs) :
  R.v17717 (state s) (inputs i) = Zmod.unsigned (N.v17717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17717 s i)) at 1.
  unfold R.v17717, N.v17717.
  unfold R.v16484, N.v16484.
  rewrite ?node_17716.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17718 (s : N.State) (i : N.Inputs) :
  R.v17718 (state s) (inputs i) = Zmod.unsigned (N.v17718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17718 s i)) at 1.
  unfold R.v17718, N.v17718.
  rewrite ?node_17711.
  rewrite ?node_17712.
  rewrite ?node_17713.
  rewrite ?node_17717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17719 (s : N.State) (i : N.Inputs) :
  R.v17719 (state s) (inputs i) = Zmod.unsigned (N.v17719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17719 s i)) at 1.
  unfold R.v17719, N.v17719.
  unfold R.v6, N.v6.
  rewrite ?node_17718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17720 (s : N.State) (i : N.Inputs) :
  R.v17720 (state s) (inputs i) = Zmod.unsigned (N.v17720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17720 s i)) at 1.
  unfold R.v17720, N.v17720.
  rewrite ?node_5722.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17721 (s : N.State) (i : N.Inputs) :
  R.v17721 (state s) (inputs i) = Zmod.unsigned (N.v17721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17721 s i)) at 1.
  unfold R.v17721, N.v17721.
  unfold R.v6, N.v6.
  rewrite ?node_5777.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17722 (s : N.State) (i : N.Inputs) :
  R.v17722 (state s) (inputs i) = Zmod.unsigned (N.v17722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17722 s i)) at 1.
  unfold R.v17722, N.v17722.
  unfold R.v6, N.v6.
  rewrite ?node_5794.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17723 (s : N.State) (i : N.Inputs) :
  R.v17723 (state s) (inputs i) = Zmod.unsigned (N.v17723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17723 s i)) at 1.
  unfold R.v17723, N.v17723.
  rewrite ?node_17720.
  rewrite ?node_17721.
  rewrite ?node_17722.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17724 (s : N.State) (i : N.Inputs) :
  R.v17724 (state s) (inputs i) = Zmod.unsigned (N.v17724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17724 s i)) at 1.
  unfold R.v17724, N.v17724.
  rewrite ?node_17719.
  rewrite ?node_17723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17725 (s : N.State) (i : N.Inputs) :
  R.v17725 (state s) (inputs i) = Zmod.unsigned (N.v17725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17725 s i)) at 1.
  unfold R.v17725, N.v17725.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17726 (s : N.State) (i : N.Inputs) :
  R.v17726 (state s) (inputs i) = Zmod.unsigned (N.v17726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17726 s i)) at 1.
  unfold R.v17726, N.v17726.
  unfold R.v16463, N.v16463.
  rewrite !state_r152_nr_5F152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r152_nr_5F152 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17727 (s : N.State) (i : N.Inputs) :
  R.v17727 (state s) (inputs i) = Zmod.unsigned (N.v17727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17727 s i)) at 1.
  unfold R.v17727, N.v17727.
  unfold R.v6, N.v6.
  rewrite !state_r151_nr_5F151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r151_nr_5F151 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17728 (s : N.State) (i : N.Inputs) :
  R.v17728 (state s) (inputs i) = Zmod.unsigned (N.v17728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17728 s i)) at 1.
  unfold R.v17728, N.v17728.
  unfold R.v6, N.v6.
  rewrite !state_r150_nr_5F150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r150_nr_5F150 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17729 (s : N.State) (i : N.Inputs) :
  R.v17729 (state s) (inputs i) = Zmod.unsigned (N.v17729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17729 s i)) at 1.
  unfold R.v17729, N.v17729.
  rewrite ?node_17727.
  rewrite ?node_17728.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17730 (s : N.State) (i : N.Inputs) :
  R.v17730 (state s) (inputs i) = Zmod.unsigned (N.v17730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17730 s i)) at 1.
  unfold R.v17730, N.v17730.
  unfold R.v16484, N.v16484.
  rewrite ?node_17729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17731 (s : N.State) (i : N.Inputs) :
  R.v17731 (state s) (inputs i) = Zmod.unsigned (N.v17731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17731 s i)) at 1.
  unfold R.v17731, N.v17731.
  rewrite ?node_17726.
  rewrite ?node_17730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17732 (s : N.State) (i : N.Inputs) :
  R.v17732 (state s) (inputs i) = Zmod.unsigned (N.v17732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17732 s i)) at 1.
  unfold R.v17732, N.v17732.
  unfold R.v6, N.v6.
  rewrite ?node_17731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17733 (s : N.State) (i : N.Inputs) :
  R.v17733 (state s) (inputs i) = Zmod.unsigned (N.v17733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17733 s i)) at 1.
  unfold R.v17733, N.v17733.
  rewrite ?node_5717.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17734 (s : N.State) (i : N.Inputs) :
  R.v17734 (state s) (inputs i) = Zmod.unsigned (N.v17734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17734 s i)) at 1.
  unfold R.v17734, N.v17734.
  unfold R.v6, N.v6.
  rewrite ?node_5777.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17735 (s : N.State) (i : N.Inputs) :
  R.v17735 (state s) (inputs i) = Zmod.unsigned (N.v17735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17735 s i)) at 1.
  unfold R.v17735, N.v17735.
  rewrite ?node_17733.
  rewrite ?node_17734.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17736 (s : N.State) (i : N.Inputs) :
  R.v17736 (state s) (inputs i) = Zmod.unsigned (N.v17736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17736 s i)) at 1.
  unfold R.v17736, N.v17736.
  rewrite ?node_17732.
  rewrite ?node_17735.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17737 (s : N.State) (i : N.Inputs) :
  R.v17737 (state s) (inputs i) = Zmod.unsigned (N.v17737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17737 s i)) at 1.
  unfold R.v17737, N.v17737.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17738 (s : N.State) (i : N.Inputs) :
  R.v17738 (state s) (inputs i) = Zmod.unsigned (N.v17738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17738 s i)) at 1.
  unfold R.v17738, N.v17738.
  rewrite ?node_5721.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17739 (s : N.State) (i : N.Inputs) :
  R.v17739 (state s) (inputs i) = Zmod.unsigned (N.v17739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17739 s i)) at 1.
  unfold R.v17739, N.v17739.
  unfold R.v6, N.v6.
  rewrite !state_r153_nr_5F153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r153_nr_5F153 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17740 (s : N.State) (i : N.Inputs) :
  R.v17740 (state s) (inputs i) = Zmod.unsigned (N.v17740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17740 s i)) at 1.
  unfold R.v17740, N.v17740.
  unfold R.v6, N.v6.
  rewrite ?node_5717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17741 (s : N.State) (i : N.Inputs) :
  R.v17741 (state s) (inputs i) = Zmod.unsigned (N.v17741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17741 s i)) at 1.
  unfold R.v17741, N.v17741.
  rewrite ?node_17739.
  rewrite ?node_17740.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17742 (s : N.State) (i : N.Inputs) :
  R.v17742 (state s) (inputs i) = Zmod.unsigned (N.v17742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17742 s i)) at 1.
  unfold R.v17742, N.v17742.
  unfold R.v16484, N.v16484.
  rewrite ?node_17741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17743 (s : N.State) (i : N.Inputs) :
  R.v17743 (state s) (inputs i) = Zmod.unsigned (N.v17743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17743 s i)) at 1.
  unfold R.v17743, N.v17743.
  rewrite ?node_17738.
  rewrite ?node_17742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17744 (s : N.State) (i : N.Inputs) :
  R.v17744 (state s) (inputs i) = Zmod.unsigned (N.v17744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17744 s i)) at 1.
  unfold R.v17744, N.v17744.
  unfold R.v6, N.v6.
  rewrite ?node_17743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17745 (s : N.State) (i : N.Inputs) :
  R.v17745 (state s) (inputs i) = Zmod.unsigned (N.v17745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17745 s i)) at 1.
  unfold R.v17745, N.v17745.
  rewrite ?node_5722.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17746 (s : N.State) (i : N.Inputs) :
  R.v17746 (state s) (inputs i) = Zmod.unsigned (N.v17746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17746 s i)) at 1.
  unfold R.v17746, N.v17746.
  unfold R.v6, N.v6.
  rewrite ?node_5794.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17747 (s : N.State) (i : N.Inputs) :
  R.v17747 (state s) (inputs i) = Zmod.unsigned (N.v17747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17747 s i)) at 1.
  unfold R.v17747, N.v17747.
  rewrite ?node_17745.
  rewrite ?node_17746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17748 (s : N.State) (i : N.Inputs) :
  R.v17748 (state s) (inputs i) = Zmod.unsigned (N.v17748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17748 s i)) at 1.
  unfold R.v17748, N.v17748.
  rewrite ?node_17744.
  rewrite ?node_17747.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17749 (s : N.State) (i : N.Inputs) :
  R.v17749 (state s) (inputs i) = Zmod.unsigned (N.v17749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17749 s i)) at 1.
  unfold R.v17749, N.v17749.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17750 (s : N.State) (i : N.Inputs) :
  R.v17750 (state s) (inputs i) = Zmod.unsigned (N.v17750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17750 s i)) at 1.
  unfold R.v17750, N.v17750.
  rewrite ?node_5762.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17751 (s : N.State) (i : N.Inputs) :
  R.v17751 (state s) (inputs i) = Zmod.unsigned (N.v17751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17751 s i)) at 1.
  unfold R.v17751, N.v17751.
  unfold R.v16463, N.v16463.
  rewrite !state_r157_nr_5F157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r157_nr_5F157 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17752 (s : N.State) (i : N.Inputs) :
  R.v17752 (state s) (inputs i) = Zmod.unsigned (N.v17752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17752 s i)) at 1.
  unfold R.v17752, N.v17752.
  unfold R.v16463, N.v16463.
  rewrite !state_r156_nr_5F156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r156_nr_5F156 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17753 (s : N.State) (i : N.Inputs) :
  R.v17753 (state s) (inputs i) = Zmod.unsigned (N.v17753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17753 s i)) at 1.
  unfold R.v17753, N.v17753.
  unfold R.v6, N.v6.
  rewrite !state_r155_nr_5F155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r155_nr_5F155 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17754 (s : N.State) (i : N.Inputs) :
  R.v17754 (state s) (inputs i) = Zmod.unsigned (N.v17754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17754 s i)) at 1.
  unfold R.v17754, N.v17754.
  unfold R.v6, N.v6.
  rewrite !state_r154_nr_5F154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r154_nr_5F154 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17755 (s : N.State) (i : N.Inputs) :
  R.v17755 (state s) (inputs i) = Zmod.unsigned (N.v17755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17755 s i)) at 1.
  unfold R.v17755, N.v17755.
  rewrite ?node_17753.
  rewrite ?node_17754.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17756 (s : N.State) (i : N.Inputs) :
  R.v17756 (state s) (inputs i) = Zmod.unsigned (N.v17756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17756 s i)) at 1.
  unfold R.v17756, N.v17756.
  unfold R.v16484, N.v16484.
  rewrite ?node_17755.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17757 (s : N.State) (i : N.Inputs) :
  R.v17757 (state s) (inputs i) = Zmod.unsigned (N.v17757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17757 s i)) at 1.
  unfold R.v17757, N.v17757.
  rewrite ?node_17750.
  rewrite ?node_17751.
  rewrite ?node_17752.
  rewrite ?node_17756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17758 (s : N.State) (i : N.Inputs) :
  R.v17758 (state s) (inputs i) = Zmod.unsigned (N.v17758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17758 s i)) at 1.
  unfold R.v17758, N.v17758.
  unfold R.v6, N.v6.
  rewrite ?node_17757.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17759 (s : N.State) (i : N.Inputs) :
  R.v17759 (state s) (inputs i) = Zmod.unsigned (N.v17759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17759 s i)) at 1.
  unfold R.v17759, N.v17759.
  rewrite ?node_5763.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17760 (s : N.State) (i : N.Inputs) :
  R.v17760 (state s) (inputs i) = Zmod.unsigned (N.v17760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17760 s i)) at 1.
  unfold R.v17760, N.v17760.
  unfold R.v6, N.v6.
  rewrite ?node_5821.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17761 (s : N.State) (i : N.Inputs) :
  R.v17761 (state s) (inputs i) = Zmod.unsigned (N.v17761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17761 s i)) at 1.
  unfold R.v17761, N.v17761.
  unfold R.v6, N.v6.
  rewrite ?node_5846.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17762 (s : N.State) (i : N.Inputs) :
  R.v17762 (state s) (inputs i) = Zmod.unsigned (N.v17762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17762 s i)) at 1.
  unfold R.v17762, N.v17762.
  rewrite ?node_17759.
  rewrite ?node_17760.
  rewrite ?node_17761.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17763 (s : N.State) (i : N.Inputs) :
  R.v17763 (state s) (inputs i) = Zmod.unsigned (N.v17763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17763 s i)) at 1.
  unfold R.v17763, N.v17763.
  rewrite ?node_17758.
  rewrite ?node_17762.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17764 (s : N.State) (i : N.Inputs) :
  R.v17764 (state s) (inputs i) = Zmod.unsigned (N.v17764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17764 s i)) at 1.
  unfold R.v17764, N.v17764.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17765 (s : N.State) (i : N.Inputs) :
  R.v17765 (state s) (inputs i) = Zmod.unsigned (N.v17765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17765 s i)) at 1.
  unfold R.v17765, N.v17765.
  unfold R.v16463, N.v16463.
  rewrite !state_r156_nr_5F156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r156_nr_5F156 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17766 (s : N.State) (i : N.Inputs) :
  R.v17766 (state s) (inputs i) = Zmod.unsigned (N.v17766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17766 s i)) at 1.
  unfold R.v17766, N.v17766.
  unfold R.v6, N.v6.
  rewrite !state_r155_nr_5F155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r155_nr_5F155 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17767 (s : N.State) (i : N.Inputs) :
  R.v17767 (state s) (inputs i) = Zmod.unsigned (N.v17767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17767 s i)) at 1.
  unfold R.v17767, N.v17767.
  unfold R.v6, N.v6.
  rewrite !state_r154_nr_5F154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r154_nr_5F154 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17768 (s : N.State) (i : N.Inputs) :
  R.v17768 (state s) (inputs i) = Zmod.unsigned (N.v17768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17768 s i)) at 1.
  unfold R.v17768, N.v17768.
  rewrite ?node_17766.
  rewrite ?node_17767.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17769 (s : N.State) (i : N.Inputs) :
  R.v17769 (state s) (inputs i) = Zmod.unsigned (N.v17769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17769 s i)) at 1.
  unfold R.v17769, N.v17769.
  unfold R.v16484, N.v16484.
  rewrite ?node_17768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17770 (s : N.State) (i : N.Inputs) :
  R.v17770 (state s) (inputs i) = Zmod.unsigned (N.v17770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17770 s i)) at 1.
  unfold R.v17770, N.v17770.
  rewrite ?node_17765.
  rewrite ?node_17769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17771 (s : N.State) (i : N.Inputs) :
  R.v17771 (state s) (inputs i) = Zmod.unsigned (N.v17771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17771 s i)) at 1.
  unfold R.v17771, N.v17771.
  unfold R.v6, N.v6.
  rewrite ?node_17770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17772 (s : N.State) (i : N.Inputs) :
  R.v17772 (state s) (inputs i) = Zmod.unsigned (N.v17772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17772 s i)) at 1.
  unfold R.v17772, N.v17772.
  rewrite ?node_5758.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17773 (s : N.State) (i : N.Inputs) :
  R.v17773 (state s) (inputs i) = Zmod.unsigned (N.v17773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17773 s i)) at 1.
  unfold R.v17773, N.v17773.
  unfold R.v6, N.v6.
  rewrite ?node_5821.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17774 (s : N.State) (i : N.Inputs) :
  R.v17774 (state s) (inputs i) = Zmod.unsigned (N.v17774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17774 s i)) at 1.
  unfold R.v17774, N.v17774.
  rewrite ?node_17772.
  rewrite ?node_17773.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17775 (s : N.State) (i : N.Inputs) :
  R.v17775 (state s) (inputs i) = Zmod.unsigned (N.v17775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17775 s i)) at 1.
  unfold R.v17775, N.v17775.
  rewrite ?node_17771.
  rewrite ?node_17774.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17776 (s : N.State) (i : N.Inputs) :
  R.v17776 (state s) (inputs i) = Zmod.unsigned (N.v17776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17776 s i)) at 1.
  unfold R.v17776, N.v17776.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17777 (s : N.State) (i : N.Inputs) :
  R.v17777 (state s) (inputs i) = Zmod.unsigned (N.v17777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17777 s i)) at 1.
  unfold R.v17777, N.v17777.
  rewrite ?node_5762.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17778 (s : N.State) (i : N.Inputs) :
  R.v17778 (state s) (inputs i) = Zmod.unsigned (N.v17778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17778 s i)) at 1.
  unfold R.v17778, N.v17778.
  unfold R.v6, N.v6.
  rewrite !state_r157_nr_5F157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r157_nr_5F157 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17779 (s : N.State) (i : N.Inputs) :
  R.v17779 (state s) (inputs i) = Zmod.unsigned (N.v17779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17779 s i)) at 1.
  unfold R.v17779, N.v17779.
  unfold R.v6, N.v6.
  rewrite ?node_5758.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17780 (s : N.State) (i : N.Inputs) :
  R.v17780 (state s) (inputs i) = Zmod.unsigned (N.v17780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17780 s i)) at 1.
  unfold R.v17780, N.v17780.
  rewrite ?node_17778.
  rewrite ?node_17779.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17781 (s : N.State) (i : N.Inputs) :
  R.v17781 (state s) (inputs i) = Zmod.unsigned (N.v17781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17781 s i)) at 1.
  unfold R.v17781, N.v17781.
  unfold R.v16484, N.v16484.
  rewrite ?node_17780.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17782 (s : N.State) (i : N.Inputs) :
  R.v17782 (state s) (inputs i) = Zmod.unsigned (N.v17782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17782 s i)) at 1.
  unfold R.v17782, N.v17782.
  rewrite ?node_17777.
  rewrite ?node_17781.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17783 (s : N.State) (i : N.Inputs) :
  R.v17783 (state s) (inputs i) = Zmod.unsigned (N.v17783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17783 s i)) at 1.
  unfold R.v17783, N.v17783.
  unfold R.v6, N.v6.
  rewrite ?node_17782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17784 (s : N.State) (i : N.Inputs) :
  R.v17784 (state s) (inputs i) = Zmod.unsigned (N.v17784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17784 s i)) at 1.
  unfold R.v17784, N.v17784.
  rewrite ?node_5763.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17785 (s : N.State) (i : N.Inputs) :
  R.v17785 (state s) (inputs i) = Zmod.unsigned (N.v17785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17785 s i)) at 1.
  unfold R.v17785, N.v17785.
  unfold R.v6, N.v6.
  rewrite ?node_5846.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17786 (s : N.State) (i : N.Inputs) :
  R.v17786 (state s) (inputs i) = Zmod.unsigned (N.v17786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17786 s i)) at 1.
  unfold R.v17786, N.v17786.
  rewrite ?node_17784.
  rewrite ?node_17785.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17787 (s : N.State) (i : N.Inputs) :
  R.v17787 (state s) (inputs i) = Zmod.unsigned (N.v17787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17787 s i)) at 1.
  unfold R.v17787, N.v17787.
  rewrite ?node_17783.
  rewrite ?node_17786.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17788 (s : N.State) (i : N.Inputs) :
  R.v17788 (state s) (inputs i) = Zmod.unsigned (N.v17788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17788 s i)) at 1.
  unfold R.v17788, N.v17788.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17789 (s : N.State) (i : N.Inputs) :
  R.v17789 (state s) (inputs i) = Zmod.unsigned (N.v17789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17789 s i)) at 1.
  unfold R.v17789, N.v17789.
  rewrite ?node_5769.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17790 (s : N.State) (i : N.Inputs) :
  R.v17790 (state s) (inputs i) = Zmod.unsigned (N.v17790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17790 s i)) at 1.
  unfold R.v17790, N.v17790.
  unfold R.v16463, N.v16463.
  rewrite !state_r161_nr_5F161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r161_nr_5F161 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17791 (s : N.State) (i : N.Inputs) :
  R.v17791 (state s) (inputs i) = Zmod.unsigned (N.v17791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17791 s i)) at 1.
  unfold R.v17791, N.v17791.
  unfold R.v16463, N.v16463.
  rewrite !state_r160_nr_5F160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r160_nr_5F160 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17792 (s : N.State) (i : N.Inputs) :
  R.v17792 (state s) (inputs i) = Zmod.unsigned (N.v17792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17792 s i)) at 1.
  unfold R.v17792, N.v17792.
  unfold R.v6, N.v6.
  rewrite !state_r159_nr_5F159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r159_nr_5F159 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17793 (s : N.State) (i : N.Inputs) :
  R.v17793 (state s) (inputs i) = Zmod.unsigned (N.v17793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17793 s i)) at 1.
  unfold R.v17793, N.v17793.
  unfold R.v6, N.v6.
  rewrite !state_r158_nr_5F158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r158_nr_5F158 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17794 (s : N.State) (i : N.Inputs) :
  R.v17794 (state s) (inputs i) = Zmod.unsigned (N.v17794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17794 s i)) at 1.
  unfold R.v17794, N.v17794.
  rewrite ?node_17792.
  rewrite ?node_17793.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17795 (s : N.State) (i : N.Inputs) :
  R.v17795 (state s) (inputs i) = Zmod.unsigned (N.v17795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17795 s i)) at 1.
  unfold R.v17795, N.v17795.
  unfold R.v16484, N.v16484.
  rewrite ?node_17794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17796 (s : N.State) (i : N.Inputs) :
  R.v17796 (state s) (inputs i) = Zmod.unsigned (N.v17796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17796 s i)) at 1.
  unfold R.v17796, N.v17796.
  rewrite ?node_17789.
  rewrite ?node_17790.
  rewrite ?node_17791.
  rewrite ?node_17795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17797 (s : N.State) (i : N.Inputs) :
  R.v17797 (state s) (inputs i) = Zmod.unsigned (N.v17797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17797 s i)) at 1.
  unfold R.v17797, N.v17797.
  unfold R.v6, N.v6.
  rewrite ?node_17796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17798 (s : N.State) (i : N.Inputs) :
  R.v17798 (state s) (inputs i) = Zmod.unsigned (N.v17798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17798 s i)) at 1.
  unfold R.v17798, N.v17798.
  rewrite ?node_5770.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17799 (s : N.State) (i : N.Inputs) :
  R.v17799 (state s) (inputs i) = Zmod.unsigned (N.v17799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17799 s i)) at 1.
  unfold R.v17799, N.v17799.
  unfold R.v6, N.v6.
  rewrite ?node_5828.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17800 (s : N.State) (i : N.Inputs) :
  R.v17800 (state s) (inputs i) = Zmod.unsigned (N.v17800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17800 s i)) at 1.
  unfold R.v17800, N.v17800.
  unfold R.v6, N.v6.
  rewrite ?node_5849.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17801 (s : N.State) (i : N.Inputs) :
  R.v17801 (state s) (inputs i) = Zmod.unsigned (N.v17801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17801 s i)) at 1.
  unfold R.v17801, N.v17801.
  rewrite ?node_17798.
  rewrite ?node_17799.
  rewrite ?node_17800.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17802 (s : N.State) (i : N.Inputs) :
  R.v17802 (state s) (inputs i) = Zmod.unsigned (N.v17802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17802 s i)) at 1.
  unfold R.v17802, N.v17802.
  rewrite ?node_17797.
  rewrite ?node_17801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17803 (s : N.State) (i : N.Inputs) :
  R.v17803 (state s) (inputs i) = Zmod.unsigned (N.v17803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17803 s i)) at 1.
  unfold R.v17803, N.v17803.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17804 (s : N.State) (i : N.Inputs) :
  R.v17804 (state s) (inputs i) = Zmod.unsigned (N.v17804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17804 s i)) at 1.
  unfold R.v17804, N.v17804.
  unfold R.v16463, N.v16463.
  rewrite !state_r160_nr_5F160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r160_nr_5F160 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17805 (s : N.State) (i : N.Inputs) :
  R.v17805 (state s) (inputs i) = Zmod.unsigned (N.v17805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17805 s i)) at 1.
  unfold R.v17805, N.v17805.
  unfold R.v6, N.v6.
  rewrite !state_r159_nr_5F159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r159_nr_5F159 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17806 (s : N.State) (i : N.Inputs) :
  R.v17806 (state s) (inputs i) = Zmod.unsigned (N.v17806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17806 s i)) at 1.
  unfold R.v17806, N.v17806.
  unfold R.v6, N.v6.
  rewrite !state_r158_nr_5F158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r158_nr_5F158 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17807 (s : N.State) (i : N.Inputs) :
  R.v17807 (state s) (inputs i) = Zmod.unsigned (N.v17807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17807 s i)) at 1.
  unfold R.v17807, N.v17807.
  rewrite ?node_17805.
  rewrite ?node_17806.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17808 (s : N.State) (i : N.Inputs) :
  R.v17808 (state s) (inputs i) = Zmod.unsigned (N.v17808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17808 s i)) at 1.
  unfold R.v17808, N.v17808.
  unfold R.v16484, N.v16484.
  rewrite ?node_17807.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17809 (s : N.State) (i : N.Inputs) :
  R.v17809 (state s) (inputs i) = Zmod.unsigned (N.v17809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17809 s i)) at 1.
  unfold R.v17809, N.v17809.
  rewrite ?node_17804.
  rewrite ?node_17808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17810 (s : N.State) (i : N.Inputs) :
  R.v17810 (state s) (inputs i) = Zmod.unsigned (N.v17810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17810 s i)) at 1.
  unfold R.v17810, N.v17810.
  unfold R.v6, N.v6.
  rewrite ?node_17809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17811 (s : N.State) (i : N.Inputs) :
  R.v17811 (state s) (inputs i) = Zmod.unsigned (N.v17811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17811 s i)) at 1.
  unfold R.v17811, N.v17811.
  rewrite ?node_5765.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17812 (s : N.State) (i : N.Inputs) :
  R.v17812 (state s) (inputs i) = Zmod.unsigned (N.v17812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17812 s i)) at 1.
  unfold R.v17812, N.v17812.
  unfold R.v6, N.v6.
  rewrite ?node_5828.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17813 (s : N.State) (i : N.Inputs) :
  R.v17813 (state s) (inputs i) = Zmod.unsigned (N.v17813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17813 s i)) at 1.
  unfold R.v17813, N.v17813.
  rewrite ?node_17811.
  rewrite ?node_17812.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17814 (s : N.State) (i : N.Inputs) :
  R.v17814 (state s) (inputs i) = Zmod.unsigned (N.v17814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17814 s i)) at 1.
  unfold R.v17814, N.v17814.
  rewrite ?node_17810.
  rewrite ?node_17813.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17815 (s : N.State) (i : N.Inputs) :
  R.v17815 (state s) (inputs i) = Zmod.unsigned (N.v17815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17815 s i)) at 1.
  unfold R.v17815, N.v17815.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17816 (s : N.State) (i : N.Inputs) :
  R.v17816 (state s) (inputs i) = Zmod.unsigned (N.v17816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17816 s i)) at 1.
  unfold R.v17816, N.v17816.
  rewrite ?node_5769.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17817 (s : N.State) (i : N.Inputs) :
  R.v17817 (state s) (inputs i) = Zmod.unsigned (N.v17817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17817 s i)) at 1.
  unfold R.v17817, N.v17817.
  unfold R.v6, N.v6.
  rewrite !state_r161_nr_5F161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r161_nr_5F161 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17818 (s : N.State) (i : N.Inputs) :
  R.v17818 (state s) (inputs i) = Zmod.unsigned (N.v17818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17818 s i)) at 1.
  unfold R.v17818, N.v17818.
  unfold R.v6, N.v6.
  rewrite ?node_5765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17819 (s : N.State) (i : N.Inputs) :
  R.v17819 (state s) (inputs i) = Zmod.unsigned (N.v17819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17819 s i)) at 1.
  unfold R.v17819, N.v17819.
  rewrite ?node_17817.
  rewrite ?node_17818.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17820 (s : N.State) (i : N.Inputs) :
  R.v17820 (state s) (inputs i) = Zmod.unsigned (N.v17820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17820 s i)) at 1.
  unfold R.v17820, N.v17820.
  unfold R.v16484, N.v16484.
  rewrite ?node_17819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17821 (s : N.State) (i : N.Inputs) :
  R.v17821 (state s) (inputs i) = Zmod.unsigned (N.v17821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17821 s i)) at 1.
  unfold R.v17821, N.v17821.
  rewrite ?node_17816.
  rewrite ?node_17820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17822 (s : N.State) (i : N.Inputs) :
  R.v17822 (state s) (inputs i) = Zmod.unsigned (N.v17822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17822 s i)) at 1.
  unfold R.v17822, N.v17822.
  unfold R.v6, N.v6.
  rewrite ?node_17821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17823 (s : N.State) (i : N.Inputs) :
  R.v17823 (state s) (inputs i) = Zmod.unsigned (N.v17823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17823 s i)) at 1.
  unfold R.v17823, N.v17823.
  rewrite ?node_5770.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17824 (s : N.State) (i : N.Inputs) :
  R.v17824 (state s) (inputs i) = Zmod.unsigned (N.v17824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17824 s i)) at 1.
  unfold R.v17824, N.v17824.
  unfold R.v6, N.v6.
  rewrite ?node_5849.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17825 (s : N.State) (i : N.Inputs) :
  R.v17825 (state s) (inputs i) = Zmod.unsigned (N.v17825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17825 s i)) at 1.
  unfold R.v17825, N.v17825.
  rewrite ?node_17823.
  rewrite ?node_17824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17826 (s : N.State) (i : N.Inputs) :
  R.v17826 (state s) (inputs i) = Zmod.unsigned (N.v17826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17826 s i)) at 1.
  unfold R.v17826, N.v17826.
  rewrite ?node_17822.
  rewrite ?node_17825.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17827 (s : N.State) (i : N.Inputs) :
  R.v17827 (state s) (inputs i) = Zmod.unsigned (N.v17827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17827 s i)) at 1.
  unfold R.v17827, N.v17827.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17828 (s : N.State) (i : N.Inputs) :
  R.v17828 (state s) (inputs i) = Zmod.unsigned (N.v17828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17828 s i)) at 1.
  unfold R.v17828, N.v17828.
  rewrite ?node_5777.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17829 (s : N.State) (i : N.Inputs) :
  R.v17829 (state s) (inputs i) = Zmod.unsigned (N.v17829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17829 s i)) at 1.
  unfold R.v17829, N.v17829.
  unfold R.v16463, N.v16463.
  rewrite !state_r165_nr_5F165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r165_nr_5F165 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17830 (s : N.State) (i : N.Inputs) :
  R.v17830 (state s) (inputs i) = Zmod.unsigned (N.v17830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17830 s i)) at 1.
  unfold R.v17830, N.v17830.
  unfold R.v16463, N.v16463.
  rewrite !state_r164_nr_5F164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r164_nr_5F164 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17831 (s : N.State) (i : N.Inputs) :
  R.v17831 (state s) (inputs i) = Zmod.unsigned (N.v17831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17831 s i)) at 1.
  unfold R.v17831, N.v17831.
  unfold R.v6, N.v6.
  rewrite !state_r163_nr_5F163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r163_nr_5F163 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17832 (s : N.State) (i : N.Inputs) :
  R.v17832 (state s) (inputs i) = Zmod.unsigned (N.v17832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17832 s i)) at 1.
  unfold R.v17832, N.v17832.
  unfold R.v6, N.v6.
  rewrite !state_r162_nr_5F162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r162_nr_5F162 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17833 (s : N.State) (i : N.Inputs) :
  R.v17833 (state s) (inputs i) = Zmod.unsigned (N.v17833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17833 s i)) at 1.
  unfold R.v17833, N.v17833.
  rewrite ?node_17831.
  rewrite ?node_17832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17834 (s : N.State) (i : N.Inputs) :
  R.v17834 (state s) (inputs i) = Zmod.unsigned (N.v17834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17834 s i)) at 1.
  unfold R.v17834, N.v17834.
  unfold R.v16484, N.v16484.
  rewrite ?node_17833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17835 (s : N.State) (i : N.Inputs) :
  R.v17835 (state s) (inputs i) = Zmod.unsigned (N.v17835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17835 s i)) at 1.
  unfold R.v17835, N.v17835.
  rewrite ?node_17828.
  rewrite ?node_17829.
  rewrite ?node_17830.
  rewrite ?node_17834.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17836 (s : N.State) (i : N.Inputs) :
  R.v17836 (state s) (inputs i) = Zmod.unsigned (N.v17836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17836 s i)) at 1.
  unfold R.v17836, N.v17836.
  unfold R.v6, N.v6.
  rewrite ?node_17835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17837 (s : N.State) (i : N.Inputs) :
  R.v17837 (state s) (inputs i) = Zmod.unsigned (N.v17837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17837 s i)) at 1.
  unfold R.v17837, N.v17837.
  rewrite ?node_5778.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17838 (s : N.State) (i : N.Inputs) :
  R.v17838 (state s) (inputs i) = Zmod.unsigned (N.v17838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17838 s i)) at 1.
  unfold R.v17838, N.v17838.
  unfold R.v6, N.v6.
  rewrite ?node_5836.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17839 (s : N.State) (i : N.Inputs) :
  R.v17839 (state s) (inputs i) = Zmod.unsigned (N.v17839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17839 s i)) at 1.
  unfold R.v17839, N.v17839.
  unfold R.v6, N.v6.
  rewrite ?node_5853.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17840 (s : N.State) (i : N.Inputs) :
  R.v17840 (state s) (inputs i) = Zmod.unsigned (N.v17840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17840 s i)) at 1.
  unfold R.v17840, N.v17840.
  rewrite ?node_17837.
  rewrite ?node_17838.
  rewrite ?node_17839.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17841 (s : N.State) (i : N.Inputs) :
  R.v17841 (state s) (inputs i) = Zmod.unsigned (N.v17841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17841 s i)) at 1.
  unfold R.v17841, N.v17841.
  rewrite ?node_17836.
  rewrite ?node_17840.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17842 (s : N.State) (i : N.Inputs) :
  R.v17842 (state s) (inputs i) = Zmod.unsigned (N.v17842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17842 s i)) at 1.
  unfold R.v17842, N.v17842.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17843 (s : N.State) (i : N.Inputs) :
  R.v17843 (state s) (inputs i) = Zmod.unsigned (N.v17843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17843 s i)) at 1.
  unfold R.v17843, N.v17843.
  unfold R.v16463, N.v16463.
  rewrite !state_r164_nr_5F164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r164_nr_5F164 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17844 (s : N.State) (i : N.Inputs) :
  R.v17844 (state s) (inputs i) = Zmod.unsigned (N.v17844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17844 s i)) at 1.
  unfold R.v17844, N.v17844.
  unfold R.v6, N.v6.
  rewrite !state_r163_nr_5F163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r163_nr_5F163 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17845 (s : N.State) (i : N.Inputs) :
  R.v17845 (state s) (inputs i) = Zmod.unsigned (N.v17845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17845 s i)) at 1.
  unfold R.v17845, N.v17845.
  unfold R.v6, N.v6.
  rewrite !state_r162_nr_5F162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r162_nr_5F162 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17846 (s : N.State) (i : N.Inputs) :
  R.v17846 (state s) (inputs i) = Zmod.unsigned (N.v17846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17846 s i)) at 1.
  unfold R.v17846, N.v17846.
  rewrite ?node_17844.
  rewrite ?node_17845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17847 (s : N.State) (i : N.Inputs) :
  R.v17847 (state s) (inputs i) = Zmod.unsigned (N.v17847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17847 s i)) at 1.
  unfold R.v17847, N.v17847.
  unfold R.v16484, N.v16484.
  rewrite ?node_17846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17848 (s : N.State) (i : N.Inputs) :
  R.v17848 (state s) (inputs i) = Zmod.unsigned (N.v17848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17848 s i)) at 1.
  unfold R.v17848, N.v17848.
  rewrite ?node_17843.
  rewrite ?node_17847.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17849 (s : N.State) (i : N.Inputs) :
  R.v17849 (state s) (inputs i) = Zmod.unsigned (N.v17849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17849 s i)) at 1.
  unfold R.v17849, N.v17849.
  unfold R.v6, N.v6.
  rewrite ?node_17848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17850 (s : N.State) (i : N.Inputs) :
  R.v17850 (state s) (inputs i) = Zmod.unsigned (N.v17850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17850 s i)) at 1.
  unfold R.v17850, N.v17850.
  rewrite ?node_5773.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17851 (s : N.State) (i : N.Inputs) :
  R.v17851 (state s) (inputs i) = Zmod.unsigned (N.v17851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17851 s i)) at 1.
  unfold R.v17851, N.v17851.
  unfold R.v6, N.v6.
  rewrite ?node_5836.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17852 (s : N.State) (i : N.Inputs) :
  R.v17852 (state s) (inputs i) = Zmod.unsigned (N.v17852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17852 s i)) at 1.
  unfold R.v17852, N.v17852.
  rewrite ?node_17850.
  rewrite ?node_17851.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17853 (s : N.State) (i : N.Inputs) :
  R.v17853 (state s) (inputs i) = Zmod.unsigned (N.v17853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17853 s i)) at 1.
  unfold R.v17853, N.v17853.
  rewrite ?node_17849.
  rewrite ?node_17852.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17854 (s : N.State) (i : N.Inputs) :
  R.v17854 (state s) (inputs i) = Zmod.unsigned (N.v17854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17854 s i)) at 1.
  unfold R.v17854, N.v17854.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17855 (s : N.State) (i : N.Inputs) :
  R.v17855 (state s) (inputs i) = Zmod.unsigned (N.v17855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17855 s i)) at 1.
  unfold R.v17855, N.v17855.
  rewrite ?node_5777.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17856 (s : N.State) (i : N.Inputs) :
  R.v17856 (state s) (inputs i) = Zmod.unsigned (N.v17856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17856 s i)) at 1.
  unfold R.v17856, N.v17856.
  unfold R.v6, N.v6.
  rewrite !state_r165_nr_5F165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r165_nr_5F165 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17857 (s : N.State) (i : N.Inputs) :
  R.v17857 (state s) (inputs i) = Zmod.unsigned (N.v17857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17857 s i)) at 1.
  unfold R.v17857, N.v17857.
  unfold R.v6, N.v6.
  rewrite ?node_5773.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17858 (s : N.State) (i : N.Inputs) :
  R.v17858 (state s) (inputs i) = Zmod.unsigned (N.v17858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17858 s i)) at 1.
  unfold R.v17858, N.v17858.
  rewrite ?node_17856.
  rewrite ?node_17857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17859 (s : N.State) (i : N.Inputs) :
  R.v17859 (state s) (inputs i) = Zmod.unsigned (N.v17859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17859 s i)) at 1.
  unfold R.v17859, N.v17859.
  unfold R.v16484, N.v16484.
  rewrite ?node_17858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17860 (s : N.State) (i : N.Inputs) :
  R.v17860 (state s) (inputs i) = Zmod.unsigned (N.v17860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17860 s i)) at 1.
  unfold R.v17860, N.v17860.
  rewrite ?node_17855.
  rewrite ?node_17859.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17861 (s : N.State) (i : N.Inputs) :
  R.v17861 (state s) (inputs i) = Zmod.unsigned (N.v17861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17861 s i)) at 1.
  unfold R.v17861, N.v17861.
  unfold R.v6, N.v6.
  rewrite ?node_17860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17862 (s : N.State) (i : N.Inputs) :
  R.v17862 (state s) (inputs i) = Zmod.unsigned (N.v17862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17862 s i)) at 1.
  unfold R.v17862, N.v17862.
  rewrite ?node_5778.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17863 (s : N.State) (i : N.Inputs) :
  R.v17863 (state s) (inputs i) = Zmod.unsigned (N.v17863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17863 s i)) at 1.
  unfold R.v17863, N.v17863.
  unfold R.v6, N.v6.
  rewrite ?node_5853.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17864 (s : N.State) (i : N.Inputs) :
  R.v17864 (state s) (inputs i) = Zmod.unsigned (N.v17864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17864 s i)) at 1.
  unfold R.v17864, N.v17864.
  rewrite ?node_17862.
  rewrite ?node_17863.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17865 (s : N.State) (i : N.Inputs) :
  R.v17865 (state s) (inputs i) = Zmod.unsigned (N.v17865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17865 s i)) at 1.
  unfold R.v17865, N.v17865.
  rewrite ?node_17861.
  rewrite ?node_17864.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17866 (s : N.State) (i : N.Inputs) :
  R.v17866 (state s) (inputs i) = Zmod.unsigned (N.v17866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17866 s i)) at 1.
  unfold R.v17866, N.v17866.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17867 (s : N.State) (i : N.Inputs) :
  R.v17867 (state s) (inputs i) = Zmod.unsigned (N.v17867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17867 s i)) at 1.
  unfold R.v17867, N.v17867.
  rewrite ?node_5821.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17868 (s : N.State) (i : N.Inputs) :
  R.v17868 (state s) (inputs i) = Zmod.unsigned (N.v17868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17868 s i)) at 1.
  unfold R.v17868, N.v17868.
  unfold R.v16463, N.v16463.
  rewrite !state_r170_nr_5F170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r170_nr_5F170 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17869 (s : N.State) (i : N.Inputs) :
  R.v17869 (state s) (inputs i) = Zmod.unsigned (N.v17869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17869 s i)) at 1.
  unfold R.v17869, N.v17869.
  unfold R.v16463, N.v16463.
  rewrite !state_r169_nr_5F169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r169_nr_5F169 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17870 (s : N.State) (i : N.Inputs) :
  R.v17870 (state s) (inputs i) = Zmod.unsigned (N.v17870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17870 s i)) at 1.
  unfold R.v17870, N.v17870.
  unfold R.v6, N.v6.
  rewrite !state_r168_nr_5F168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r168_nr_5F168 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17871 (s : N.State) (i : N.Inputs) :
  R.v17871 (state s) (inputs i) = Zmod.unsigned (N.v17871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17871 s i)) at 1.
  unfold R.v17871, N.v17871.
  unfold R.v6, N.v6.
  rewrite !state_r167_nr_5F167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r167_nr_5F167 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17872 (s : N.State) (i : N.Inputs) :
  R.v17872 (state s) (inputs i) = Zmod.unsigned (N.v17872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17872 s i)) at 1.
  unfold R.v17872, N.v17872.
  rewrite ?node_17870.
  rewrite ?node_17871.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17873 (s : N.State) (i : N.Inputs) :
  R.v17873 (state s) (inputs i) = Zmod.unsigned (N.v17873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17873 s i)) at 1.
  unfold R.v17873, N.v17873.
  unfold R.v16484, N.v16484.
  rewrite ?node_17872.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17874 (s : N.State) (i : N.Inputs) :
  R.v17874 (state s) (inputs i) = Zmod.unsigned (N.v17874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17874 s i)) at 1.
  unfold R.v17874, N.v17874.
  rewrite ?node_17867.
  rewrite ?node_17868.
  rewrite ?node_17869.
  rewrite ?node_17873.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17875 (s : N.State) (i : N.Inputs) :
  R.v17875 (state s) (inputs i) = Zmod.unsigned (N.v17875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17875 s i)) at 1.
  unfold R.v17875, N.v17875.
  unfold R.v6, N.v6.
  rewrite ?node_17874.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17876 (s : N.State) (i : N.Inputs) :
  R.v17876 (state s) (inputs i) = Zmod.unsigned (N.v17876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17876 s i)) at 1.
  unfold R.v17876, N.v17876.
  rewrite ?node_5822.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17877 (s : N.State) (i : N.Inputs) :
  R.v17877 (state s) (inputs i) = Zmod.unsigned (N.v17877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17877 s i)) at 1.
  unfold R.v17877, N.v17877.
  unfold R.v6, N.v6.
  rewrite ?node_5882.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17878 (s : N.State) (i : N.Inputs) :
  R.v17878 (state s) (inputs i) = Zmod.unsigned (N.v17878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17878 s i)) at 1.
  unfold R.v17878, N.v17878.
  unfold R.v6, N.v6.
  rewrite ?node_5908.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17879 (s : N.State) (i : N.Inputs) :
  R.v17879 (state s) (inputs i) = Zmod.unsigned (N.v17879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17879 s i)) at 1.
  unfold R.v17879, N.v17879.
  rewrite ?node_17876.
  rewrite ?node_17877.
  rewrite ?node_17878.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17880 (s : N.State) (i : N.Inputs) :
  R.v17880 (state s) (inputs i) = Zmod.unsigned (N.v17880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17880 s i)) at 1.
  unfold R.v17880, N.v17880.
  rewrite ?node_17875.
  rewrite ?node_17879.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17881 (s : N.State) (i : N.Inputs) :
  R.v17881 (state s) (inputs i) = Zmod.unsigned (N.v17881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17881 s i)) at 1.
  unfold R.v17881, N.v17881.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17882 (s : N.State) (i : N.Inputs) :
  R.v17882 (state s) (inputs i) = Zmod.unsigned (N.v17882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17882 s i)) at 1.
  unfold R.v17882, N.v17882.
  unfold R.v16463, N.v16463.
  rewrite !state_r169_nr_5F169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r169_nr_5F169 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17883 (s : N.State) (i : N.Inputs) :
  R.v17883 (state s) (inputs i) = Zmod.unsigned (N.v17883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17883 s i)) at 1.
  unfold R.v17883, N.v17883.
  unfold R.v6, N.v6.
  rewrite !state_r168_nr_5F168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r168_nr_5F168 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17884 (s : N.State) (i : N.Inputs) :
  R.v17884 (state s) (inputs i) = Zmod.unsigned (N.v17884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17884 s i)) at 1.
  unfold R.v17884, N.v17884.
  unfold R.v6, N.v6.
  rewrite !state_r167_nr_5F167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r167_nr_5F167 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17885 (s : N.State) (i : N.Inputs) :
  R.v17885 (state s) (inputs i) = Zmod.unsigned (N.v17885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17885 s i)) at 1.
  unfold R.v17885, N.v17885.
  rewrite ?node_17883.
  rewrite ?node_17884.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17886 (s : N.State) (i : N.Inputs) :
  R.v17886 (state s) (inputs i) = Zmod.unsigned (N.v17886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17886 s i)) at 1.
  unfold R.v17886, N.v17886.
  unfold R.v16484, N.v16484.
  rewrite ?node_17885.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17887 (s : N.State) (i : N.Inputs) :
  R.v17887 (state s) (inputs i) = Zmod.unsigned (N.v17887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17887 s i)) at 1.
  unfold R.v17887, N.v17887.
  rewrite ?node_17882.
  rewrite ?node_17886.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17888 (s : N.State) (i : N.Inputs) :
  R.v17888 (state s) (inputs i) = Zmod.unsigned (N.v17888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17888 s i)) at 1.
  unfold R.v17888, N.v17888.
  unfold R.v6, N.v6.
  rewrite ?node_17887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17889 (s : N.State) (i : N.Inputs) :
  R.v17889 (state s) (inputs i) = Zmod.unsigned (N.v17889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17889 s i)) at 1.
  unfold R.v17889, N.v17889.
  rewrite ?node_5817.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17890 (s : N.State) (i : N.Inputs) :
  R.v17890 (state s) (inputs i) = Zmod.unsigned (N.v17890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17890 s i)) at 1.
  unfold R.v17890, N.v17890.
  unfold R.v6, N.v6.
  rewrite ?node_5882.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17891 (s : N.State) (i : N.Inputs) :
  R.v17891 (state s) (inputs i) = Zmod.unsigned (N.v17891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17891 s i)) at 1.
  unfold R.v17891, N.v17891.
  rewrite ?node_17889.
  rewrite ?node_17890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17892 (s : N.State) (i : N.Inputs) :
  R.v17892 (state s) (inputs i) = Zmod.unsigned (N.v17892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17892 s i)) at 1.
  unfold R.v17892, N.v17892.
  rewrite ?node_17888.
  rewrite ?node_17891.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17893 (s : N.State) (i : N.Inputs) :
  R.v17893 (state s) (inputs i) = Zmod.unsigned (N.v17893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17893 s i)) at 1.
  unfold R.v17893, N.v17893.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17894 (s : N.State) (i : N.Inputs) :
  R.v17894 (state s) (inputs i) = Zmod.unsigned (N.v17894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17894 s i)) at 1.
  unfold R.v17894, N.v17894.
  rewrite ?node_5821.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17895 (s : N.State) (i : N.Inputs) :
  R.v17895 (state s) (inputs i) = Zmod.unsigned (N.v17895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17895 s i)) at 1.
  unfold R.v17895, N.v17895.
  unfold R.v6, N.v6.
  rewrite !state_r170_nr_5F170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r170_nr_5F170 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17896 (s : N.State) (i : N.Inputs) :
  R.v17896 (state s) (inputs i) = Zmod.unsigned (N.v17896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17896 s i)) at 1.
  unfold R.v17896, N.v17896.
  unfold R.v6, N.v6.
  rewrite ?node_5817.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17897 (s : N.State) (i : N.Inputs) :
  R.v17897 (state s) (inputs i) = Zmod.unsigned (N.v17897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17897 s i)) at 1.
  unfold R.v17897, N.v17897.
  rewrite ?node_17895.
  rewrite ?node_17896.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17898 (s : N.State) (i : N.Inputs) :
  R.v17898 (state s) (inputs i) = Zmod.unsigned (N.v17898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17898 s i)) at 1.
  unfold R.v17898, N.v17898.
  unfold R.v16484, N.v16484.
  rewrite ?node_17897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17899 (s : N.State) (i : N.Inputs) :
  R.v17899 (state s) (inputs i) = Zmod.unsigned (N.v17899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17899 s i)) at 1.
  unfold R.v17899, N.v17899.
  rewrite ?node_17894.
  rewrite ?node_17898.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17900 (s : N.State) (i : N.Inputs) :
  R.v17900 (state s) (inputs i) = Zmod.unsigned (N.v17900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17900 s i)) at 1.
  unfold R.v17900, N.v17900.
  unfold R.v6, N.v6.
  rewrite ?node_17899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17901 (s : N.State) (i : N.Inputs) :
  R.v17901 (state s) (inputs i) = Zmod.unsigned (N.v17901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17901 s i)) at 1.
  unfold R.v17901, N.v17901.
  rewrite ?node_5822.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17902 (s : N.State) (i : N.Inputs) :
  R.v17902 (state s) (inputs i) = Zmod.unsigned (N.v17902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17902 s i)) at 1.
  unfold R.v17902, N.v17902.
  unfold R.v6, N.v6.
  rewrite ?node_5908.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17903 (s : N.State) (i : N.Inputs) :
  R.v17903 (state s) (inputs i) = Zmod.unsigned (N.v17903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17903 s i)) at 1.
  unfold R.v17903, N.v17903.
  rewrite ?node_17901.
  rewrite ?node_17902.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17904 (s : N.State) (i : N.Inputs) :
  R.v17904 (state s) (inputs i) = Zmod.unsigned (N.v17904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17904 s i)) at 1.
  unfold R.v17904, N.v17904.
  rewrite ?node_17900.
  rewrite ?node_17903.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17905 (s : N.State) (i : N.Inputs) :
  R.v17905 (state s) (inputs i) = Zmod.unsigned (N.v17905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17905 s i)) at 1.
  unfold R.v17905, N.v17905.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17906 (s : N.State) (i : N.Inputs) :
  R.v17906 (state s) (inputs i) = Zmod.unsigned (N.v17906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17906 s i)) at 1.
  unfold R.v17906, N.v17906.
  rewrite ?node_5828.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17907 (s : N.State) (i : N.Inputs) :
  R.v17907 (state s) (inputs i) = Zmod.unsigned (N.v17907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17907 s i)) at 1.
  unfold R.v17907, N.v17907.
  unfold R.v16463, N.v16463.
  rewrite !state_r174_nr_5F174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r174_nr_5F174 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17908 (s : N.State) (i : N.Inputs) :
  R.v17908 (state s) (inputs i) = Zmod.unsigned (N.v17908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17908 s i)) at 1.
  unfold R.v17908, N.v17908.
  unfold R.v16463, N.v16463.
  rewrite !state_r173_nr_5F173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r173_nr_5F173 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17909 (s : N.State) (i : N.Inputs) :
  R.v17909 (state s) (inputs i) = Zmod.unsigned (N.v17909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17909 s i)) at 1.
  unfold R.v17909, N.v17909.
  unfold R.v6, N.v6.
  rewrite !state_r172_nr_5F172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r172_nr_5F172 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17910 (s : N.State) (i : N.Inputs) :
  R.v17910 (state s) (inputs i) = Zmod.unsigned (N.v17910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17910 s i)) at 1.
  unfold R.v17910, N.v17910.
  unfold R.v6, N.v6.
  rewrite !state_r171_nr_5F171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r171_nr_5F171 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17911 (s : N.State) (i : N.Inputs) :
  R.v17911 (state s) (inputs i) = Zmod.unsigned (N.v17911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17911 s i)) at 1.
  unfold R.v17911, N.v17911.
  rewrite ?node_17909.
  rewrite ?node_17910.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17912 (s : N.State) (i : N.Inputs) :
  R.v17912 (state s) (inputs i) = Zmod.unsigned (N.v17912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17912 s i)) at 1.
  unfold R.v17912, N.v17912.
  unfold R.v16484, N.v16484.
  rewrite ?node_17911.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17913 (s : N.State) (i : N.Inputs) :
  R.v17913 (state s) (inputs i) = Zmod.unsigned (N.v17913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17913 s i)) at 1.
  unfold R.v17913, N.v17913.
  rewrite ?node_17906.
  rewrite ?node_17907.
  rewrite ?node_17908.
  rewrite ?node_17912.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17914 (s : N.State) (i : N.Inputs) :
  R.v17914 (state s) (inputs i) = Zmod.unsigned (N.v17914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17914 s i)) at 1.
  unfold R.v17914, N.v17914.
  unfold R.v6, N.v6.
  rewrite ?node_17913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17915 (s : N.State) (i : N.Inputs) :
  R.v17915 (state s) (inputs i) = Zmod.unsigned (N.v17915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17915 s i)) at 1.
  unfold R.v17915, N.v17915.
  rewrite ?node_5829.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17916 (s : N.State) (i : N.Inputs) :
  R.v17916 (state s) (inputs i) = Zmod.unsigned (N.v17916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17916 s i)) at 1.
  unfold R.v17916, N.v17916.
  unfold R.v6, N.v6.
  rewrite ?node_5889.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17917 (s : N.State) (i : N.Inputs) :
  R.v17917 (state s) (inputs i) = Zmod.unsigned (N.v17917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17917 s i)) at 1.
  unfold R.v17917, N.v17917.
  unfold R.v6, N.v6.
  rewrite ?node_5911.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17918 (s : N.State) (i : N.Inputs) :
  R.v17918 (state s) (inputs i) = Zmod.unsigned (N.v17918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17918 s i)) at 1.
  unfold R.v17918, N.v17918.
  rewrite ?node_17915.
  rewrite ?node_17916.
  rewrite ?node_17917.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17919 (s : N.State) (i : N.Inputs) :
  R.v17919 (state s) (inputs i) = Zmod.unsigned (N.v17919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17919 s i)) at 1.
  unfold R.v17919, N.v17919.
  rewrite ?node_17914.
  rewrite ?node_17918.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17920 (s : N.State) (i : N.Inputs) :
  R.v17920 (state s) (inputs i) = Zmod.unsigned (N.v17920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17920 s i)) at 1.
  unfold R.v17920, N.v17920.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17921 (s : N.State) (i : N.Inputs) :
  R.v17921 (state s) (inputs i) = Zmod.unsigned (N.v17921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17921 s i)) at 1.
  unfold R.v17921, N.v17921.
  unfold R.v16463, N.v16463.
  rewrite !state_r173_nr_5F173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r173_nr_5F173 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17922 (s : N.State) (i : N.Inputs) :
  R.v17922 (state s) (inputs i) = Zmod.unsigned (N.v17922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17922 s i)) at 1.
  unfold R.v17922, N.v17922.
  unfold R.v6, N.v6.
  rewrite !state_r172_nr_5F172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r172_nr_5F172 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17923 (s : N.State) (i : N.Inputs) :
  R.v17923 (state s) (inputs i) = Zmod.unsigned (N.v17923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17923 s i)) at 1.
  unfold R.v17923, N.v17923.
  unfold R.v6, N.v6.
  rewrite !state_r171_nr_5F171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r171_nr_5F171 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17924 (s : N.State) (i : N.Inputs) :
  R.v17924 (state s) (inputs i) = Zmod.unsigned (N.v17924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17924 s i)) at 1.
  unfold R.v17924, N.v17924.
  rewrite ?node_17922.
  rewrite ?node_17923.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17925 (s : N.State) (i : N.Inputs) :
  R.v17925 (state s) (inputs i) = Zmod.unsigned (N.v17925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17925 s i)) at 1.
  unfold R.v17925, N.v17925.
  unfold R.v16484, N.v16484.
  rewrite ?node_17924.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17926 (s : N.State) (i : N.Inputs) :
  R.v17926 (state s) (inputs i) = Zmod.unsigned (N.v17926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17926 s i)) at 1.
  unfold R.v17926, N.v17926.
  rewrite ?node_17921.
  rewrite ?node_17925.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17927 (s : N.State) (i : N.Inputs) :
  R.v17927 (state s) (inputs i) = Zmod.unsigned (N.v17927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17927 s i)) at 1.
  unfold R.v17927, N.v17927.
  unfold R.v6, N.v6.
  rewrite ?node_17926.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17928 (s : N.State) (i : N.Inputs) :
  R.v17928 (state s) (inputs i) = Zmod.unsigned (N.v17928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17928 s i)) at 1.
  unfold R.v17928, N.v17928.
  rewrite ?node_5824.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17929 (s : N.State) (i : N.Inputs) :
  R.v17929 (state s) (inputs i) = Zmod.unsigned (N.v17929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17929 s i)) at 1.
  unfold R.v17929, N.v17929.
  unfold R.v6, N.v6.
  rewrite ?node_5889.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17930 (s : N.State) (i : N.Inputs) :
  R.v17930 (state s) (inputs i) = Zmod.unsigned (N.v17930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17930 s i)) at 1.
  unfold R.v17930, N.v17930.
  rewrite ?node_17928.
  rewrite ?node_17929.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17931 (s : N.State) (i : N.Inputs) :
  R.v17931 (state s) (inputs i) = Zmod.unsigned (N.v17931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17931 s i)) at 1.
  unfold R.v17931, N.v17931.
  rewrite ?node_17927.
  rewrite ?node_17930.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17932 (s : N.State) (i : N.Inputs) :
  R.v17932 (state s) (inputs i) = Zmod.unsigned (N.v17932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17932 s i)) at 1.
  unfold R.v17932, N.v17932.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17933 (s : N.State) (i : N.Inputs) :
  R.v17933 (state s) (inputs i) = Zmod.unsigned (N.v17933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17933 s i)) at 1.
  unfold R.v17933, N.v17933.
  rewrite ?node_5828.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17934 (s : N.State) (i : N.Inputs) :
  R.v17934 (state s) (inputs i) = Zmod.unsigned (N.v17934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17934 s i)) at 1.
  unfold R.v17934, N.v17934.
  unfold R.v6, N.v6.
  rewrite !state_r174_nr_5F174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r174_nr_5F174 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17935 (s : N.State) (i : N.Inputs) :
  R.v17935 (state s) (inputs i) = Zmod.unsigned (N.v17935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17935 s i)) at 1.
  unfold R.v17935, N.v17935.
  unfold R.v6, N.v6.
  rewrite ?node_5824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17936 (s : N.State) (i : N.Inputs) :
  R.v17936 (state s) (inputs i) = Zmod.unsigned (N.v17936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17936 s i)) at 1.
  unfold R.v17936, N.v17936.
  rewrite ?node_17934.
  rewrite ?node_17935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17937 (s : N.State) (i : N.Inputs) :
  R.v17937 (state s) (inputs i) = Zmod.unsigned (N.v17937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17937 s i)) at 1.
  unfold R.v17937, N.v17937.
  unfold R.v16484, N.v16484.
  rewrite ?node_17936.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17938 (s : N.State) (i : N.Inputs) :
  R.v17938 (state s) (inputs i) = Zmod.unsigned (N.v17938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17938 s i)) at 1.
  unfold R.v17938, N.v17938.
  rewrite ?node_17933.
  rewrite ?node_17937.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17939 (s : N.State) (i : N.Inputs) :
  R.v17939 (state s) (inputs i) = Zmod.unsigned (N.v17939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17939 s i)) at 1.
  unfold R.v17939, N.v17939.
  unfold R.v6, N.v6.
  rewrite ?node_17938.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17940 (s : N.State) (i : N.Inputs) :
  R.v17940 (state s) (inputs i) = Zmod.unsigned (N.v17940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17940 s i)) at 1.
  unfold R.v17940, N.v17940.
  rewrite ?node_5829.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17941 (s : N.State) (i : N.Inputs) :
  R.v17941 (state s) (inputs i) = Zmod.unsigned (N.v17941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17941 s i)) at 1.
  unfold R.v17941, N.v17941.
  unfold R.v6, N.v6.
  rewrite ?node_5911.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17942 (s : N.State) (i : N.Inputs) :
  R.v17942 (state s) (inputs i) = Zmod.unsigned (N.v17942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17942 s i)) at 1.
  unfold R.v17942, N.v17942.
  rewrite ?node_17940.
  rewrite ?node_17941.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17943 (s : N.State) (i : N.Inputs) :
  R.v17943 (state s) (inputs i) = Zmod.unsigned (N.v17943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17943 s i)) at 1.
  unfold R.v17943, N.v17943.
  rewrite ?node_17939.
  rewrite ?node_17942.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17944 (s : N.State) (i : N.Inputs) :
  R.v17944 (state s) (inputs i) = Zmod.unsigned (N.v17944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17944 s i)) at 1.
  unfold R.v17944, N.v17944.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17945 (s : N.State) (i : N.Inputs) :
  R.v17945 (state s) (inputs i) = Zmod.unsigned (N.v17945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17945 s i)) at 1.
  unfold R.v17945, N.v17945.
  rewrite ?node_5836.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17946 (s : N.State) (i : N.Inputs) :
  R.v17946 (state s) (inputs i) = Zmod.unsigned (N.v17946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17946 s i)) at 1.
  unfold R.v17946, N.v17946.
  unfold R.v16463, N.v16463.
  rewrite !state_r178_nr_5F178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r178_nr_5F178 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17947 (s : N.State) (i : N.Inputs) :
  R.v17947 (state s) (inputs i) = Zmod.unsigned (N.v17947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17947 s i)) at 1.
  unfold R.v17947, N.v17947.
  unfold R.v16463, N.v16463.
  rewrite !state_r177_nr_5F177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r177_nr_5F177 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17948 (s : N.State) (i : N.Inputs) :
  R.v17948 (state s) (inputs i) = Zmod.unsigned (N.v17948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17948 s i)) at 1.
  unfold R.v17948, N.v17948.
  unfold R.v6, N.v6.
  rewrite !state_r176_nr_5F176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r176_nr_5F176 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17949 (s : N.State) (i : N.Inputs) :
  R.v17949 (state s) (inputs i) = Zmod.unsigned (N.v17949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17949 s i)) at 1.
  unfold R.v17949, N.v17949.
  unfold R.v6, N.v6.
  rewrite !state_r175_nr_5F175.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r175_nr_5F175 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17950 (s : N.State) (i : N.Inputs) :
  R.v17950 (state s) (inputs i) = Zmod.unsigned (N.v17950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17950 s i)) at 1.
  unfold R.v17950, N.v17950.
  rewrite ?node_17948.
  rewrite ?node_17949.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17951 (s : N.State) (i : N.Inputs) :
  R.v17951 (state s) (inputs i) = Zmod.unsigned (N.v17951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17951 s i)) at 1.
  unfold R.v17951, N.v17951.
  unfold R.v16484, N.v16484.
  rewrite ?node_17950.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17952 (s : N.State) (i : N.Inputs) :
  R.v17952 (state s) (inputs i) = Zmod.unsigned (N.v17952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17952 s i)) at 1.
  unfold R.v17952, N.v17952.
  rewrite ?node_17945.
  rewrite ?node_17946.
  rewrite ?node_17947.
  rewrite ?node_17951.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17953 (s : N.State) (i : N.Inputs) :
  R.v17953 (state s) (inputs i) = Zmod.unsigned (N.v17953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17953 s i)) at 1.
  unfold R.v17953, N.v17953.
  unfold R.v6, N.v6.
  rewrite ?node_17952.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17954 (s : N.State) (i : N.Inputs) :
  R.v17954 (state s) (inputs i) = Zmod.unsigned (N.v17954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17954 s i)) at 1.
  unfold R.v17954, N.v17954.
  rewrite ?node_5837.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17955 (s : N.State) (i : N.Inputs) :
  R.v17955 (state s) (inputs i) = Zmod.unsigned (N.v17955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17955 s i)) at 1.
  unfold R.v17955, N.v17955.
  unfold R.v6, N.v6.
  rewrite ?node_5897.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17956 (s : N.State) (i : N.Inputs) :
  R.v17956 (state s) (inputs i) = Zmod.unsigned (N.v17956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17956 s i)) at 1.
  unfold R.v17956, N.v17956.
  unfold R.v6, N.v6.
  rewrite ?node_5915.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17957 (s : N.State) (i : N.Inputs) :
  R.v17957 (state s) (inputs i) = Zmod.unsigned (N.v17957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17957 s i)) at 1.
  unfold R.v17957, N.v17957.
  rewrite ?node_17954.
  rewrite ?node_17955.
  rewrite ?node_17956.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17958 (s : N.State) (i : N.Inputs) :
  R.v17958 (state s) (inputs i) = Zmod.unsigned (N.v17958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17958 s i)) at 1.
  unfold R.v17958, N.v17958.
  rewrite ?node_17953.
  rewrite ?node_17957.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17959 (s : N.State) (i : N.Inputs) :
  R.v17959 (state s) (inputs i) = Zmod.unsigned (N.v17959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17959 s i)) at 1.
  unfold R.v17959, N.v17959.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17960 (s : N.State) (i : N.Inputs) :
  R.v17960 (state s) (inputs i) = Zmod.unsigned (N.v17960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17960 s i)) at 1.
  unfold R.v17960, N.v17960.
  unfold R.v16463, N.v16463.
  rewrite !state_r177_nr_5F177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r177_nr_5F177 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17961 (s : N.State) (i : N.Inputs) :
  R.v17961 (state s) (inputs i) = Zmod.unsigned (N.v17961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17961 s i)) at 1.
  unfold R.v17961, N.v17961.
  unfold R.v6, N.v6.
  rewrite !state_r176_nr_5F176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r176_nr_5F176 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17962 (s : N.State) (i : N.Inputs) :
  R.v17962 (state s) (inputs i) = Zmod.unsigned (N.v17962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17962 s i)) at 1.
  unfold R.v17962, N.v17962.
  unfold R.v6, N.v6.
  rewrite !state_r175_nr_5F175.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r175_nr_5F175 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17963 (s : N.State) (i : N.Inputs) :
  R.v17963 (state s) (inputs i) = Zmod.unsigned (N.v17963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17963 s i)) at 1.
  unfold R.v17963, N.v17963.
  rewrite ?node_17961.
  rewrite ?node_17962.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17964 (s : N.State) (i : N.Inputs) :
  R.v17964 (state s) (inputs i) = Zmod.unsigned (N.v17964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17964 s i)) at 1.
  unfold R.v17964, N.v17964.
  unfold R.v16484, N.v16484.
  rewrite ?node_17963.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17965 (s : N.State) (i : N.Inputs) :
  R.v17965 (state s) (inputs i) = Zmod.unsigned (N.v17965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17965 s i)) at 1.
  unfold R.v17965, N.v17965.
  rewrite ?node_17960.
  rewrite ?node_17964.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17966 (s : N.State) (i : N.Inputs) :
  R.v17966 (state s) (inputs i) = Zmod.unsigned (N.v17966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17966 s i)) at 1.
  unfold R.v17966, N.v17966.
  unfold R.v6, N.v6.
  rewrite ?node_17965.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17967 (s : N.State) (i : N.Inputs) :
  R.v17967 (state s) (inputs i) = Zmod.unsigned (N.v17967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17967 s i)) at 1.
  unfold R.v17967, N.v17967.
  rewrite ?node_5832.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17968 (s : N.State) (i : N.Inputs) :
  R.v17968 (state s) (inputs i) = Zmod.unsigned (N.v17968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17968 s i)) at 1.
  unfold R.v17968, N.v17968.
  unfold R.v6, N.v6.
  rewrite ?node_5897.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17969 (s : N.State) (i : N.Inputs) :
  R.v17969 (state s) (inputs i) = Zmod.unsigned (N.v17969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17969 s i)) at 1.
  unfold R.v17969, N.v17969.
  rewrite ?node_17967.
  rewrite ?node_17968.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17970 (s : N.State) (i : N.Inputs) :
  R.v17970 (state s) (inputs i) = Zmod.unsigned (N.v17970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17970 s i)) at 1.
  unfold R.v17970, N.v17970.
  rewrite ?node_17966.
  rewrite ?node_17969.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17971 (s : N.State) (i : N.Inputs) :
  R.v17971 (state s) (inputs i) = Zmod.unsigned (N.v17971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17971 s i)) at 1.
  unfold R.v17971, N.v17971.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17972 (s : N.State) (i : N.Inputs) :
  R.v17972 (state s) (inputs i) = Zmod.unsigned (N.v17972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17972 s i)) at 1.
  unfold R.v17972, N.v17972.
  rewrite ?node_5836.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17973 (s : N.State) (i : N.Inputs) :
  R.v17973 (state s) (inputs i) = Zmod.unsigned (N.v17973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17973 s i)) at 1.
  unfold R.v17973, N.v17973.
  unfold R.v6, N.v6.
  rewrite !state_r178_nr_5F178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r178_nr_5F178 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17974 (s : N.State) (i : N.Inputs) :
  R.v17974 (state s) (inputs i) = Zmod.unsigned (N.v17974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17974 s i)) at 1.
  unfold R.v17974, N.v17974.
  unfold R.v6, N.v6.
  rewrite ?node_5832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17975 (s : N.State) (i : N.Inputs) :
  R.v17975 (state s) (inputs i) = Zmod.unsigned (N.v17975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17975 s i)) at 1.
  unfold R.v17975, N.v17975.
  rewrite ?node_17973.
  rewrite ?node_17974.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17976 (s : N.State) (i : N.Inputs) :
  R.v17976 (state s) (inputs i) = Zmod.unsigned (N.v17976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17976 s i)) at 1.
  unfold R.v17976, N.v17976.
  unfold R.v16484, N.v16484.
  rewrite ?node_17975.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17977 (s : N.State) (i : N.Inputs) :
  R.v17977 (state s) (inputs i) = Zmod.unsigned (N.v17977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17977 s i)) at 1.
  unfold R.v17977, N.v17977.
  rewrite ?node_17972.
  rewrite ?node_17976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17978 (s : N.State) (i : N.Inputs) :
  R.v17978 (state s) (inputs i) = Zmod.unsigned (N.v17978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17978 s i)) at 1.
  unfold R.v17978, N.v17978.
  unfold R.v6, N.v6.
  rewrite ?node_17977.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17979 (s : N.State) (i : N.Inputs) :
  R.v17979 (state s) (inputs i) = Zmod.unsigned (N.v17979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17979 s i)) at 1.
  unfold R.v17979, N.v17979.
  rewrite ?node_5837.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17980 (s : N.State) (i : N.Inputs) :
  R.v17980 (state s) (inputs i) = Zmod.unsigned (N.v17980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17980 s i)) at 1.
  unfold R.v17980, N.v17980.
  unfold R.v6, N.v6.
  rewrite ?node_5915.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17981 (s : N.State) (i : N.Inputs) :
  R.v17981 (state s) (inputs i) = Zmod.unsigned (N.v17981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17981 s i)) at 1.
  unfold R.v17981, N.v17981.
  rewrite ?node_17979.
  rewrite ?node_17980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17982 (s : N.State) (i : N.Inputs) :
  R.v17982 (state s) (inputs i) = Zmod.unsigned (N.v17982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17982 s i)) at 1.
  unfold R.v17982, N.v17982.
  rewrite ?node_17978.
  rewrite ?node_17981.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17983 (s : N.State) (i : N.Inputs) :
  R.v17983 (state s) (inputs i) = Zmod.unsigned (N.v17983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17983 s i)) at 1.
  unfold R.v17983, N.v17983.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17984 (s : N.State) (i : N.Inputs) :
  R.v17984 (state s) (inputs i) = Zmod.unsigned (N.v17984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17984 s i)) at 1.
  unfold R.v17984, N.v17984.
  rewrite ?node_5882.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17985 (s : N.State) (i : N.Inputs) :
  R.v17985 (state s) (inputs i) = Zmod.unsigned (N.v17985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17985 s i)) at 1.
  unfold R.v17985, N.v17985.
  unfold R.v16463, N.v16463.
  rewrite !state_r183_nr_5F183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r183_nr_5F183 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17986 (s : N.State) (i : N.Inputs) :
  R.v17986 (state s) (inputs i) = Zmod.unsigned (N.v17986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17986 s i)) at 1.
  unfold R.v17986, N.v17986.
  unfold R.v16463, N.v16463.
  rewrite !state_r182_nr_5F182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r182_nr_5F182 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17987 (s : N.State) (i : N.Inputs) :
  R.v17987 (state s) (inputs i) = Zmod.unsigned (N.v17987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17987 s i)) at 1.
  unfold R.v17987, N.v17987.
  unfold R.v6, N.v6.
  rewrite !state_r181_nr_5F181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r181_nr_5F181 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17988 (s : N.State) (i : N.Inputs) :
  R.v17988 (state s) (inputs i) = Zmod.unsigned (N.v17988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17988 s i)) at 1.
  unfold R.v17988, N.v17988.
  unfold R.v6, N.v6.
  rewrite !state_r180_nr_5F180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r180_nr_5F180 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17989 (s : N.State) (i : N.Inputs) :
  R.v17989 (state s) (inputs i) = Zmod.unsigned (N.v17989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17989 s i)) at 1.
  unfold R.v17989, N.v17989.
  rewrite ?node_17987.
  rewrite ?node_17988.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17990 (s : N.State) (i : N.Inputs) :
  R.v17990 (state s) (inputs i) = Zmod.unsigned (N.v17990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17990 s i)) at 1.
  unfold R.v17990, N.v17990.
  unfold R.v16484, N.v16484.
  rewrite ?node_17989.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17991 (s : N.State) (i : N.Inputs) :
  R.v17991 (state s) (inputs i) = Zmod.unsigned (N.v17991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17991 s i)) at 1.
  unfold R.v17991, N.v17991.
  rewrite ?node_17984.
  rewrite ?node_17985.
  rewrite ?node_17986.
  rewrite ?node_17990.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17992 (s : N.State) (i : N.Inputs) :
  R.v17992 (state s) (inputs i) = Zmod.unsigned (N.v17992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17992 s i)) at 1.
  unfold R.v17992, N.v17992.
  unfold R.v6, N.v6.
  rewrite ?node_17991.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17993 (s : N.State) (i : N.Inputs) :
  R.v17993 (state s) (inputs i) = Zmod.unsigned (N.v17993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17993 s i)) at 1.
  unfold R.v17993, N.v17993.
  rewrite ?node_5883.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17994 (s : N.State) (i : N.Inputs) :
  R.v17994 (state s) (inputs i) = Zmod.unsigned (N.v17994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17994 s i)) at 1.
  unfold R.v17994, N.v17994.
  unfold R.v6, N.v6.
  rewrite ?node_5944.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17995 (s : N.State) (i : N.Inputs) :
  R.v17995 (state s) (inputs i) = Zmod.unsigned (N.v17995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17995 s i)) at 1.
  unfold R.v17995, N.v17995.
  unfold R.v6, N.v6.
  rewrite ?node_5970.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17996 (s : N.State) (i : N.Inputs) :
  R.v17996 (state s) (inputs i) = Zmod.unsigned (N.v17996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17996 s i)) at 1.
  unfold R.v17996, N.v17996.
  rewrite ?node_17993.
  rewrite ?node_17994.
  rewrite ?node_17995.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17997 (s : N.State) (i : N.Inputs) :
  R.v17997 (state s) (inputs i) = Zmod.unsigned (N.v17997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17997 s i)) at 1.
  unfold R.v17997, N.v17997.
  rewrite ?node_17992.
  rewrite ?node_17996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17998 (s : N.State) (i : N.Inputs) :
  R.v17998 (state s) (inputs i) = Zmod.unsigned (N.v17998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17998 s i)) at 1.
  unfold R.v17998, N.v17998.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17999 (s : N.State) (i : N.Inputs) :
  R.v17999 (state s) (inputs i) = Zmod.unsigned (N.v17999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17999 s i)) at 1.
  unfold R.v17999, N.v17999.
  unfold R.v16463, N.v16463.
  rewrite !state_r182_nr_5F182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r182_nr_5F182 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
