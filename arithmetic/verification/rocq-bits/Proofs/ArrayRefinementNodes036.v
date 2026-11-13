(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes035.
Lemma node_36000 (s : N.State) (i : N.Inputs) :
  R.v36000 (state s) (inputs i) = Zmod.unsigned (N.v36000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36000 s i)) at 1.
  unfold R.v36000, N.v36000.
  rewrite ?node_35998.
  rewrite ?node_35999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36001 (s : N.State) (i : N.Inputs) :
  R.v36001 (state s) (inputs i) = Zmod.unsigned (N.v36001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36001 s i)) at 1.
  unfold R.v36001, N.v36001.
  rewrite ?node_35997.
  rewrite ?node_36000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36002 (s : N.State) (i : N.Inputs) :
  R.v36002 (state s) (inputs i) = Zmod.unsigned (N.v36002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36002 s i)) at 1.
  unfold R.v36002, N.v36002.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36003 (s : N.State) (i : N.Inputs) :
  R.v36003 (state s) (inputs i) = Zmod.unsigned (N.v36003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36003 s i)) at 1.
  unfold R.v36003, N.v36003.
  rewrite ?node_15146.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36004 (s : N.State) (i : N.Inputs) :
  R.v36004 (state s) (inputs i) = Zmod.unsigned (N.v36004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36004 s i)) at 1.
  unfold R.v36004, N.v36004.
  unfold R.v6, N.v6.
  rewrite !state_r2094_nr_5F2112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2094_nr_5F2112 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36005 (s : N.State) (i : N.Inputs) :
  R.v36005 (state s) (inputs i) = Zmod.unsigned (N.v36005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36005 s i)) at 1.
  unfold R.v36005, N.v36005.
  unfold R.v6, N.v6.
  rewrite ?node_15142.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36006 (s : N.State) (i : N.Inputs) :
  R.v36006 (state s) (inputs i) = Zmod.unsigned (N.v36006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36006 s i)) at 1.
  unfold R.v36006, N.v36006.
  rewrite ?node_36004.
  rewrite ?node_36005.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36007 (s : N.State) (i : N.Inputs) :
  R.v36007 (state s) (inputs i) = Zmod.unsigned (N.v36007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36007 s i)) at 1.
  unfold R.v36007, N.v36007.
  unfold R.v16484, N.v16484.
  rewrite ?node_36006.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36008 (s : N.State) (i : N.Inputs) :
  R.v36008 (state s) (inputs i) = Zmod.unsigned (N.v36008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36008 s i)) at 1.
  unfold R.v36008, N.v36008.
  rewrite ?node_36003.
  rewrite ?node_36007.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36009 (s : N.State) (i : N.Inputs) :
  R.v36009 (state s) (inputs i) = Zmod.unsigned (N.v36009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36009 s i)) at 1.
  unfold R.v36009, N.v36009.
  unfold R.v6, N.v6.
  rewrite ?node_36008.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36010 (s : N.State) (i : N.Inputs) :
  R.v36010 (state s) (inputs i) = Zmod.unsigned (N.v36010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36010 s i)) at 1.
  unfold R.v36010, N.v36010.
  rewrite ?node_15147.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36011 (s : N.State) (i : N.Inputs) :
  R.v36011 (state s) (inputs i) = Zmod.unsigned (N.v36011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36011 s i)) at 1.
  unfold R.v36011, N.v36011.
  unfold R.v6, N.v6.
  rewrite ?node_15234.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36012 (s : N.State) (i : N.Inputs) :
  R.v36012 (state s) (inputs i) = Zmod.unsigned (N.v36012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36012 s i)) at 1.
  unfold R.v36012, N.v36012.
  rewrite ?node_36010.
  rewrite ?node_36011.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36013 (s : N.State) (i : N.Inputs) :
  R.v36013 (state s) (inputs i) = Zmod.unsigned (N.v36013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36013 s i)) at 1.
  unfold R.v36013, N.v36013.
  rewrite ?node_36009.
  rewrite ?node_36012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36014 (s : N.State) (i : N.Inputs) :
  R.v36014 (state s) (inputs i) = Zmod.unsigned (N.v36014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36014 s i)) at 1.
  unfold R.v36014, N.v36014.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36015 (s : N.State) (i : N.Inputs) :
  R.v36015 (state s) (inputs i) = Zmod.unsigned (N.v36015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36015 s i)) at 1.
  unfold R.v36015, N.v36015.
  unfold R.v6, N.v6.
  rewrite !state_r2096_nr_5F2114.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2096_nr_5F2114 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36016 (s : N.State) (i : N.Inputs) :
  R.v36016 (state s) (inputs i) = Zmod.unsigned (N.v36016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36016 s i)) at 1.
  unfold R.v36016, N.v36016.
  unfold R.v6, N.v6.
  rewrite !state_r2095_nr_5F2113.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2095_nr_5F2113 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36017 (s : N.State) (i : N.Inputs) :
  R.v36017 (state s) (inputs i) = Zmod.unsigned (N.v36017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36017 s i)) at 1.
  unfold R.v36017, N.v36017.
  rewrite ?node_36015.
  rewrite ?node_36016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36018 (s : N.State) (i : N.Inputs) :
  R.v36018 (state s) (inputs i) = Zmod.unsigned (N.v36018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36018 s i)) at 1.
  unfold R.v36018, N.v36018.
  unfold R.v16463, N.v16463.
  rewrite ?node_36017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36019 (s : N.State) (i : N.Inputs) :
  R.v36019 (state s) (inputs i) = Zmod.unsigned (N.v36019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36019 s i)) at 1.
  unfold R.v36019, N.v36019.
  rewrite ?node_15149.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36020 (s : N.State) (i : N.Inputs) :
  R.v36020 (state s) (inputs i) = Zmod.unsigned (N.v36020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36020 s i)) at 1.
  unfold R.v36020, N.v36020.
  unfold R.v6, N.v6.
  rewrite ?node_15236.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36021 (s : N.State) (i : N.Inputs) :
  R.v36021 (state s) (inputs i) = Zmod.unsigned (N.v36021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36021 s i)) at 1.
  unfold R.v36021, N.v36021.
  rewrite ?node_36019.
  rewrite ?node_36020.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36022 (s : N.State) (i : N.Inputs) :
  R.v36022 (state s) (inputs i) = Zmod.unsigned (N.v36022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36022 s i)) at 1.
  unfold R.v36022, N.v36022.
  rewrite ?node_36018.
  rewrite ?node_36021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36023 (s : N.State) (i : N.Inputs) :
  R.v36023 (state s) (inputs i) = Zmod.unsigned (N.v36023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36023 s i)) at 1.
  unfold R.v36023, N.v36023.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36024 (s : N.State) (i : N.Inputs) :
  R.v36024 (state s) (inputs i) = Zmod.unsigned (N.v36024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36024 s i)) at 1.
  unfold R.v36024, N.v36024.
  rewrite ?node_15201.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36025 (s : N.State) (i : N.Inputs) :
  R.v36025 (state s) (inputs i) = Zmod.unsigned (N.v36025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36025 s i)) at 1.
  unfold R.v36025, N.v36025.
  unfold R.v16463, N.v16463.
  rewrite !state_r2099_nr_5F2118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2099_nr_5F2118 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36026 (s : N.State) (i : N.Inputs) :
  R.v36026 (state s) (inputs i) = Zmod.unsigned (N.v36026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36026 s i)) at 1.
  unfold R.v36026, N.v36026.
  unfold R.v16463, N.v16463.
  rewrite !state_r2098_nr_5F2117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2098_nr_5F2117 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36027 (s : N.State) (i : N.Inputs) :
  R.v36027 (state s) (inputs i) = Zmod.unsigned (N.v36027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36027 s i)) at 1.
  unfold R.v36027, N.v36027.
  unfold R.v6, N.v6.
  rewrite !state_r2097_nr_5F2116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2097_nr_5F2116 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36028 (s : N.State) (i : N.Inputs) :
  R.v36028 (state s) (inputs i) = Zmod.unsigned (N.v36028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36028 s i)) at 1.
  unfold R.v36028, N.v36028.
  unfold R.v19, N.v19.
  rewrite ?node_36027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36029 (s : N.State) (i : N.Inputs) :
  R.v36029 (state s) (inputs i) = Zmod.unsigned (N.v36029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36029 s i)) at 1.
  unfold R.v36029, N.v36029.
  unfold R.v16484, N.v16484.
  rewrite ?node_36028.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36030 (s : N.State) (i : N.Inputs) :
  R.v36030 (state s) (inputs i) = Zmod.unsigned (N.v36030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36030 s i)) at 1.
  unfold R.v36030, N.v36030.
  rewrite ?node_36024.
  rewrite ?node_36025.
  rewrite ?node_36026.
  rewrite ?node_36029.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36031 (s : N.State) (i : N.Inputs) :
  R.v36031 (state s) (inputs i) = Zmod.unsigned (N.v36031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36031 s i)) at 1.
  unfold R.v36031, N.v36031.
  unfold R.v6, N.v6.
  rewrite ?node_36030.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36032 (s : N.State) (i : N.Inputs) :
  R.v36032 (state s) (inputs i) = Zmod.unsigned (N.v36032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36032 s i)) at 1.
  unfold R.v36032, N.v36032.
  rewrite ?node_15202.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36033 (s : N.State) (i : N.Inputs) :
  R.v36033 (state s) (inputs i) = Zmod.unsigned (N.v36033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36033 s i)) at 1.
  unfold R.v36033, N.v36033.
  unfold R.v6, N.v6.
  rewrite ?node_15268.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36034 (s : N.State) (i : N.Inputs) :
  R.v36034 (state s) (inputs i) = Zmod.unsigned (N.v36034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36034 s i)) at 1.
  unfold R.v36034, N.v36034.
  unfold R.v6, N.v6.
  rewrite ?node_15293.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36035 (s : N.State) (i : N.Inputs) :
  R.v36035 (state s) (inputs i) = Zmod.unsigned (N.v36035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36035 s i)) at 1.
  unfold R.v36035, N.v36035.
  rewrite ?node_36032.
  rewrite ?node_36033.
  rewrite ?node_36034.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36036 (s : N.State) (i : N.Inputs) :
  R.v36036 (state s) (inputs i) = Zmod.unsigned (N.v36036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36036 s i)) at 1.
  unfold R.v36036, N.v36036.
  rewrite ?node_36031.
  rewrite ?node_36035.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36037 (s : N.State) (i : N.Inputs) :
  R.v36037 (state s) (inputs i) = Zmod.unsigned (N.v36037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36037 s i)) at 1.
  unfold R.v36037, N.v36037.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36038 (s : N.State) (i : N.Inputs) :
  R.v36038 (state s) (inputs i) = Zmod.unsigned (N.v36038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36038 s i)) at 1.
  unfold R.v36038, N.v36038.
  unfold R.v16463, N.v16463.
  rewrite !state_r2098_nr_5F2117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2098_nr_5F2117 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36039 (s : N.State) (i : N.Inputs) :
  R.v36039 (state s) (inputs i) = Zmod.unsigned (N.v36039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36039 s i)) at 1.
  unfold R.v36039, N.v36039.
  unfold R.v6, N.v6.
  rewrite !state_r2097_nr_5F2116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2097_nr_5F2116 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36040 (s : N.State) (i : N.Inputs) :
  R.v36040 (state s) (inputs i) = Zmod.unsigned (N.v36040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36040 s i)) at 1.
  unfold R.v36040, N.v36040.
  unfold R.v19, N.v19.
  rewrite ?node_36039.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36041 (s : N.State) (i : N.Inputs) :
  R.v36041 (state s) (inputs i) = Zmod.unsigned (N.v36041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36041 s i)) at 1.
  unfold R.v36041, N.v36041.
  unfold R.v16484, N.v16484.
  rewrite ?node_36040.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36042 (s : N.State) (i : N.Inputs) :
  R.v36042 (state s) (inputs i) = Zmod.unsigned (N.v36042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36042 s i)) at 1.
  unfold R.v36042, N.v36042.
  rewrite ?node_36038.
  rewrite ?node_36041.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36043 (s : N.State) (i : N.Inputs) :
  R.v36043 (state s) (inputs i) = Zmod.unsigned (N.v36043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36043 s i)) at 1.
  unfold R.v36043, N.v36043.
  unfold R.v6, N.v6.
  rewrite ?node_36042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36044 (s : N.State) (i : N.Inputs) :
  R.v36044 (state s) (inputs i) = Zmod.unsigned (N.v36044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36044 s i)) at 1.
  unfold R.v36044, N.v36044.
  rewrite ?node_15197.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36045 (s : N.State) (i : N.Inputs) :
  R.v36045 (state s) (inputs i) = Zmod.unsigned (N.v36045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36045 s i)) at 1.
  unfold R.v36045, N.v36045.
  unfold R.v6, N.v6.
  rewrite ?node_15268.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36046 (s : N.State) (i : N.Inputs) :
  R.v36046 (state s) (inputs i) = Zmod.unsigned (N.v36046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36046 s i)) at 1.
  unfold R.v36046, N.v36046.
  rewrite ?node_36044.
  rewrite ?node_36045.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36047 (s : N.State) (i : N.Inputs) :
  R.v36047 (state s) (inputs i) = Zmod.unsigned (N.v36047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36047 s i)) at 1.
  unfold R.v36047, N.v36047.
  rewrite ?node_36043.
  rewrite ?node_36046.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36048 (s : N.State) (i : N.Inputs) :
  R.v36048 (state s) (inputs i) = Zmod.unsigned (N.v36048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36048 s i)) at 1.
  unfold R.v36048, N.v36048.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36049 (s : N.State) (i : N.Inputs) :
  R.v36049 (state s) (inputs i) = Zmod.unsigned (N.v36049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36049 s i)) at 1.
  unfold R.v36049, N.v36049.
  rewrite ?node_15201.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36050 (s : N.State) (i : N.Inputs) :
  R.v36050 (state s) (inputs i) = Zmod.unsigned (N.v36050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36050 s i)) at 1.
  unfold R.v36050, N.v36050.
  unfold R.v6, N.v6.
  rewrite !state_r2099_nr_5F2118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2099_nr_5F2118 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36051 (s : N.State) (i : N.Inputs) :
  R.v36051 (state s) (inputs i) = Zmod.unsigned (N.v36051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36051 s i)) at 1.
  unfold R.v36051, N.v36051.
  unfold R.v6, N.v6.
  rewrite ?node_15197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36052 (s : N.State) (i : N.Inputs) :
  R.v36052 (state s) (inputs i) = Zmod.unsigned (N.v36052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36052 s i)) at 1.
  unfold R.v36052, N.v36052.
  rewrite ?node_36050.
  rewrite ?node_36051.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36053 (s : N.State) (i : N.Inputs) :
  R.v36053 (state s) (inputs i) = Zmod.unsigned (N.v36053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36053 s i)) at 1.
  unfold R.v36053, N.v36053.
  unfold R.v16484, N.v16484.
  rewrite ?node_36052.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36054 (s : N.State) (i : N.Inputs) :
  R.v36054 (state s) (inputs i) = Zmod.unsigned (N.v36054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36054 s i)) at 1.
  unfold R.v36054, N.v36054.
  rewrite ?node_36049.
  rewrite ?node_36053.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36055 (s : N.State) (i : N.Inputs) :
  R.v36055 (state s) (inputs i) = Zmod.unsigned (N.v36055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36055 s i)) at 1.
  unfold R.v36055, N.v36055.
  unfold R.v6, N.v6.
  rewrite ?node_36054.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36056 (s : N.State) (i : N.Inputs) :
  R.v36056 (state s) (inputs i) = Zmod.unsigned (N.v36056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36056 s i)) at 1.
  unfold R.v36056, N.v36056.
  rewrite ?node_15202.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36057 (s : N.State) (i : N.Inputs) :
  R.v36057 (state s) (inputs i) = Zmod.unsigned (N.v36057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36057 s i)) at 1.
  unfold R.v36057, N.v36057.
  unfold R.v6, N.v6.
  rewrite ?node_15293.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36058 (s : N.State) (i : N.Inputs) :
  R.v36058 (state s) (inputs i) = Zmod.unsigned (N.v36058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36058 s i)) at 1.
  unfold R.v36058, N.v36058.
  rewrite ?node_36056.
  rewrite ?node_36057.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36059 (s : N.State) (i : N.Inputs) :
  R.v36059 (state s) (inputs i) = Zmod.unsigned (N.v36059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36059 s i)) at 1.
  unfold R.v36059, N.v36059.
  rewrite ?node_36055.
  rewrite ?node_36058.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36060 (s : N.State) (i : N.Inputs) :
  R.v36060 (state s) (inputs i) = Zmod.unsigned (N.v36060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36060 s i)) at 1.
  unfold R.v36060, N.v36060.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36061 (s : N.State) (i : N.Inputs) :
  R.v36061 (state s) (inputs i) = Zmod.unsigned (N.v36061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36061 s i)) at 1.
  unfold R.v36061, N.v36061.
  rewrite ?node_15208.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36062 (s : N.State) (i : N.Inputs) :
  R.v36062 (state s) (inputs i) = Zmod.unsigned (N.v36062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36062 s i)) at 1.
  unfold R.v36062, N.v36062.
  unfold R.v16463, N.v16463.
  rewrite !state_r2103_nr_5F2122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2103_nr_5F2122 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36063 (s : N.State) (i : N.Inputs) :
  R.v36063 (state s) (inputs i) = Zmod.unsigned (N.v36063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36063 s i)) at 1.
  unfold R.v36063, N.v36063.
  unfold R.v16463, N.v16463.
  rewrite !state_r2102_nr_5F2121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2102_nr_5F2121 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36064 (s : N.State) (i : N.Inputs) :
  R.v36064 (state s) (inputs i) = Zmod.unsigned (N.v36064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36064 s i)) at 1.
  unfold R.v36064, N.v36064.
  unfold R.v6, N.v6.
  rewrite !state_r2101_nr_5F2120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2101_nr_5F2120 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36065 (s : N.State) (i : N.Inputs) :
  R.v36065 (state s) (inputs i) = Zmod.unsigned (N.v36065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36065 s i)) at 1.
  unfold R.v36065, N.v36065.
  unfold R.v6, N.v6.
  rewrite !state_r2100_nr_5F2119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2100_nr_5F2119 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36066 (s : N.State) (i : N.Inputs) :
  R.v36066 (state s) (inputs i) = Zmod.unsigned (N.v36066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36066 s i)) at 1.
  unfold R.v36066, N.v36066.
  rewrite ?node_36064.
  rewrite ?node_36065.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36067 (s : N.State) (i : N.Inputs) :
  R.v36067 (state s) (inputs i) = Zmod.unsigned (N.v36067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36067 s i)) at 1.
  unfold R.v36067, N.v36067.
  unfold R.v16484, N.v16484.
  rewrite ?node_36066.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36068 (s : N.State) (i : N.Inputs) :
  R.v36068 (state s) (inputs i) = Zmod.unsigned (N.v36068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36068 s i)) at 1.
  unfold R.v36068, N.v36068.
  rewrite ?node_36061.
  rewrite ?node_36062.
  rewrite ?node_36063.
  rewrite ?node_36067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36069 (s : N.State) (i : N.Inputs) :
  R.v36069 (state s) (inputs i) = Zmod.unsigned (N.v36069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36069 s i)) at 1.
  unfold R.v36069, N.v36069.
  unfold R.v6, N.v6.
  rewrite ?node_36068.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36070 (s : N.State) (i : N.Inputs) :
  R.v36070 (state s) (inputs i) = Zmod.unsigned (N.v36070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36070 s i)) at 1.
  unfold R.v36070, N.v36070.
  rewrite ?node_15209.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36071 (s : N.State) (i : N.Inputs) :
  R.v36071 (state s) (inputs i) = Zmod.unsigned (N.v36071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36071 s i)) at 1.
  unfold R.v36071, N.v36071.
  unfold R.v6, N.v6.
  rewrite ?node_15275.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36072 (s : N.State) (i : N.Inputs) :
  R.v36072 (state s) (inputs i) = Zmod.unsigned (N.v36072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36072 s i)) at 1.
  unfold R.v36072, N.v36072.
  unfold R.v6, N.v6.
  rewrite ?node_15296.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36073 (s : N.State) (i : N.Inputs) :
  R.v36073 (state s) (inputs i) = Zmod.unsigned (N.v36073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36073 s i)) at 1.
  unfold R.v36073, N.v36073.
  rewrite ?node_36070.
  rewrite ?node_36071.
  rewrite ?node_36072.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36074 (s : N.State) (i : N.Inputs) :
  R.v36074 (state s) (inputs i) = Zmod.unsigned (N.v36074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36074 s i)) at 1.
  unfold R.v36074, N.v36074.
  rewrite ?node_36069.
  rewrite ?node_36073.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36075 (s : N.State) (i : N.Inputs) :
  R.v36075 (state s) (inputs i) = Zmod.unsigned (N.v36075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36075 s i)) at 1.
  unfold R.v36075, N.v36075.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36076 (s : N.State) (i : N.Inputs) :
  R.v36076 (state s) (inputs i) = Zmod.unsigned (N.v36076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36076 s i)) at 1.
  unfold R.v36076, N.v36076.
  unfold R.v16463, N.v16463.
  rewrite !state_r2102_nr_5F2121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2102_nr_5F2121 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36077 (s : N.State) (i : N.Inputs) :
  R.v36077 (state s) (inputs i) = Zmod.unsigned (N.v36077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36077 s i)) at 1.
  unfold R.v36077, N.v36077.
  unfold R.v6, N.v6.
  rewrite !state_r2101_nr_5F2120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2101_nr_5F2120 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36078 (s : N.State) (i : N.Inputs) :
  R.v36078 (state s) (inputs i) = Zmod.unsigned (N.v36078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36078 s i)) at 1.
  unfold R.v36078, N.v36078.
  unfold R.v6, N.v6.
  rewrite !state_r2100_nr_5F2119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2100_nr_5F2119 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36079 (s : N.State) (i : N.Inputs) :
  R.v36079 (state s) (inputs i) = Zmod.unsigned (N.v36079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36079 s i)) at 1.
  unfold R.v36079, N.v36079.
  rewrite ?node_36077.
  rewrite ?node_36078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36080 (s : N.State) (i : N.Inputs) :
  R.v36080 (state s) (inputs i) = Zmod.unsigned (N.v36080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36080 s i)) at 1.
  unfold R.v36080, N.v36080.
  unfold R.v16484, N.v16484.
  rewrite ?node_36079.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36081 (s : N.State) (i : N.Inputs) :
  R.v36081 (state s) (inputs i) = Zmod.unsigned (N.v36081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36081 s i)) at 1.
  unfold R.v36081, N.v36081.
  rewrite ?node_36076.
  rewrite ?node_36080.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36082 (s : N.State) (i : N.Inputs) :
  R.v36082 (state s) (inputs i) = Zmod.unsigned (N.v36082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36082 s i)) at 1.
  unfold R.v36082, N.v36082.
  unfold R.v6, N.v6.
  rewrite ?node_36081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36083 (s : N.State) (i : N.Inputs) :
  R.v36083 (state s) (inputs i) = Zmod.unsigned (N.v36083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36083 s i)) at 1.
  unfold R.v36083, N.v36083.
  rewrite ?node_15204.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36084 (s : N.State) (i : N.Inputs) :
  R.v36084 (state s) (inputs i) = Zmod.unsigned (N.v36084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36084 s i)) at 1.
  unfold R.v36084, N.v36084.
  unfold R.v6, N.v6.
  rewrite ?node_15275.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36085 (s : N.State) (i : N.Inputs) :
  R.v36085 (state s) (inputs i) = Zmod.unsigned (N.v36085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36085 s i)) at 1.
  unfold R.v36085, N.v36085.
  rewrite ?node_36083.
  rewrite ?node_36084.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36086 (s : N.State) (i : N.Inputs) :
  R.v36086 (state s) (inputs i) = Zmod.unsigned (N.v36086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36086 s i)) at 1.
  unfold R.v36086, N.v36086.
  rewrite ?node_36082.
  rewrite ?node_36085.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36087 (s : N.State) (i : N.Inputs) :
  R.v36087 (state s) (inputs i) = Zmod.unsigned (N.v36087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36087 s i)) at 1.
  unfold R.v36087, N.v36087.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36088 (s : N.State) (i : N.Inputs) :
  R.v36088 (state s) (inputs i) = Zmod.unsigned (N.v36088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36088 s i)) at 1.
  unfold R.v36088, N.v36088.
  rewrite ?node_15208.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36089 (s : N.State) (i : N.Inputs) :
  R.v36089 (state s) (inputs i) = Zmod.unsigned (N.v36089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36089 s i)) at 1.
  unfold R.v36089, N.v36089.
  unfold R.v6, N.v6.
  rewrite !state_r2103_nr_5F2122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2103_nr_5F2122 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36090 (s : N.State) (i : N.Inputs) :
  R.v36090 (state s) (inputs i) = Zmod.unsigned (N.v36090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36090 s i)) at 1.
  unfold R.v36090, N.v36090.
  unfold R.v6, N.v6.
  rewrite ?node_15204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36091 (s : N.State) (i : N.Inputs) :
  R.v36091 (state s) (inputs i) = Zmod.unsigned (N.v36091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36091 s i)) at 1.
  unfold R.v36091, N.v36091.
  rewrite ?node_36089.
  rewrite ?node_36090.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36092 (s : N.State) (i : N.Inputs) :
  R.v36092 (state s) (inputs i) = Zmod.unsigned (N.v36092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36092 s i)) at 1.
  unfold R.v36092, N.v36092.
  unfold R.v16484, N.v16484.
  rewrite ?node_36091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36093 (s : N.State) (i : N.Inputs) :
  R.v36093 (state s) (inputs i) = Zmod.unsigned (N.v36093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36093 s i)) at 1.
  unfold R.v36093, N.v36093.
  rewrite ?node_36088.
  rewrite ?node_36092.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36094 (s : N.State) (i : N.Inputs) :
  R.v36094 (state s) (inputs i) = Zmod.unsigned (N.v36094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36094 s i)) at 1.
  unfold R.v36094, N.v36094.
  unfold R.v6, N.v6.
  rewrite ?node_36093.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36095 (s : N.State) (i : N.Inputs) :
  R.v36095 (state s) (inputs i) = Zmod.unsigned (N.v36095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36095 s i)) at 1.
  unfold R.v36095, N.v36095.
  rewrite ?node_15209.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36096 (s : N.State) (i : N.Inputs) :
  R.v36096 (state s) (inputs i) = Zmod.unsigned (N.v36096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36096 s i)) at 1.
  unfold R.v36096, N.v36096.
  unfold R.v6, N.v6.
  rewrite ?node_15296.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36097 (s : N.State) (i : N.Inputs) :
  R.v36097 (state s) (inputs i) = Zmod.unsigned (N.v36097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36097 s i)) at 1.
  unfold R.v36097, N.v36097.
  rewrite ?node_36095.
  rewrite ?node_36096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36098 (s : N.State) (i : N.Inputs) :
  R.v36098 (state s) (inputs i) = Zmod.unsigned (N.v36098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36098 s i)) at 1.
  unfold R.v36098, N.v36098.
  rewrite ?node_36094.
  rewrite ?node_36097.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36099 (s : N.State) (i : N.Inputs) :
  R.v36099 (state s) (inputs i) = Zmod.unsigned (N.v36099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36099 s i)) at 1.
  unfold R.v36099, N.v36099.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36100 (s : N.State) (i : N.Inputs) :
  R.v36100 (state s) (inputs i) = Zmod.unsigned (N.v36100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36100 s i)) at 1.
  unfold R.v36100, N.v36100.
  rewrite ?node_15216.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36101 (s : N.State) (i : N.Inputs) :
  R.v36101 (state s) (inputs i) = Zmod.unsigned (N.v36101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36101 s i)) at 1.
  unfold R.v36101, N.v36101.
  unfold R.v16463, N.v16463.
  rewrite !state_r2107_nr_5F2126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2107_nr_5F2126 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36102 (s : N.State) (i : N.Inputs) :
  R.v36102 (state s) (inputs i) = Zmod.unsigned (N.v36102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36102 s i)) at 1.
  unfold R.v36102, N.v36102.
  unfold R.v16463, N.v16463.
  rewrite !state_r2106_nr_5F2125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2106_nr_5F2125 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36103 (s : N.State) (i : N.Inputs) :
  R.v36103 (state s) (inputs i) = Zmod.unsigned (N.v36103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36103 s i)) at 1.
  unfold R.v36103, N.v36103.
  unfold R.v6, N.v6.
  rewrite !state_r2105_nr_5F2124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2105_nr_5F2124 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36104 (s : N.State) (i : N.Inputs) :
  R.v36104 (state s) (inputs i) = Zmod.unsigned (N.v36104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36104 s i)) at 1.
  unfold R.v36104, N.v36104.
  unfold R.v6, N.v6.
  rewrite !state_r2104_nr_5F2123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2104_nr_5F2123 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36105 (s : N.State) (i : N.Inputs) :
  R.v36105 (state s) (inputs i) = Zmod.unsigned (N.v36105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36105 s i)) at 1.
  unfold R.v36105, N.v36105.
  rewrite ?node_36103.
  rewrite ?node_36104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36106 (s : N.State) (i : N.Inputs) :
  R.v36106 (state s) (inputs i) = Zmod.unsigned (N.v36106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36106 s i)) at 1.
  unfold R.v36106, N.v36106.
  unfold R.v16484, N.v16484.
  rewrite ?node_36105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36107 (s : N.State) (i : N.Inputs) :
  R.v36107 (state s) (inputs i) = Zmod.unsigned (N.v36107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36107 s i)) at 1.
  unfold R.v36107, N.v36107.
  rewrite ?node_36100.
  rewrite ?node_36101.
  rewrite ?node_36102.
  rewrite ?node_36106.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36108 (s : N.State) (i : N.Inputs) :
  R.v36108 (state s) (inputs i) = Zmod.unsigned (N.v36108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36108 s i)) at 1.
  unfold R.v36108, N.v36108.
  unfold R.v6, N.v6.
  rewrite ?node_36107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36109 (s : N.State) (i : N.Inputs) :
  R.v36109 (state s) (inputs i) = Zmod.unsigned (N.v36109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36109 s i)) at 1.
  unfold R.v36109, N.v36109.
  rewrite ?node_15217.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36110 (s : N.State) (i : N.Inputs) :
  R.v36110 (state s) (inputs i) = Zmod.unsigned (N.v36110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36110 s i)) at 1.
  unfold R.v36110, N.v36110.
  unfold R.v6, N.v6.
  rewrite ?node_15283.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36111 (s : N.State) (i : N.Inputs) :
  R.v36111 (state s) (inputs i) = Zmod.unsigned (N.v36111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36111 s i)) at 1.
  unfold R.v36111, N.v36111.
  unfold R.v6, N.v6.
  rewrite ?node_15300.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36112 (s : N.State) (i : N.Inputs) :
  R.v36112 (state s) (inputs i) = Zmod.unsigned (N.v36112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36112 s i)) at 1.
  unfold R.v36112, N.v36112.
  rewrite ?node_36109.
  rewrite ?node_36110.
  rewrite ?node_36111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36113 (s : N.State) (i : N.Inputs) :
  R.v36113 (state s) (inputs i) = Zmod.unsigned (N.v36113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36113 s i)) at 1.
  unfold R.v36113, N.v36113.
  rewrite ?node_36108.
  rewrite ?node_36112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36114 (s : N.State) (i : N.Inputs) :
  R.v36114 (state s) (inputs i) = Zmod.unsigned (N.v36114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36114 s i)) at 1.
  unfold R.v36114, N.v36114.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36115 (s : N.State) (i : N.Inputs) :
  R.v36115 (state s) (inputs i) = Zmod.unsigned (N.v36115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36115 s i)) at 1.
  unfold R.v36115, N.v36115.
  unfold R.v16463, N.v16463.
  rewrite !state_r2106_nr_5F2125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2106_nr_5F2125 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36116 (s : N.State) (i : N.Inputs) :
  R.v36116 (state s) (inputs i) = Zmod.unsigned (N.v36116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36116 s i)) at 1.
  unfold R.v36116, N.v36116.
  unfold R.v6, N.v6.
  rewrite !state_r2105_nr_5F2124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2105_nr_5F2124 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36117 (s : N.State) (i : N.Inputs) :
  R.v36117 (state s) (inputs i) = Zmod.unsigned (N.v36117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36117 s i)) at 1.
  unfold R.v36117, N.v36117.
  unfold R.v6, N.v6.
  rewrite !state_r2104_nr_5F2123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2104_nr_5F2123 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36118 (s : N.State) (i : N.Inputs) :
  R.v36118 (state s) (inputs i) = Zmod.unsigned (N.v36118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36118 s i)) at 1.
  unfold R.v36118, N.v36118.
  rewrite ?node_36116.
  rewrite ?node_36117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36119 (s : N.State) (i : N.Inputs) :
  R.v36119 (state s) (inputs i) = Zmod.unsigned (N.v36119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36119 s i)) at 1.
  unfold R.v36119, N.v36119.
  unfold R.v16484, N.v16484.
  rewrite ?node_36118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36120 (s : N.State) (i : N.Inputs) :
  R.v36120 (state s) (inputs i) = Zmod.unsigned (N.v36120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36120 s i)) at 1.
  unfold R.v36120, N.v36120.
  rewrite ?node_36115.
  rewrite ?node_36119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36121 (s : N.State) (i : N.Inputs) :
  R.v36121 (state s) (inputs i) = Zmod.unsigned (N.v36121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36121 s i)) at 1.
  unfold R.v36121, N.v36121.
  unfold R.v6, N.v6.
  rewrite ?node_36120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36122 (s : N.State) (i : N.Inputs) :
  R.v36122 (state s) (inputs i) = Zmod.unsigned (N.v36122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36122 s i)) at 1.
  unfold R.v36122, N.v36122.
  rewrite ?node_15212.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36123 (s : N.State) (i : N.Inputs) :
  R.v36123 (state s) (inputs i) = Zmod.unsigned (N.v36123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36123 s i)) at 1.
  unfold R.v36123, N.v36123.
  unfold R.v6, N.v6.
  rewrite ?node_15283.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36124 (s : N.State) (i : N.Inputs) :
  R.v36124 (state s) (inputs i) = Zmod.unsigned (N.v36124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36124 s i)) at 1.
  unfold R.v36124, N.v36124.
  rewrite ?node_36122.
  rewrite ?node_36123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36125 (s : N.State) (i : N.Inputs) :
  R.v36125 (state s) (inputs i) = Zmod.unsigned (N.v36125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36125 s i)) at 1.
  unfold R.v36125, N.v36125.
  rewrite ?node_36121.
  rewrite ?node_36124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36126 (s : N.State) (i : N.Inputs) :
  R.v36126 (state s) (inputs i) = Zmod.unsigned (N.v36126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36126 s i)) at 1.
  unfold R.v36126, N.v36126.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36127 (s : N.State) (i : N.Inputs) :
  R.v36127 (state s) (inputs i) = Zmod.unsigned (N.v36127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36127 s i)) at 1.
  unfold R.v36127, N.v36127.
  rewrite ?node_15216.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36128 (s : N.State) (i : N.Inputs) :
  R.v36128 (state s) (inputs i) = Zmod.unsigned (N.v36128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36128 s i)) at 1.
  unfold R.v36128, N.v36128.
  unfold R.v6, N.v6.
  rewrite !state_r2107_nr_5F2126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2107_nr_5F2126 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36129 (s : N.State) (i : N.Inputs) :
  R.v36129 (state s) (inputs i) = Zmod.unsigned (N.v36129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36129 s i)) at 1.
  unfold R.v36129, N.v36129.
  unfold R.v6, N.v6.
  rewrite ?node_15212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36130 (s : N.State) (i : N.Inputs) :
  R.v36130 (state s) (inputs i) = Zmod.unsigned (N.v36130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36130 s i)) at 1.
  unfold R.v36130, N.v36130.
  rewrite ?node_36128.
  rewrite ?node_36129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36131 (s : N.State) (i : N.Inputs) :
  R.v36131 (state s) (inputs i) = Zmod.unsigned (N.v36131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36131 s i)) at 1.
  unfold R.v36131, N.v36131.
  unfold R.v16484, N.v16484.
  rewrite ?node_36130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36132 (s : N.State) (i : N.Inputs) :
  R.v36132 (state s) (inputs i) = Zmod.unsigned (N.v36132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36132 s i)) at 1.
  unfold R.v36132, N.v36132.
  rewrite ?node_36127.
  rewrite ?node_36131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36133 (s : N.State) (i : N.Inputs) :
  R.v36133 (state s) (inputs i) = Zmod.unsigned (N.v36133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36133 s i)) at 1.
  unfold R.v36133, N.v36133.
  unfold R.v6, N.v6.
  rewrite ?node_36132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36134 (s : N.State) (i : N.Inputs) :
  R.v36134 (state s) (inputs i) = Zmod.unsigned (N.v36134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36134 s i)) at 1.
  unfold R.v36134, N.v36134.
  rewrite ?node_15217.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36135 (s : N.State) (i : N.Inputs) :
  R.v36135 (state s) (inputs i) = Zmod.unsigned (N.v36135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36135 s i)) at 1.
  unfold R.v36135, N.v36135.
  unfold R.v6, N.v6.
  rewrite ?node_15300.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36136 (s : N.State) (i : N.Inputs) :
  R.v36136 (state s) (inputs i) = Zmod.unsigned (N.v36136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36136 s i)) at 1.
  unfold R.v36136, N.v36136.
  rewrite ?node_36134.
  rewrite ?node_36135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36137 (s : N.State) (i : N.Inputs) :
  R.v36137 (state s) (inputs i) = Zmod.unsigned (N.v36137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36137 s i)) at 1.
  unfold R.v36137, N.v36137.
  rewrite ?node_36133.
  rewrite ?node_36136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36138 (s : N.State) (i : N.Inputs) :
  R.v36138 (state s) (inputs i) = Zmod.unsigned (N.v36138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36138 s i)) at 1.
  unfold R.v36138, N.v36138.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36139 (s : N.State) (i : N.Inputs) :
  R.v36139 (state s) (inputs i) = Zmod.unsigned (N.v36139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36139 s i)) at 1.
  unfold R.v36139, N.v36139.
  unfold R.v6, N.v6.
  rewrite !state_r2109_nr_5F2128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2109_nr_5F2128 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36140 (s : N.State) (i : N.Inputs) :
  R.v36140 (state s) (inputs i) = Zmod.unsigned (N.v36140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36140 s i)) at 1.
  unfold R.v36140, N.v36140.
  unfold R.v6, N.v6.
  rewrite !state_r2108_nr_5F2127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2108_nr_5F2127 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36141 (s : N.State) (i : N.Inputs) :
  R.v36141 (state s) (inputs i) = Zmod.unsigned (N.v36141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36141 s i)) at 1.
  unfold R.v36141, N.v36141.
  rewrite ?node_36139.
  rewrite ?node_36140.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36142 (s : N.State) (i : N.Inputs) :
  R.v36142 (state s) (inputs i) = Zmod.unsigned (N.v36142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36142 s i)) at 1.
  unfold R.v36142, N.v36142.
  unfold R.v16463, N.v16463.
  rewrite ?node_36141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36143 (s : N.State) (i : N.Inputs) :
  R.v36143 (state s) (inputs i) = Zmod.unsigned (N.v36143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36143 s i)) at 1.
  unfold R.v36143, N.v36143.
  rewrite ?node_15219.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36144 (s : N.State) (i : N.Inputs) :
  R.v36144 (state s) (inputs i) = Zmod.unsigned (N.v36144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36144 s i)) at 1.
  unfold R.v36144, N.v36144.
  unfold R.v6, N.v6.
  rewrite ?node_15302.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36145 (s : N.State) (i : N.Inputs) :
  R.v36145 (state s) (inputs i) = Zmod.unsigned (N.v36145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36145 s i)) at 1.
  unfold R.v36145, N.v36145.
  rewrite ?node_36143.
  rewrite ?node_36144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36146 (s : N.State) (i : N.Inputs) :
  R.v36146 (state s) (inputs i) = Zmod.unsigned (N.v36146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36146 s i)) at 1.
  unfold R.v36146, N.v36146.
  rewrite ?node_36142.
  rewrite ?node_36145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36147 (s : N.State) (i : N.Inputs) :
  R.v36147 (state s) (inputs i) = Zmod.unsigned (N.v36147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36147 s i)) at 1.
  unfold R.v36147, N.v36147.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36148 (s : N.State) (i : N.Inputs) :
  R.v36148 (state s) (inputs i) = Zmod.unsigned (N.v36148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36148 s i)) at 1.
  unfold R.v36148, N.v36148.
  rewrite ?node_15268.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36149 (s : N.State) (i : N.Inputs) :
  R.v36149 (state s) (inputs i) = Zmod.unsigned (N.v36149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36149 s i)) at 1.
  unfold R.v36149, N.v36149.
  unfold R.v16463, N.v16463.
  rewrite !state_r2113_nr_5F2132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2113_nr_5F2132 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36150 (s : N.State) (i : N.Inputs) :
  R.v36150 (state s) (inputs i) = Zmod.unsigned (N.v36150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36150 s i)) at 1.
  unfold R.v36150, N.v36150.
  unfold R.v16463, N.v16463.
  rewrite !state_r2112_nr_5F2131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2112_nr_5F2131 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36151 (s : N.State) (i : N.Inputs) :
  R.v36151 (state s) (inputs i) = Zmod.unsigned (N.v36151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36151 s i)) at 1.
  unfold R.v36151, N.v36151.
  unfold R.v6, N.v6.
  rewrite !state_r2111_nr_5F2130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2111_nr_5F2130 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36152 (s : N.State) (i : N.Inputs) :
  R.v36152 (state s) (inputs i) = Zmod.unsigned (N.v36152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36152 s i)) at 1.
  unfold R.v36152, N.v36152.
  unfold R.v6, N.v6.
  rewrite !state_r2110_nr_5F2129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2110_nr_5F2129 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36153 (s : N.State) (i : N.Inputs) :
  R.v36153 (state s) (inputs i) = Zmod.unsigned (N.v36153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36153 s i)) at 1.
  unfold R.v36153, N.v36153.
  rewrite ?node_36151.
  rewrite ?node_36152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36154 (s : N.State) (i : N.Inputs) :
  R.v36154 (state s) (inputs i) = Zmod.unsigned (N.v36154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36154 s i)) at 1.
  unfold R.v36154, N.v36154.
  unfold R.v16484, N.v16484.
  rewrite ?node_36153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36155 (s : N.State) (i : N.Inputs) :
  R.v36155 (state s) (inputs i) = Zmod.unsigned (N.v36155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36155 s i)) at 1.
  unfold R.v36155, N.v36155.
  rewrite ?node_36148.
  rewrite ?node_36149.
  rewrite ?node_36150.
  rewrite ?node_36154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36156 (s : N.State) (i : N.Inputs) :
  R.v36156 (state s) (inputs i) = Zmod.unsigned (N.v36156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36156 s i)) at 1.
  unfold R.v36156, N.v36156.
  unfold R.v6, N.v6.
  rewrite ?node_36155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36157 (s : N.State) (i : N.Inputs) :
  R.v36157 (state s) (inputs i) = Zmod.unsigned (N.v36157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36157 s i)) at 1.
  unfold R.v36157, N.v36157.
  rewrite ?node_15269.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36158 (s : N.State) (i : N.Inputs) :
  R.v36158 (state s) (inputs i) = Zmod.unsigned (N.v36158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36158 s i)) at 1.
  unfold R.v36158, N.v36158.
  unfold R.v6, N.v6.
  rewrite ?node_15335.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36159 (s : N.State) (i : N.Inputs) :
  R.v36159 (state s) (inputs i) = Zmod.unsigned (N.v36159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36159 s i)) at 1.
  unfold R.v36159, N.v36159.
  unfold R.v6, N.v6.
  rewrite ?node_15360.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36160 (s : N.State) (i : N.Inputs) :
  R.v36160 (state s) (inputs i) = Zmod.unsigned (N.v36160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36160 s i)) at 1.
  unfold R.v36160, N.v36160.
  rewrite ?node_36157.
  rewrite ?node_36158.
  rewrite ?node_36159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36161 (s : N.State) (i : N.Inputs) :
  R.v36161 (state s) (inputs i) = Zmod.unsigned (N.v36161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36161 s i)) at 1.
  unfold R.v36161, N.v36161.
  rewrite ?node_36156.
  rewrite ?node_36160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36162 (s : N.State) (i : N.Inputs) :
  R.v36162 (state s) (inputs i) = Zmod.unsigned (N.v36162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36162 s i)) at 1.
  unfold R.v36162, N.v36162.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36163 (s : N.State) (i : N.Inputs) :
  R.v36163 (state s) (inputs i) = Zmod.unsigned (N.v36163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36163 s i)) at 1.
  unfold R.v36163, N.v36163.
  unfold R.v16463, N.v16463.
  rewrite !state_r2112_nr_5F2131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2112_nr_5F2131 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36164 (s : N.State) (i : N.Inputs) :
  R.v36164 (state s) (inputs i) = Zmod.unsigned (N.v36164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36164 s i)) at 1.
  unfold R.v36164, N.v36164.
  unfold R.v6, N.v6.
  rewrite !state_r2111_nr_5F2130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2111_nr_5F2130 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36165 (s : N.State) (i : N.Inputs) :
  R.v36165 (state s) (inputs i) = Zmod.unsigned (N.v36165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36165 s i)) at 1.
  unfold R.v36165, N.v36165.
  unfold R.v6, N.v6.
  rewrite !state_r2110_nr_5F2129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2110_nr_5F2129 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36166 (s : N.State) (i : N.Inputs) :
  R.v36166 (state s) (inputs i) = Zmod.unsigned (N.v36166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36166 s i)) at 1.
  unfold R.v36166, N.v36166.
  rewrite ?node_36164.
  rewrite ?node_36165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36167 (s : N.State) (i : N.Inputs) :
  R.v36167 (state s) (inputs i) = Zmod.unsigned (N.v36167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36167 s i)) at 1.
  unfold R.v36167, N.v36167.
  unfold R.v16484, N.v16484.
  rewrite ?node_36166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36168 (s : N.State) (i : N.Inputs) :
  R.v36168 (state s) (inputs i) = Zmod.unsigned (N.v36168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36168 s i)) at 1.
  unfold R.v36168, N.v36168.
  rewrite ?node_36163.
  rewrite ?node_36167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36169 (s : N.State) (i : N.Inputs) :
  R.v36169 (state s) (inputs i) = Zmod.unsigned (N.v36169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36169 s i)) at 1.
  unfold R.v36169, N.v36169.
  unfold R.v6, N.v6.
  rewrite ?node_36168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36170 (s : N.State) (i : N.Inputs) :
  R.v36170 (state s) (inputs i) = Zmod.unsigned (N.v36170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36170 s i)) at 1.
  unfold R.v36170, N.v36170.
  rewrite ?node_15265.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36171 (s : N.State) (i : N.Inputs) :
  R.v36171 (state s) (inputs i) = Zmod.unsigned (N.v36171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36171 s i)) at 1.
  unfold R.v36171, N.v36171.
  unfold R.v6, N.v6.
  rewrite ?node_15335.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36172 (s : N.State) (i : N.Inputs) :
  R.v36172 (state s) (inputs i) = Zmod.unsigned (N.v36172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36172 s i)) at 1.
  unfold R.v36172, N.v36172.
  rewrite ?node_36170.
  rewrite ?node_36171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36173 (s : N.State) (i : N.Inputs) :
  R.v36173 (state s) (inputs i) = Zmod.unsigned (N.v36173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36173 s i)) at 1.
  unfold R.v36173, N.v36173.
  rewrite ?node_36169.
  rewrite ?node_36172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36174 (s : N.State) (i : N.Inputs) :
  R.v36174 (state s) (inputs i) = Zmod.unsigned (N.v36174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36174 s i)) at 1.
  unfold R.v36174, N.v36174.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36175 (s : N.State) (i : N.Inputs) :
  R.v36175 (state s) (inputs i) = Zmod.unsigned (N.v36175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36175 s i)) at 1.
  unfold R.v36175, N.v36175.
  rewrite ?node_15268.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36176 (s : N.State) (i : N.Inputs) :
  R.v36176 (state s) (inputs i) = Zmod.unsigned (N.v36176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36176 s i)) at 1.
  unfold R.v36176, N.v36176.
  unfold R.v6, N.v6.
  rewrite !state_r2113_nr_5F2132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2113_nr_5F2132 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36177 (s : N.State) (i : N.Inputs) :
  R.v36177 (state s) (inputs i) = Zmod.unsigned (N.v36177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36177 s i)) at 1.
  unfold R.v36177, N.v36177.
  unfold R.v6, N.v6.
  rewrite ?node_15265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36178 (s : N.State) (i : N.Inputs) :
  R.v36178 (state s) (inputs i) = Zmod.unsigned (N.v36178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36178 s i)) at 1.
  unfold R.v36178, N.v36178.
  rewrite ?node_36176.
  rewrite ?node_36177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36179 (s : N.State) (i : N.Inputs) :
  R.v36179 (state s) (inputs i) = Zmod.unsigned (N.v36179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36179 s i)) at 1.
  unfold R.v36179, N.v36179.
  unfold R.v16484, N.v16484.
  rewrite ?node_36178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36180 (s : N.State) (i : N.Inputs) :
  R.v36180 (state s) (inputs i) = Zmod.unsigned (N.v36180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36180 s i)) at 1.
  unfold R.v36180, N.v36180.
  rewrite ?node_36175.
  rewrite ?node_36179.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36181 (s : N.State) (i : N.Inputs) :
  R.v36181 (state s) (inputs i) = Zmod.unsigned (N.v36181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36181 s i)) at 1.
  unfold R.v36181, N.v36181.
  unfold R.v6, N.v6.
  rewrite ?node_36180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36182 (s : N.State) (i : N.Inputs) :
  R.v36182 (state s) (inputs i) = Zmod.unsigned (N.v36182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36182 s i)) at 1.
  unfold R.v36182, N.v36182.
  rewrite ?node_15269.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36183 (s : N.State) (i : N.Inputs) :
  R.v36183 (state s) (inputs i) = Zmod.unsigned (N.v36183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36183 s i)) at 1.
  unfold R.v36183, N.v36183.
  unfold R.v6, N.v6.
  rewrite ?node_15360.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36184 (s : N.State) (i : N.Inputs) :
  R.v36184 (state s) (inputs i) = Zmod.unsigned (N.v36184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36184 s i)) at 1.
  unfold R.v36184, N.v36184.
  rewrite ?node_36182.
  rewrite ?node_36183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36185 (s : N.State) (i : N.Inputs) :
  R.v36185 (state s) (inputs i) = Zmod.unsigned (N.v36185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36185 s i)) at 1.
  unfold R.v36185, N.v36185.
  rewrite ?node_36181.
  rewrite ?node_36184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36186 (s : N.State) (i : N.Inputs) :
  R.v36186 (state s) (inputs i) = Zmod.unsigned (N.v36186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36186 s i)) at 1.
  unfold R.v36186, N.v36186.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36187 (s : N.State) (i : N.Inputs) :
  R.v36187 (state s) (inputs i) = Zmod.unsigned (N.v36187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36187 s i)) at 1.
  unfold R.v36187, N.v36187.
  rewrite ?node_15275.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36188 (s : N.State) (i : N.Inputs) :
  R.v36188 (state s) (inputs i) = Zmod.unsigned (N.v36188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36188 s i)) at 1.
  unfold R.v36188, N.v36188.
  unfold R.v16463, N.v16463.
  rewrite !state_r2117_nr_5F2136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2117_nr_5F2136 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36189 (s : N.State) (i : N.Inputs) :
  R.v36189 (state s) (inputs i) = Zmod.unsigned (N.v36189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36189 s i)) at 1.
  unfold R.v36189, N.v36189.
  unfold R.v16463, N.v16463.
  rewrite !state_r2116_nr_5F2135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2116_nr_5F2135 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36190 (s : N.State) (i : N.Inputs) :
  R.v36190 (state s) (inputs i) = Zmod.unsigned (N.v36190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36190 s i)) at 1.
  unfold R.v36190, N.v36190.
  unfold R.v6, N.v6.
  rewrite !state_r2115_nr_5F2134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2115_nr_5F2134 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36191 (s : N.State) (i : N.Inputs) :
  R.v36191 (state s) (inputs i) = Zmod.unsigned (N.v36191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36191 s i)) at 1.
  unfold R.v36191, N.v36191.
  unfold R.v6, N.v6.
  rewrite !state_r2114_nr_5F2133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2114_nr_5F2133 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36192 (s : N.State) (i : N.Inputs) :
  R.v36192 (state s) (inputs i) = Zmod.unsigned (N.v36192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36192 s i)) at 1.
  unfold R.v36192, N.v36192.
  rewrite ?node_36190.
  rewrite ?node_36191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36193 (s : N.State) (i : N.Inputs) :
  R.v36193 (state s) (inputs i) = Zmod.unsigned (N.v36193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36193 s i)) at 1.
  unfold R.v36193, N.v36193.
  unfold R.v16484, N.v16484.
  rewrite ?node_36192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36194 (s : N.State) (i : N.Inputs) :
  R.v36194 (state s) (inputs i) = Zmod.unsigned (N.v36194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36194 s i)) at 1.
  unfold R.v36194, N.v36194.
  rewrite ?node_36187.
  rewrite ?node_36188.
  rewrite ?node_36189.
  rewrite ?node_36193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36195 (s : N.State) (i : N.Inputs) :
  R.v36195 (state s) (inputs i) = Zmod.unsigned (N.v36195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36195 s i)) at 1.
  unfold R.v36195, N.v36195.
  unfold R.v6, N.v6.
  rewrite ?node_36194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36196 (s : N.State) (i : N.Inputs) :
  R.v36196 (state s) (inputs i) = Zmod.unsigned (N.v36196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36196 s i)) at 1.
  unfold R.v36196, N.v36196.
  rewrite ?node_15276.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36197 (s : N.State) (i : N.Inputs) :
  R.v36197 (state s) (inputs i) = Zmod.unsigned (N.v36197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36197 s i)) at 1.
  unfold R.v36197, N.v36197.
  unfold R.v6, N.v6.
  rewrite ?node_15342.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36198 (s : N.State) (i : N.Inputs) :
  R.v36198 (state s) (inputs i) = Zmod.unsigned (N.v36198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36198 s i)) at 1.
  unfold R.v36198, N.v36198.
  unfold R.v6, N.v6.
  rewrite ?node_15363.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36199 (s : N.State) (i : N.Inputs) :
  R.v36199 (state s) (inputs i) = Zmod.unsigned (N.v36199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36199 s i)) at 1.
  unfold R.v36199, N.v36199.
  rewrite ?node_36196.
  rewrite ?node_36197.
  rewrite ?node_36198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36200 (s : N.State) (i : N.Inputs) :
  R.v36200 (state s) (inputs i) = Zmod.unsigned (N.v36200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36200 s i)) at 1.
  unfold R.v36200, N.v36200.
  rewrite ?node_36195.
  rewrite ?node_36199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36201 (s : N.State) (i : N.Inputs) :
  R.v36201 (state s) (inputs i) = Zmod.unsigned (N.v36201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36201 s i)) at 1.
  unfold R.v36201, N.v36201.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36202 (s : N.State) (i : N.Inputs) :
  R.v36202 (state s) (inputs i) = Zmod.unsigned (N.v36202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36202 s i)) at 1.
  unfold R.v36202, N.v36202.
  unfold R.v16463, N.v16463.
  rewrite !state_r2116_nr_5F2135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2116_nr_5F2135 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36203 (s : N.State) (i : N.Inputs) :
  R.v36203 (state s) (inputs i) = Zmod.unsigned (N.v36203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36203 s i)) at 1.
  unfold R.v36203, N.v36203.
  unfold R.v6, N.v6.
  rewrite !state_r2115_nr_5F2134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2115_nr_5F2134 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36204 (s : N.State) (i : N.Inputs) :
  R.v36204 (state s) (inputs i) = Zmod.unsigned (N.v36204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36204 s i)) at 1.
  unfold R.v36204, N.v36204.
  unfold R.v6, N.v6.
  rewrite !state_r2114_nr_5F2133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2114_nr_5F2133 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36205 (s : N.State) (i : N.Inputs) :
  R.v36205 (state s) (inputs i) = Zmod.unsigned (N.v36205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36205 s i)) at 1.
  unfold R.v36205, N.v36205.
  rewrite ?node_36203.
  rewrite ?node_36204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36206 (s : N.State) (i : N.Inputs) :
  R.v36206 (state s) (inputs i) = Zmod.unsigned (N.v36206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36206 s i)) at 1.
  unfold R.v36206, N.v36206.
  unfold R.v16484, N.v16484.
  rewrite ?node_36205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36207 (s : N.State) (i : N.Inputs) :
  R.v36207 (state s) (inputs i) = Zmod.unsigned (N.v36207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36207 s i)) at 1.
  unfold R.v36207, N.v36207.
  rewrite ?node_36202.
  rewrite ?node_36206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36208 (s : N.State) (i : N.Inputs) :
  R.v36208 (state s) (inputs i) = Zmod.unsigned (N.v36208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36208 s i)) at 1.
  unfold R.v36208, N.v36208.
  unfold R.v6, N.v6.
  rewrite ?node_36207.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36209 (s : N.State) (i : N.Inputs) :
  R.v36209 (state s) (inputs i) = Zmod.unsigned (N.v36209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36209 s i)) at 1.
  unfold R.v36209, N.v36209.
  rewrite ?node_15271.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36210 (s : N.State) (i : N.Inputs) :
  R.v36210 (state s) (inputs i) = Zmod.unsigned (N.v36210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36210 s i)) at 1.
  unfold R.v36210, N.v36210.
  unfold R.v6, N.v6.
  rewrite ?node_15342.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36211 (s : N.State) (i : N.Inputs) :
  R.v36211 (state s) (inputs i) = Zmod.unsigned (N.v36211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36211 s i)) at 1.
  unfold R.v36211, N.v36211.
  rewrite ?node_36209.
  rewrite ?node_36210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36212 (s : N.State) (i : N.Inputs) :
  R.v36212 (state s) (inputs i) = Zmod.unsigned (N.v36212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36212 s i)) at 1.
  unfold R.v36212, N.v36212.
  rewrite ?node_36208.
  rewrite ?node_36211.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36213 (s : N.State) (i : N.Inputs) :
  R.v36213 (state s) (inputs i) = Zmod.unsigned (N.v36213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36213 s i)) at 1.
  unfold R.v36213, N.v36213.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36214 (s : N.State) (i : N.Inputs) :
  R.v36214 (state s) (inputs i) = Zmod.unsigned (N.v36214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36214 s i)) at 1.
  unfold R.v36214, N.v36214.
  rewrite ?node_15275.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36215 (s : N.State) (i : N.Inputs) :
  R.v36215 (state s) (inputs i) = Zmod.unsigned (N.v36215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36215 s i)) at 1.
  unfold R.v36215, N.v36215.
  unfold R.v6, N.v6.
  rewrite !state_r2117_nr_5F2136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2117_nr_5F2136 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36216 (s : N.State) (i : N.Inputs) :
  R.v36216 (state s) (inputs i) = Zmod.unsigned (N.v36216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36216 s i)) at 1.
  unfold R.v36216, N.v36216.
  unfold R.v6, N.v6.
  rewrite ?node_15271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36217 (s : N.State) (i : N.Inputs) :
  R.v36217 (state s) (inputs i) = Zmod.unsigned (N.v36217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36217 s i)) at 1.
  unfold R.v36217, N.v36217.
  rewrite ?node_36215.
  rewrite ?node_36216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36218 (s : N.State) (i : N.Inputs) :
  R.v36218 (state s) (inputs i) = Zmod.unsigned (N.v36218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36218 s i)) at 1.
  unfold R.v36218, N.v36218.
  unfold R.v16484, N.v16484.
  rewrite ?node_36217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36219 (s : N.State) (i : N.Inputs) :
  R.v36219 (state s) (inputs i) = Zmod.unsigned (N.v36219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36219 s i)) at 1.
  unfold R.v36219, N.v36219.
  rewrite ?node_36214.
  rewrite ?node_36218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36220 (s : N.State) (i : N.Inputs) :
  R.v36220 (state s) (inputs i) = Zmod.unsigned (N.v36220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36220 s i)) at 1.
  unfold R.v36220, N.v36220.
  unfold R.v6, N.v6.
  rewrite ?node_36219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36221 (s : N.State) (i : N.Inputs) :
  R.v36221 (state s) (inputs i) = Zmod.unsigned (N.v36221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36221 s i)) at 1.
  unfold R.v36221, N.v36221.
  rewrite ?node_15276.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36222 (s : N.State) (i : N.Inputs) :
  R.v36222 (state s) (inputs i) = Zmod.unsigned (N.v36222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36222 s i)) at 1.
  unfold R.v36222, N.v36222.
  unfold R.v6, N.v6.
  rewrite ?node_15363.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36223 (s : N.State) (i : N.Inputs) :
  R.v36223 (state s) (inputs i) = Zmod.unsigned (N.v36223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36223 s i)) at 1.
  unfold R.v36223, N.v36223.
  rewrite ?node_36221.
  rewrite ?node_36222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36224 (s : N.State) (i : N.Inputs) :
  R.v36224 (state s) (inputs i) = Zmod.unsigned (N.v36224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36224 s i)) at 1.
  unfold R.v36224, N.v36224.
  rewrite ?node_36220.
  rewrite ?node_36223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36225 (s : N.State) (i : N.Inputs) :
  R.v36225 (state s) (inputs i) = Zmod.unsigned (N.v36225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36225 s i)) at 1.
  unfold R.v36225, N.v36225.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36226 (s : N.State) (i : N.Inputs) :
  R.v36226 (state s) (inputs i) = Zmod.unsigned (N.v36226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36226 s i)) at 1.
  unfold R.v36226, N.v36226.
  rewrite ?node_15283.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36227 (s : N.State) (i : N.Inputs) :
  R.v36227 (state s) (inputs i) = Zmod.unsigned (N.v36227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36227 s i)) at 1.
  unfold R.v36227, N.v36227.
  unfold R.v16463, N.v16463.
  rewrite !state_r2121_nr_5F2140.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2121_nr_5F2140 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36228 (s : N.State) (i : N.Inputs) :
  R.v36228 (state s) (inputs i) = Zmod.unsigned (N.v36228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36228 s i)) at 1.
  unfold R.v36228, N.v36228.
  unfold R.v16463, N.v16463.
  rewrite !state_r2120_nr_5F2139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2120_nr_5F2139 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36229 (s : N.State) (i : N.Inputs) :
  R.v36229 (state s) (inputs i) = Zmod.unsigned (N.v36229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36229 s i)) at 1.
  unfold R.v36229, N.v36229.
  unfold R.v6, N.v6.
  rewrite !state_r2119_nr_5F2138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2119_nr_5F2138 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36230 (s : N.State) (i : N.Inputs) :
  R.v36230 (state s) (inputs i) = Zmod.unsigned (N.v36230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36230 s i)) at 1.
  unfold R.v36230, N.v36230.
  unfold R.v6, N.v6.
  rewrite !state_r2118_nr_5F2137.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2118_nr_5F2137 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36231 (s : N.State) (i : N.Inputs) :
  R.v36231 (state s) (inputs i) = Zmod.unsigned (N.v36231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36231 s i)) at 1.
  unfold R.v36231, N.v36231.
  rewrite ?node_36229.
  rewrite ?node_36230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36232 (s : N.State) (i : N.Inputs) :
  R.v36232 (state s) (inputs i) = Zmod.unsigned (N.v36232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36232 s i)) at 1.
  unfold R.v36232, N.v36232.
  unfold R.v16484, N.v16484.
  rewrite ?node_36231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36233 (s : N.State) (i : N.Inputs) :
  R.v36233 (state s) (inputs i) = Zmod.unsigned (N.v36233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36233 s i)) at 1.
  unfold R.v36233, N.v36233.
  rewrite ?node_36226.
  rewrite ?node_36227.
  rewrite ?node_36228.
  rewrite ?node_36232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36234 (s : N.State) (i : N.Inputs) :
  R.v36234 (state s) (inputs i) = Zmod.unsigned (N.v36234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36234 s i)) at 1.
  unfold R.v36234, N.v36234.
  unfold R.v6, N.v6.
  rewrite ?node_36233.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36235 (s : N.State) (i : N.Inputs) :
  R.v36235 (state s) (inputs i) = Zmod.unsigned (N.v36235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36235 s i)) at 1.
  unfold R.v36235, N.v36235.
  rewrite ?node_15284.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36236 (s : N.State) (i : N.Inputs) :
  R.v36236 (state s) (inputs i) = Zmod.unsigned (N.v36236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36236 s i)) at 1.
  unfold R.v36236, N.v36236.
  unfold R.v6, N.v6.
  rewrite ?node_15350.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36237 (s : N.State) (i : N.Inputs) :
  R.v36237 (state s) (inputs i) = Zmod.unsigned (N.v36237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36237 s i)) at 1.
  unfold R.v36237, N.v36237.
  unfold R.v6, N.v6.
  rewrite ?node_15367.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36238 (s : N.State) (i : N.Inputs) :
  R.v36238 (state s) (inputs i) = Zmod.unsigned (N.v36238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36238 s i)) at 1.
  unfold R.v36238, N.v36238.
  rewrite ?node_36235.
  rewrite ?node_36236.
  rewrite ?node_36237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36239 (s : N.State) (i : N.Inputs) :
  R.v36239 (state s) (inputs i) = Zmod.unsigned (N.v36239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36239 s i)) at 1.
  unfold R.v36239, N.v36239.
  rewrite ?node_36234.
  rewrite ?node_36238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36240 (s : N.State) (i : N.Inputs) :
  R.v36240 (state s) (inputs i) = Zmod.unsigned (N.v36240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36240 s i)) at 1.
  unfold R.v36240, N.v36240.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36241 (s : N.State) (i : N.Inputs) :
  R.v36241 (state s) (inputs i) = Zmod.unsigned (N.v36241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36241 s i)) at 1.
  unfold R.v36241, N.v36241.
  unfold R.v16463, N.v16463.
  rewrite !state_r2120_nr_5F2139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2120_nr_5F2139 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36242 (s : N.State) (i : N.Inputs) :
  R.v36242 (state s) (inputs i) = Zmod.unsigned (N.v36242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36242 s i)) at 1.
  unfold R.v36242, N.v36242.
  unfold R.v6, N.v6.
  rewrite !state_r2119_nr_5F2138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2119_nr_5F2138 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36243 (s : N.State) (i : N.Inputs) :
  R.v36243 (state s) (inputs i) = Zmod.unsigned (N.v36243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36243 s i)) at 1.
  unfold R.v36243, N.v36243.
  unfold R.v6, N.v6.
  rewrite !state_r2118_nr_5F2137.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2118_nr_5F2137 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36244 (s : N.State) (i : N.Inputs) :
  R.v36244 (state s) (inputs i) = Zmod.unsigned (N.v36244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36244 s i)) at 1.
  unfold R.v36244, N.v36244.
  rewrite ?node_36242.
  rewrite ?node_36243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36245 (s : N.State) (i : N.Inputs) :
  R.v36245 (state s) (inputs i) = Zmod.unsigned (N.v36245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36245 s i)) at 1.
  unfold R.v36245, N.v36245.
  unfold R.v16484, N.v16484.
  rewrite ?node_36244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36246 (s : N.State) (i : N.Inputs) :
  R.v36246 (state s) (inputs i) = Zmod.unsigned (N.v36246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36246 s i)) at 1.
  unfold R.v36246, N.v36246.
  rewrite ?node_36241.
  rewrite ?node_36245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36247 (s : N.State) (i : N.Inputs) :
  R.v36247 (state s) (inputs i) = Zmod.unsigned (N.v36247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36247 s i)) at 1.
  unfold R.v36247, N.v36247.
  unfold R.v6, N.v6.
  rewrite ?node_36246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36248 (s : N.State) (i : N.Inputs) :
  R.v36248 (state s) (inputs i) = Zmod.unsigned (N.v36248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36248 s i)) at 1.
  unfold R.v36248, N.v36248.
  rewrite ?node_15279.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36249 (s : N.State) (i : N.Inputs) :
  R.v36249 (state s) (inputs i) = Zmod.unsigned (N.v36249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36249 s i)) at 1.
  unfold R.v36249, N.v36249.
  unfold R.v6, N.v6.
  rewrite ?node_15350.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36250 (s : N.State) (i : N.Inputs) :
  R.v36250 (state s) (inputs i) = Zmod.unsigned (N.v36250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36250 s i)) at 1.
  unfold R.v36250, N.v36250.
  rewrite ?node_36248.
  rewrite ?node_36249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36251 (s : N.State) (i : N.Inputs) :
  R.v36251 (state s) (inputs i) = Zmod.unsigned (N.v36251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36251 s i)) at 1.
  unfold R.v36251, N.v36251.
  rewrite ?node_36247.
  rewrite ?node_36250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36252 (s : N.State) (i : N.Inputs) :
  R.v36252 (state s) (inputs i) = Zmod.unsigned (N.v36252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36252 s i)) at 1.
  unfold R.v36252, N.v36252.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36253 (s : N.State) (i : N.Inputs) :
  R.v36253 (state s) (inputs i) = Zmod.unsigned (N.v36253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36253 s i)) at 1.
  unfold R.v36253, N.v36253.
  rewrite ?node_15283.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36254 (s : N.State) (i : N.Inputs) :
  R.v36254 (state s) (inputs i) = Zmod.unsigned (N.v36254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36254 s i)) at 1.
  unfold R.v36254, N.v36254.
  unfold R.v6, N.v6.
  rewrite !state_r2121_nr_5F2140.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2121_nr_5F2140 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36255 (s : N.State) (i : N.Inputs) :
  R.v36255 (state s) (inputs i) = Zmod.unsigned (N.v36255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36255 s i)) at 1.
  unfold R.v36255, N.v36255.
  unfold R.v6, N.v6.
  rewrite ?node_15279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36256 (s : N.State) (i : N.Inputs) :
  R.v36256 (state s) (inputs i) = Zmod.unsigned (N.v36256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36256 s i)) at 1.
  unfold R.v36256, N.v36256.
  rewrite ?node_36254.
  rewrite ?node_36255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36257 (s : N.State) (i : N.Inputs) :
  R.v36257 (state s) (inputs i) = Zmod.unsigned (N.v36257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36257 s i)) at 1.
  unfold R.v36257, N.v36257.
  unfold R.v16484, N.v16484.
  rewrite ?node_36256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36258 (s : N.State) (i : N.Inputs) :
  R.v36258 (state s) (inputs i) = Zmod.unsigned (N.v36258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36258 s i)) at 1.
  unfold R.v36258, N.v36258.
  rewrite ?node_36253.
  rewrite ?node_36257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36259 (s : N.State) (i : N.Inputs) :
  R.v36259 (state s) (inputs i) = Zmod.unsigned (N.v36259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36259 s i)) at 1.
  unfold R.v36259, N.v36259.
  unfold R.v6, N.v6.
  rewrite ?node_36258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36260 (s : N.State) (i : N.Inputs) :
  R.v36260 (state s) (inputs i) = Zmod.unsigned (N.v36260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36260 s i)) at 1.
  unfold R.v36260, N.v36260.
  rewrite ?node_15284.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36261 (s : N.State) (i : N.Inputs) :
  R.v36261 (state s) (inputs i) = Zmod.unsigned (N.v36261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36261 s i)) at 1.
  unfold R.v36261, N.v36261.
  unfold R.v6, N.v6.
  rewrite ?node_15367.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36262 (s : N.State) (i : N.Inputs) :
  R.v36262 (state s) (inputs i) = Zmod.unsigned (N.v36262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36262 s i)) at 1.
  unfold R.v36262, N.v36262.
  rewrite ?node_36260.
  rewrite ?node_36261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36263 (s : N.State) (i : N.Inputs) :
  R.v36263 (state s) (inputs i) = Zmod.unsigned (N.v36263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36263 s i)) at 1.
  unfold R.v36263, N.v36263.
  rewrite ?node_36259.
  rewrite ?node_36262.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36264 (s : N.State) (i : N.Inputs) :
  R.v36264 (state s) (inputs i) = Zmod.unsigned (N.v36264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36264 s i)) at 1.
  unfold R.v36264, N.v36264.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36265 (s : N.State) (i : N.Inputs) :
  R.v36265 (state s) (inputs i) = Zmod.unsigned (N.v36265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36265 s i)) at 1.
  unfold R.v36265, N.v36265.
  rewrite ?node_15335.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36266 (s : N.State) (i : N.Inputs) :
  R.v36266 (state s) (inputs i) = Zmod.unsigned (N.v36266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36266 s i)) at 1.
  unfold R.v36266, N.v36266.
  unfold R.v16463, N.v16463.
  rewrite !state_r2125_nr_5F2145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2125_nr_5F2145 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36267 (s : N.State) (i : N.Inputs) :
  R.v36267 (state s) (inputs i) = Zmod.unsigned (N.v36267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36267 s i)) at 1.
  unfold R.v36267, N.v36267.
  unfold R.v16463, N.v16463.
  rewrite !state_r2124_nr_5F2144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2124_nr_5F2144 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36268 (s : N.State) (i : N.Inputs) :
  R.v36268 (state s) (inputs i) = Zmod.unsigned (N.v36268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36268 s i)) at 1.
  unfold R.v36268, N.v36268.
  unfold R.v6, N.v6.
  rewrite !state_r2123_nr_5F2143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2123_nr_5F2143 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36269 (s : N.State) (i : N.Inputs) :
  R.v36269 (state s) (inputs i) = Zmod.unsigned (N.v36269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36269 s i)) at 1.
  unfold R.v36269, N.v36269.
  unfold R.v19, N.v19.
  rewrite ?node_36268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36270 (s : N.State) (i : N.Inputs) :
  R.v36270 (state s) (inputs i) = Zmod.unsigned (N.v36270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36270 s i)) at 1.
  unfold R.v36270, N.v36270.
  unfold R.v16484, N.v16484.
  rewrite ?node_36269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36271 (s : N.State) (i : N.Inputs) :
  R.v36271 (state s) (inputs i) = Zmod.unsigned (N.v36271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36271 s i)) at 1.
  unfold R.v36271, N.v36271.
  rewrite ?node_36265.
  rewrite ?node_36266.
  rewrite ?node_36267.
  rewrite ?node_36270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36272 (s : N.State) (i : N.Inputs) :
  R.v36272 (state s) (inputs i) = Zmod.unsigned (N.v36272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36272 s i)) at 1.
  unfold R.v36272, N.v36272.
  unfold R.v6, N.v6.
  rewrite ?node_36271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36273 (s : N.State) (i : N.Inputs) :
  R.v36273 (state s) (inputs i) = Zmod.unsigned (N.v36273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36273 s i)) at 1.
  unfold R.v36273, N.v36273.
  rewrite ?node_15336.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36274 (s : N.State) (i : N.Inputs) :
  R.v36274 (state s) (inputs i) = Zmod.unsigned (N.v36274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36274 s i)) at 1.
  unfold R.v36274, N.v36274.
  unfold R.v6, N.v6.
  rewrite ?node_15399.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36275 (s : N.State) (i : N.Inputs) :
  R.v36275 (state s) (inputs i) = Zmod.unsigned (N.v36275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36275 s i)) at 1.
  unfold R.v36275, N.v36275.
  unfold R.v6, N.v6.
  rewrite ?node_15419.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36276 (s : N.State) (i : N.Inputs) :
  R.v36276 (state s) (inputs i) = Zmod.unsigned (N.v36276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36276 s i)) at 1.
  unfold R.v36276, N.v36276.
  rewrite ?node_36273.
  rewrite ?node_36274.
  rewrite ?node_36275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36277 (s : N.State) (i : N.Inputs) :
  R.v36277 (state s) (inputs i) = Zmod.unsigned (N.v36277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36277 s i)) at 1.
  unfold R.v36277, N.v36277.
  rewrite ?node_36272.
  rewrite ?node_36276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36278 (s : N.State) (i : N.Inputs) :
  R.v36278 (state s) (inputs i) = Zmod.unsigned (N.v36278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36278 s i)) at 1.
  unfold R.v36278, N.v36278.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36279 (s : N.State) (i : N.Inputs) :
  R.v36279 (state s) (inputs i) = Zmod.unsigned (N.v36279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36279 s i)) at 1.
  unfold R.v36279, N.v36279.
  unfold R.v16463, N.v16463.
  rewrite !state_r2124_nr_5F2144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2124_nr_5F2144 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36280 (s : N.State) (i : N.Inputs) :
  R.v36280 (state s) (inputs i) = Zmod.unsigned (N.v36280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36280 s i)) at 1.
  unfold R.v36280, N.v36280.
  unfold R.v6, N.v6.
  rewrite !state_r2123_nr_5F2143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2123_nr_5F2143 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36281 (s : N.State) (i : N.Inputs) :
  R.v36281 (state s) (inputs i) = Zmod.unsigned (N.v36281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36281 s i)) at 1.
  unfold R.v36281, N.v36281.
  unfold R.v19, N.v19.
  rewrite ?node_36280.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36282 (s : N.State) (i : N.Inputs) :
  R.v36282 (state s) (inputs i) = Zmod.unsigned (N.v36282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36282 s i)) at 1.
  unfold R.v36282, N.v36282.
  unfold R.v16484, N.v16484.
  rewrite ?node_36281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36283 (s : N.State) (i : N.Inputs) :
  R.v36283 (state s) (inputs i) = Zmod.unsigned (N.v36283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36283 s i)) at 1.
  unfold R.v36283, N.v36283.
  rewrite ?node_36279.
  rewrite ?node_36282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36284 (s : N.State) (i : N.Inputs) :
  R.v36284 (state s) (inputs i) = Zmod.unsigned (N.v36284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36284 s i)) at 1.
  unfold R.v36284, N.v36284.
  unfold R.v6, N.v6.
  rewrite ?node_36283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36285 (s : N.State) (i : N.Inputs) :
  R.v36285 (state s) (inputs i) = Zmod.unsigned (N.v36285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36285 s i)) at 1.
  unfold R.v36285, N.v36285.
  rewrite ?node_15331.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36286 (s : N.State) (i : N.Inputs) :
  R.v36286 (state s) (inputs i) = Zmod.unsigned (N.v36286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36286 s i)) at 1.
  unfold R.v36286, N.v36286.
  unfold R.v6, N.v6.
  rewrite ?node_15399.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36287 (s : N.State) (i : N.Inputs) :
  R.v36287 (state s) (inputs i) = Zmod.unsigned (N.v36287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36287 s i)) at 1.
  unfold R.v36287, N.v36287.
  rewrite ?node_36285.
  rewrite ?node_36286.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36288 (s : N.State) (i : N.Inputs) :
  R.v36288 (state s) (inputs i) = Zmod.unsigned (N.v36288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36288 s i)) at 1.
  unfold R.v36288, N.v36288.
  rewrite ?node_36284.
  rewrite ?node_36287.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36289 (s : N.State) (i : N.Inputs) :
  R.v36289 (state s) (inputs i) = Zmod.unsigned (N.v36289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36289 s i)) at 1.
  unfold R.v36289, N.v36289.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36290 (s : N.State) (i : N.Inputs) :
  R.v36290 (state s) (inputs i) = Zmod.unsigned (N.v36290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36290 s i)) at 1.
  unfold R.v36290, N.v36290.
  rewrite ?node_15335.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36291 (s : N.State) (i : N.Inputs) :
  R.v36291 (state s) (inputs i) = Zmod.unsigned (N.v36291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36291 s i)) at 1.
  unfold R.v36291, N.v36291.
  unfold R.v6, N.v6.
  rewrite !state_r2125_nr_5F2145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2125_nr_5F2145 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36292 (s : N.State) (i : N.Inputs) :
  R.v36292 (state s) (inputs i) = Zmod.unsigned (N.v36292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36292 s i)) at 1.
  unfold R.v36292, N.v36292.
  unfold R.v6, N.v6.
  rewrite ?node_15331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36293 (s : N.State) (i : N.Inputs) :
  R.v36293 (state s) (inputs i) = Zmod.unsigned (N.v36293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36293 s i)) at 1.
  unfold R.v36293, N.v36293.
  rewrite ?node_36291.
  rewrite ?node_36292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36294 (s : N.State) (i : N.Inputs) :
  R.v36294 (state s) (inputs i) = Zmod.unsigned (N.v36294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36294 s i)) at 1.
  unfold R.v36294, N.v36294.
  unfold R.v16484, N.v16484.
  rewrite ?node_36293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36295 (s : N.State) (i : N.Inputs) :
  R.v36295 (state s) (inputs i) = Zmod.unsigned (N.v36295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36295 s i)) at 1.
  unfold R.v36295, N.v36295.
  rewrite ?node_36290.
  rewrite ?node_36294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36296 (s : N.State) (i : N.Inputs) :
  R.v36296 (state s) (inputs i) = Zmod.unsigned (N.v36296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36296 s i)) at 1.
  unfold R.v36296, N.v36296.
  unfold R.v6, N.v6.
  rewrite ?node_36295.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36297 (s : N.State) (i : N.Inputs) :
  R.v36297 (state s) (inputs i) = Zmod.unsigned (N.v36297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36297 s i)) at 1.
  unfold R.v36297, N.v36297.
  rewrite ?node_15336.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36298 (s : N.State) (i : N.Inputs) :
  R.v36298 (state s) (inputs i) = Zmod.unsigned (N.v36298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36298 s i)) at 1.
  unfold R.v36298, N.v36298.
  unfold R.v6, N.v6.
  rewrite ?node_15419.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36299 (s : N.State) (i : N.Inputs) :
  R.v36299 (state s) (inputs i) = Zmod.unsigned (N.v36299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36299 s i)) at 1.
  unfold R.v36299, N.v36299.
  rewrite ?node_36297.
  rewrite ?node_36298.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36300 (s : N.State) (i : N.Inputs) :
  R.v36300 (state s) (inputs i) = Zmod.unsigned (N.v36300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36300 s i)) at 1.
  unfold R.v36300, N.v36300.
  rewrite ?node_36296.
  rewrite ?node_36299.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36301 (s : N.State) (i : N.Inputs) :
  R.v36301 (state s) (inputs i) = Zmod.unsigned (N.v36301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36301 s i)) at 1.
  unfold R.v36301, N.v36301.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36302 (s : N.State) (i : N.Inputs) :
  R.v36302 (state s) (inputs i) = Zmod.unsigned (N.v36302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36302 s i)) at 1.
  unfold R.v36302, N.v36302.
  rewrite ?node_15342.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36303 (s : N.State) (i : N.Inputs) :
  R.v36303 (state s) (inputs i) = Zmod.unsigned (N.v36303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36303 s i)) at 1.
  unfold R.v36303, N.v36303.
  unfold R.v16463, N.v16463.
  rewrite !state_r2129_nr_5F2149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2129_nr_5F2149 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36304 (s : N.State) (i : N.Inputs) :
  R.v36304 (state s) (inputs i) = Zmod.unsigned (N.v36304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36304 s i)) at 1.
  unfold R.v36304, N.v36304.
  unfold R.v16463, N.v16463.
  rewrite !state_r2128_nr_5F2148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2128_nr_5F2148 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36305 (s : N.State) (i : N.Inputs) :
  R.v36305 (state s) (inputs i) = Zmod.unsigned (N.v36305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36305 s i)) at 1.
  unfold R.v36305, N.v36305.
  unfold R.v6, N.v6.
  rewrite !state_r2127_nr_5F2147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2127_nr_5F2147 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36306 (s : N.State) (i : N.Inputs) :
  R.v36306 (state s) (inputs i) = Zmod.unsigned (N.v36306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36306 s i)) at 1.
  unfold R.v36306, N.v36306.
  unfold R.v6, N.v6.
  rewrite !state_r2126_nr_5F2146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2126_nr_5F2146 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36307 (s : N.State) (i : N.Inputs) :
  R.v36307 (state s) (inputs i) = Zmod.unsigned (N.v36307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36307 s i)) at 1.
  unfold R.v36307, N.v36307.
  rewrite ?node_36305.
  rewrite ?node_36306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36308 (s : N.State) (i : N.Inputs) :
  R.v36308 (state s) (inputs i) = Zmod.unsigned (N.v36308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36308 s i)) at 1.
  unfold R.v36308, N.v36308.
  unfold R.v16484, N.v16484.
  rewrite ?node_36307.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36309 (s : N.State) (i : N.Inputs) :
  R.v36309 (state s) (inputs i) = Zmod.unsigned (N.v36309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36309 s i)) at 1.
  unfold R.v36309, N.v36309.
  rewrite ?node_36302.
  rewrite ?node_36303.
  rewrite ?node_36304.
  rewrite ?node_36308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36310 (s : N.State) (i : N.Inputs) :
  R.v36310 (state s) (inputs i) = Zmod.unsigned (N.v36310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36310 s i)) at 1.
  unfold R.v36310, N.v36310.
  unfold R.v6, N.v6.
  rewrite ?node_36309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36311 (s : N.State) (i : N.Inputs) :
  R.v36311 (state s) (inputs i) = Zmod.unsigned (N.v36311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36311 s i)) at 1.
  unfold R.v36311, N.v36311.
  rewrite ?node_15343.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36312 (s : N.State) (i : N.Inputs) :
  R.v36312 (state s) (inputs i) = Zmod.unsigned (N.v36312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36312 s i)) at 1.
  unfold R.v36312, N.v36312.
  unfold R.v6, N.v6.
  rewrite ?node_15406.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36313 (s : N.State) (i : N.Inputs) :
  R.v36313 (state s) (inputs i) = Zmod.unsigned (N.v36313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36313 s i)) at 1.
  unfold R.v36313, N.v36313.
  unfold R.v6, N.v6.
  rewrite ?node_15427.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36314 (s : N.State) (i : N.Inputs) :
  R.v36314 (state s) (inputs i) = Zmod.unsigned (N.v36314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36314 s i)) at 1.
  unfold R.v36314, N.v36314.
  rewrite ?node_36311.
  rewrite ?node_36312.
  rewrite ?node_36313.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36315 (s : N.State) (i : N.Inputs) :
  R.v36315 (state s) (inputs i) = Zmod.unsigned (N.v36315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36315 s i)) at 1.
  unfold R.v36315, N.v36315.
  rewrite ?node_36310.
  rewrite ?node_36314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36316 (s : N.State) (i : N.Inputs) :
  R.v36316 (state s) (inputs i) = Zmod.unsigned (N.v36316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36316 s i)) at 1.
  unfold R.v36316, N.v36316.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36317 (s : N.State) (i : N.Inputs) :
  R.v36317 (state s) (inputs i) = Zmod.unsigned (N.v36317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36317 s i)) at 1.
  unfold R.v36317, N.v36317.
  unfold R.v16463, N.v16463.
  rewrite !state_r2128_nr_5F2148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2128_nr_5F2148 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36318 (s : N.State) (i : N.Inputs) :
  R.v36318 (state s) (inputs i) = Zmod.unsigned (N.v36318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36318 s i)) at 1.
  unfold R.v36318, N.v36318.
  unfold R.v6, N.v6.
  rewrite !state_r2127_nr_5F2147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2127_nr_5F2147 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36319 (s : N.State) (i : N.Inputs) :
  R.v36319 (state s) (inputs i) = Zmod.unsigned (N.v36319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36319 s i)) at 1.
  unfold R.v36319, N.v36319.
  unfold R.v6, N.v6.
  rewrite !state_r2126_nr_5F2146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2126_nr_5F2146 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36320 (s : N.State) (i : N.Inputs) :
  R.v36320 (state s) (inputs i) = Zmod.unsigned (N.v36320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36320 s i)) at 1.
  unfold R.v36320, N.v36320.
  rewrite ?node_36318.
  rewrite ?node_36319.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36321 (s : N.State) (i : N.Inputs) :
  R.v36321 (state s) (inputs i) = Zmod.unsigned (N.v36321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36321 s i)) at 1.
  unfold R.v36321, N.v36321.
  unfold R.v16484, N.v16484.
  rewrite ?node_36320.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36322 (s : N.State) (i : N.Inputs) :
  R.v36322 (state s) (inputs i) = Zmod.unsigned (N.v36322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36322 s i)) at 1.
  unfold R.v36322, N.v36322.
  rewrite ?node_36317.
  rewrite ?node_36321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36323 (s : N.State) (i : N.Inputs) :
  R.v36323 (state s) (inputs i) = Zmod.unsigned (N.v36323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36323 s i)) at 1.
  unfold R.v36323, N.v36323.
  unfold R.v6, N.v6.
  rewrite ?node_36322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36324 (s : N.State) (i : N.Inputs) :
  R.v36324 (state s) (inputs i) = Zmod.unsigned (N.v36324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36324 s i)) at 1.
  unfold R.v36324, N.v36324.
  rewrite ?node_15338.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36325 (s : N.State) (i : N.Inputs) :
  R.v36325 (state s) (inputs i) = Zmod.unsigned (N.v36325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36325 s i)) at 1.
  unfold R.v36325, N.v36325.
  unfold R.v6, N.v6.
  rewrite ?node_15406.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36326 (s : N.State) (i : N.Inputs) :
  R.v36326 (state s) (inputs i) = Zmod.unsigned (N.v36326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36326 s i)) at 1.
  unfold R.v36326, N.v36326.
  rewrite ?node_36324.
  rewrite ?node_36325.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36327 (s : N.State) (i : N.Inputs) :
  R.v36327 (state s) (inputs i) = Zmod.unsigned (N.v36327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36327 s i)) at 1.
  unfold R.v36327, N.v36327.
  rewrite ?node_36323.
  rewrite ?node_36326.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36328 (s : N.State) (i : N.Inputs) :
  R.v36328 (state s) (inputs i) = Zmod.unsigned (N.v36328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36328 s i)) at 1.
  unfold R.v36328, N.v36328.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36329 (s : N.State) (i : N.Inputs) :
  R.v36329 (state s) (inputs i) = Zmod.unsigned (N.v36329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36329 s i)) at 1.
  unfold R.v36329, N.v36329.
  rewrite ?node_15342.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36330 (s : N.State) (i : N.Inputs) :
  R.v36330 (state s) (inputs i) = Zmod.unsigned (N.v36330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36330 s i)) at 1.
  unfold R.v36330, N.v36330.
  unfold R.v6, N.v6.
  rewrite !state_r2129_nr_5F2149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2129_nr_5F2149 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36331 (s : N.State) (i : N.Inputs) :
  R.v36331 (state s) (inputs i) = Zmod.unsigned (N.v36331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36331 s i)) at 1.
  unfold R.v36331, N.v36331.
  unfold R.v6, N.v6.
  rewrite ?node_15338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36332 (s : N.State) (i : N.Inputs) :
  R.v36332 (state s) (inputs i) = Zmod.unsigned (N.v36332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36332 s i)) at 1.
  unfold R.v36332, N.v36332.
  rewrite ?node_36330.
  rewrite ?node_36331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36333 (s : N.State) (i : N.Inputs) :
  R.v36333 (state s) (inputs i) = Zmod.unsigned (N.v36333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36333 s i)) at 1.
  unfold R.v36333, N.v36333.
  unfold R.v16484, N.v16484.
  rewrite ?node_36332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36334 (s : N.State) (i : N.Inputs) :
  R.v36334 (state s) (inputs i) = Zmod.unsigned (N.v36334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36334 s i)) at 1.
  unfold R.v36334, N.v36334.
  rewrite ?node_36329.
  rewrite ?node_36333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36335 (s : N.State) (i : N.Inputs) :
  R.v36335 (state s) (inputs i) = Zmod.unsigned (N.v36335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36335 s i)) at 1.
  unfold R.v36335, N.v36335.
  unfold R.v6, N.v6.
  rewrite ?node_36334.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36336 (s : N.State) (i : N.Inputs) :
  R.v36336 (state s) (inputs i) = Zmod.unsigned (N.v36336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36336 s i)) at 1.
  unfold R.v36336, N.v36336.
  rewrite ?node_15343.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36337 (s : N.State) (i : N.Inputs) :
  R.v36337 (state s) (inputs i) = Zmod.unsigned (N.v36337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36337 s i)) at 1.
  unfold R.v36337, N.v36337.
  unfold R.v6, N.v6.
  rewrite ?node_15427.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36338 (s : N.State) (i : N.Inputs) :
  R.v36338 (state s) (inputs i) = Zmod.unsigned (N.v36338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36338 s i)) at 1.
  unfold R.v36338, N.v36338.
  rewrite ?node_36336.
  rewrite ?node_36337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36339 (s : N.State) (i : N.Inputs) :
  R.v36339 (state s) (inputs i) = Zmod.unsigned (N.v36339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36339 s i)) at 1.
  unfold R.v36339, N.v36339.
  rewrite ?node_36335.
  rewrite ?node_36338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36340 (s : N.State) (i : N.Inputs) :
  R.v36340 (state s) (inputs i) = Zmod.unsigned (N.v36340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36340 s i)) at 1.
  unfold R.v36340, N.v36340.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36341 (s : N.State) (i : N.Inputs) :
  R.v36341 (state s) (inputs i) = Zmod.unsigned (N.v36341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36341 s i)) at 1.
  unfold R.v36341, N.v36341.
  rewrite ?node_15350.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36342 (s : N.State) (i : N.Inputs) :
  R.v36342 (state s) (inputs i) = Zmod.unsigned (N.v36342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36342 s i)) at 1.
  unfold R.v36342, N.v36342.
  unfold R.v16463, N.v16463.
  rewrite !state_r2133_nr_5F2153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2133_nr_5F2153 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36343 (s : N.State) (i : N.Inputs) :
  R.v36343 (state s) (inputs i) = Zmod.unsigned (N.v36343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36343 s i)) at 1.
  unfold R.v36343, N.v36343.
  unfold R.v16463, N.v16463.
  rewrite !state_r2132_nr_5F2152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2132_nr_5F2152 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36344 (s : N.State) (i : N.Inputs) :
  R.v36344 (state s) (inputs i) = Zmod.unsigned (N.v36344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36344 s i)) at 1.
  unfold R.v36344, N.v36344.
  unfold R.v6, N.v6.
  rewrite !state_r2131_nr_5F2151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2131_nr_5F2151 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36345 (s : N.State) (i : N.Inputs) :
  R.v36345 (state s) (inputs i) = Zmod.unsigned (N.v36345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36345 s i)) at 1.
  unfold R.v36345, N.v36345.
  unfold R.v6, N.v6.
  rewrite !state_r2130_nr_5F2150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2130_nr_5F2150 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36346 (s : N.State) (i : N.Inputs) :
  R.v36346 (state s) (inputs i) = Zmod.unsigned (N.v36346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36346 s i)) at 1.
  unfold R.v36346, N.v36346.
  rewrite ?node_36344.
  rewrite ?node_36345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36347 (s : N.State) (i : N.Inputs) :
  R.v36347 (state s) (inputs i) = Zmod.unsigned (N.v36347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36347 s i)) at 1.
  unfold R.v36347, N.v36347.
  unfold R.v16484, N.v16484.
  rewrite ?node_36346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36348 (s : N.State) (i : N.Inputs) :
  R.v36348 (state s) (inputs i) = Zmod.unsigned (N.v36348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36348 s i)) at 1.
  unfold R.v36348, N.v36348.
  rewrite ?node_36341.
  rewrite ?node_36342.
  rewrite ?node_36343.
  rewrite ?node_36347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36349 (s : N.State) (i : N.Inputs) :
  R.v36349 (state s) (inputs i) = Zmod.unsigned (N.v36349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36349 s i)) at 1.
  unfold R.v36349, N.v36349.
  unfold R.v6, N.v6.
  rewrite ?node_36348.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36350 (s : N.State) (i : N.Inputs) :
  R.v36350 (state s) (inputs i) = Zmod.unsigned (N.v36350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36350 s i)) at 1.
  unfold R.v36350, N.v36350.
  rewrite ?node_15351.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36351 (s : N.State) (i : N.Inputs) :
  R.v36351 (state s) (inputs i) = Zmod.unsigned (N.v36351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36351 s i)) at 1.
  unfold R.v36351, N.v36351.
  unfold R.v6, N.v6.
  rewrite ?node_15414.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36352 (s : N.State) (i : N.Inputs) :
  R.v36352 (state s) (inputs i) = Zmod.unsigned (N.v36352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36352 s i)) at 1.
  unfold R.v36352, N.v36352.
  unfold R.v6, N.v6.
  rewrite ?node_15430.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36353 (s : N.State) (i : N.Inputs) :
  R.v36353 (state s) (inputs i) = Zmod.unsigned (N.v36353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36353 s i)) at 1.
  unfold R.v36353, N.v36353.
  rewrite ?node_36350.
  rewrite ?node_36351.
  rewrite ?node_36352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36354 (s : N.State) (i : N.Inputs) :
  R.v36354 (state s) (inputs i) = Zmod.unsigned (N.v36354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36354 s i)) at 1.
  unfold R.v36354, N.v36354.
  rewrite ?node_36349.
  rewrite ?node_36353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36355 (s : N.State) (i : N.Inputs) :
  R.v36355 (state s) (inputs i) = Zmod.unsigned (N.v36355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36355 s i)) at 1.
  unfold R.v36355, N.v36355.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36356 (s : N.State) (i : N.Inputs) :
  R.v36356 (state s) (inputs i) = Zmod.unsigned (N.v36356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36356 s i)) at 1.
  unfold R.v36356, N.v36356.
  unfold R.v16463, N.v16463.
  rewrite !state_r2132_nr_5F2152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2132_nr_5F2152 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36357 (s : N.State) (i : N.Inputs) :
  R.v36357 (state s) (inputs i) = Zmod.unsigned (N.v36357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36357 s i)) at 1.
  unfold R.v36357, N.v36357.
  unfold R.v6, N.v6.
  rewrite !state_r2131_nr_5F2151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2131_nr_5F2151 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36358 (s : N.State) (i : N.Inputs) :
  R.v36358 (state s) (inputs i) = Zmod.unsigned (N.v36358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36358 s i)) at 1.
  unfold R.v36358, N.v36358.
  unfold R.v6, N.v6.
  rewrite !state_r2130_nr_5F2150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2130_nr_5F2150 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36359 (s : N.State) (i : N.Inputs) :
  R.v36359 (state s) (inputs i) = Zmod.unsigned (N.v36359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36359 s i)) at 1.
  unfold R.v36359, N.v36359.
  rewrite ?node_36357.
  rewrite ?node_36358.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36360 (s : N.State) (i : N.Inputs) :
  R.v36360 (state s) (inputs i) = Zmod.unsigned (N.v36360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36360 s i)) at 1.
  unfold R.v36360, N.v36360.
  unfold R.v16484, N.v16484.
  rewrite ?node_36359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36361 (s : N.State) (i : N.Inputs) :
  R.v36361 (state s) (inputs i) = Zmod.unsigned (N.v36361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36361 s i)) at 1.
  unfold R.v36361, N.v36361.
  rewrite ?node_36356.
  rewrite ?node_36360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36362 (s : N.State) (i : N.Inputs) :
  R.v36362 (state s) (inputs i) = Zmod.unsigned (N.v36362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36362 s i)) at 1.
  unfold R.v36362, N.v36362.
  unfold R.v6, N.v6.
  rewrite ?node_36361.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36363 (s : N.State) (i : N.Inputs) :
  R.v36363 (state s) (inputs i) = Zmod.unsigned (N.v36363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36363 s i)) at 1.
  unfold R.v36363, N.v36363.
  rewrite ?node_15346.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36364 (s : N.State) (i : N.Inputs) :
  R.v36364 (state s) (inputs i) = Zmod.unsigned (N.v36364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36364 s i)) at 1.
  unfold R.v36364, N.v36364.
  unfold R.v6, N.v6.
  rewrite ?node_15414.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36365 (s : N.State) (i : N.Inputs) :
  R.v36365 (state s) (inputs i) = Zmod.unsigned (N.v36365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36365 s i)) at 1.
  unfold R.v36365, N.v36365.
  rewrite ?node_36363.
  rewrite ?node_36364.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36366 (s : N.State) (i : N.Inputs) :
  R.v36366 (state s) (inputs i) = Zmod.unsigned (N.v36366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36366 s i)) at 1.
  unfold R.v36366, N.v36366.
  rewrite ?node_36362.
  rewrite ?node_36365.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36367 (s : N.State) (i : N.Inputs) :
  R.v36367 (state s) (inputs i) = Zmod.unsigned (N.v36367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36367 s i)) at 1.
  unfold R.v36367, N.v36367.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36368 (s : N.State) (i : N.Inputs) :
  R.v36368 (state s) (inputs i) = Zmod.unsigned (N.v36368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36368 s i)) at 1.
  unfold R.v36368, N.v36368.
  rewrite ?node_15350.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36369 (s : N.State) (i : N.Inputs) :
  R.v36369 (state s) (inputs i) = Zmod.unsigned (N.v36369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36369 s i)) at 1.
  unfold R.v36369, N.v36369.
  unfold R.v6, N.v6.
  rewrite !state_r2133_nr_5F2153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2133_nr_5F2153 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36370 (s : N.State) (i : N.Inputs) :
  R.v36370 (state s) (inputs i) = Zmod.unsigned (N.v36370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36370 s i)) at 1.
  unfold R.v36370, N.v36370.
  unfold R.v6, N.v6.
  rewrite ?node_15346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36371 (s : N.State) (i : N.Inputs) :
  R.v36371 (state s) (inputs i) = Zmod.unsigned (N.v36371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36371 s i)) at 1.
  unfold R.v36371, N.v36371.
  rewrite ?node_36369.
  rewrite ?node_36370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36372 (s : N.State) (i : N.Inputs) :
  R.v36372 (state s) (inputs i) = Zmod.unsigned (N.v36372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36372 s i)) at 1.
  unfold R.v36372, N.v36372.
  unfold R.v16484, N.v16484.
  rewrite ?node_36371.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36373 (s : N.State) (i : N.Inputs) :
  R.v36373 (state s) (inputs i) = Zmod.unsigned (N.v36373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36373 s i)) at 1.
  unfold R.v36373, N.v36373.
  rewrite ?node_36368.
  rewrite ?node_36372.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36374 (s : N.State) (i : N.Inputs) :
  R.v36374 (state s) (inputs i) = Zmod.unsigned (N.v36374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36374 s i)) at 1.
  unfold R.v36374, N.v36374.
  unfold R.v6, N.v6.
  rewrite ?node_36373.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36375 (s : N.State) (i : N.Inputs) :
  R.v36375 (state s) (inputs i) = Zmod.unsigned (N.v36375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36375 s i)) at 1.
  unfold R.v36375, N.v36375.
  rewrite ?node_15351.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36376 (s : N.State) (i : N.Inputs) :
  R.v36376 (state s) (inputs i) = Zmod.unsigned (N.v36376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36376 s i)) at 1.
  unfold R.v36376, N.v36376.
  unfold R.v6, N.v6.
  rewrite ?node_15430.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36377 (s : N.State) (i : N.Inputs) :
  R.v36377 (state s) (inputs i) = Zmod.unsigned (N.v36377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36377 s i)) at 1.
  unfold R.v36377, N.v36377.
  rewrite ?node_36375.
  rewrite ?node_36376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36378 (s : N.State) (i : N.Inputs) :
  R.v36378 (state s) (inputs i) = Zmod.unsigned (N.v36378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36378 s i)) at 1.
  unfold R.v36378, N.v36378.
  rewrite ?node_36374.
  rewrite ?node_36377.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36379 (s : N.State) (i : N.Inputs) :
  R.v36379 (state s) (inputs i) = Zmod.unsigned (N.v36379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36379 s i)) at 1.
  unfold R.v36379, N.v36379.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36380 (s : N.State) (i : N.Inputs) :
  R.v36380 (state s) (inputs i) = Zmod.unsigned (N.v36380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36380 s i)) at 1.
  unfold R.v36380, N.v36380.
  rewrite ?node_15399.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36381 (s : N.State) (i : N.Inputs) :
  R.v36381 (state s) (inputs i) = Zmod.unsigned (N.v36381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36381 s i)) at 1.
  unfold R.v36381, N.v36381.
  unfold R.v16463, N.v16463.
  rewrite !state_r2138_nr_5F2158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2138_nr_5F2158 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36382 (s : N.State) (i : N.Inputs) :
  R.v36382 (state s) (inputs i) = Zmod.unsigned (N.v36382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36382 s i)) at 1.
  unfold R.v36382, N.v36382.
  unfold R.v16463, N.v16463.
  rewrite !state_r2137_nr_5F2157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2137_nr_5F2157 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36383 (s : N.State) (i : N.Inputs) :
  R.v36383 (state s) (inputs i) = Zmod.unsigned (N.v36383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36383 s i)) at 1.
  unfold R.v36383, N.v36383.
  unfold R.v6, N.v6.
  rewrite !state_r2136_nr_5F2156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2136_nr_5F2156 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36384 (s : N.State) (i : N.Inputs) :
  R.v36384 (state s) (inputs i) = Zmod.unsigned (N.v36384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36384 s i)) at 1.
  unfold R.v36384, N.v36384.
  unfold R.v6, N.v6.
  rewrite !state_r2135_nr_5F2155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2135_nr_5F2155 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36385 (s : N.State) (i : N.Inputs) :
  R.v36385 (state s) (inputs i) = Zmod.unsigned (N.v36385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36385 s i)) at 1.
  unfold R.v36385, N.v36385.
  rewrite ?node_36383.
  rewrite ?node_36384.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36386 (s : N.State) (i : N.Inputs) :
  R.v36386 (state s) (inputs i) = Zmod.unsigned (N.v36386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36386 s i)) at 1.
  unfold R.v36386, N.v36386.
  unfold R.v16484, N.v16484.
  rewrite ?node_36385.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36387 (s : N.State) (i : N.Inputs) :
  R.v36387 (state s) (inputs i) = Zmod.unsigned (N.v36387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36387 s i)) at 1.
  unfold R.v36387, N.v36387.
  rewrite ?node_36380.
  rewrite ?node_36381.
  rewrite ?node_36382.
  rewrite ?node_36386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36388 (s : N.State) (i : N.Inputs) :
  R.v36388 (state s) (inputs i) = Zmod.unsigned (N.v36388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36388 s i)) at 1.
  unfold R.v36388, N.v36388.
  unfold R.v6, N.v6.
  rewrite ?node_36387.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36389 (s : N.State) (i : N.Inputs) :
  R.v36389 (state s) (inputs i) = Zmod.unsigned (N.v36389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36389 s i)) at 1.
  unfold R.v36389, N.v36389.
  rewrite ?node_15400.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36390 (s : N.State) (i : N.Inputs) :
  R.v36390 (state s) (inputs i) = Zmod.unsigned (N.v36390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36390 s i)) at 1.
  unfold R.v36390, N.v36390.
  unfold R.v6, N.v6.
  rewrite ?node_15461.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36391 (s : N.State) (i : N.Inputs) :
  R.v36391 (state s) (inputs i) = Zmod.unsigned (N.v36391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36391 s i)) at 1.
  unfold R.v36391, N.v36391.
  unfold R.v6, N.v6.
  rewrite ?node_15481.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36392 (s : N.State) (i : N.Inputs) :
  R.v36392 (state s) (inputs i) = Zmod.unsigned (N.v36392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36392 s i)) at 1.
  unfold R.v36392, N.v36392.
  rewrite ?node_36389.
  rewrite ?node_36390.
  rewrite ?node_36391.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36393 (s : N.State) (i : N.Inputs) :
  R.v36393 (state s) (inputs i) = Zmod.unsigned (N.v36393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36393 s i)) at 1.
  unfold R.v36393, N.v36393.
  rewrite ?node_36388.
  rewrite ?node_36392.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36394 (s : N.State) (i : N.Inputs) :
  R.v36394 (state s) (inputs i) = Zmod.unsigned (N.v36394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36394 s i)) at 1.
  unfold R.v36394, N.v36394.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36395 (s : N.State) (i : N.Inputs) :
  R.v36395 (state s) (inputs i) = Zmod.unsigned (N.v36395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36395 s i)) at 1.
  unfold R.v36395, N.v36395.
  unfold R.v16463, N.v16463.
  rewrite !state_r2137_nr_5F2157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2137_nr_5F2157 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36396 (s : N.State) (i : N.Inputs) :
  R.v36396 (state s) (inputs i) = Zmod.unsigned (N.v36396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36396 s i)) at 1.
  unfold R.v36396, N.v36396.
  unfold R.v6, N.v6.
  rewrite !state_r2136_nr_5F2156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2136_nr_5F2156 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36397 (s : N.State) (i : N.Inputs) :
  R.v36397 (state s) (inputs i) = Zmod.unsigned (N.v36397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36397 s i)) at 1.
  unfold R.v36397, N.v36397.
  unfold R.v6, N.v6.
  rewrite !state_r2135_nr_5F2155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2135_nr_5F2155 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36398 (s : N.State) (i : N.Inputs) :
  R.v36398 (state s) (inputs i) = Zmod.unsigned (N.v36398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36398 s i)) at 1.
  unfold R.v36398, N.v36398.
  rewrite ?node_36396.
  rewrite ?node_36397.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36399 (s : N.State) (i : N.Inputs) :
  R.v36399 (state s) (inputs i) = Zmod.unsigned (N.v36399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36399 s i)) at 1.
  unfold R.v36399, N.v36399.
  unfold R.v16484, N.v16484.
  rewrite ?node_36398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36400 (s : N.State) (i : N.Inputs) :
  R.v36400 (state s) (inputs i) = Zmod.unsigned (N.v36400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36400 s i)) at 1.
  unfold R.v36400, N.v36400.
  rewrite ?node_36395.
  rewrite ?node_36399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36401 (s : N.State) (i : N.Inputs) :
  R.v36401 (state s) (inputs i) = Zmod.unsigned (N.v36401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36401 s i)) at 1.
  unfold R.v36401, N.v36401.
  unfold R.v6, N.v6.
  rewrite ?node_36400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36402 (s : N.State) (i : N.Inputs) :
  R.v36402 (state s) (inputs i) = Zmod.unsigned (N.v36402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36402 s i)) at 1.
  unfold R.v36402, N.v36402.
  rewrite ?node_15396.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36403 (s : N.State) (i : N.Inputs) :
  R.v36403 (state s) (inputs i) = Zmod.unsigned (N.v36403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36403 s i)) at 1.
  unfold R.v36403, N.v36403.
  unfold R.v6, N.v6.
  rewrite ?node_15461.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36404 (s : N.State) (i : N.Inputs) :
  R.v36404 (state s) (inputs i) = Zmod.unsigned (N.v36404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36404 s i)) at 1.
  unfold R.v36404, N.v36404.
  rewrite ?node_36402.
  rewrite ?node_36403.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36405 (s : N.State) (i : N.Inputs) :
  R.v36405 (state s) (inputs i) = Zmod.unsigned (N.v36405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36405 s i)) at 1.
  unfold R.v36405, N.v36405.
  rewrite ?node_36401.
  rewrite ?node_36404.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36406 (s : N.State) (i : N.Inputs) :
  R.v36406 (state s) (inputs i) = Zmod.unsigned (N.v36406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36406 s i)) at 1.
  unfold R.v36406, N.v36406.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36407 (s : N.State) (i : N.Inputs) :
  R.v36407 (state s) (inputs i) = Zmod.unsigned (N.v36407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36407 s i)) at 1.
  unfold R.v36407, N.v36407.
  rewrite ?node_15399.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36408 (s : N.State) (i : N.Inputs) :
  R.v36408 (state s) (inputs i) = Zmod.unsigned (N.v36408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36408 s i)) at 1.
  unfold R.v36408, N.v36408.
  unfold R.v6, N.v6.
  rewrite !state_r2138_nr_5F2158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2138_nr_5F2158 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36409 (s : N.State) (i : N.Inputs) :
  R.v36409 (state s) (inputs i) = Zmod.unsigned (N.v36409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36409 s i)) at 1.
  unfold R.v36409, N.v36409.
  unfold R.v6, N.v6.
  rewrite ?node_15396.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36410 (s : N.State) (i : N.Inputs) :
  R.v36410 (state s) (inputs i) = Zmod.unsigned (N.v36410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36410 s i)) at 1.
  unfold R.v36410, N.v36410.
  rewrite ?node_36408.
  rewrite ?node_36409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36411 (s : N.State) (i : N.Inputs) :
  R.v36411 (state s) (inputs i) = Zmod.unsigned (N.v36411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36411 s i)) at 1.
  unfold R.v36411, N.v36411.
  unfold R.v16484, N.v16484.
  rewrite ?node_36410.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36412 (s : N.State) (i : N.Inputs) :
  R.v36412 (state s) (inputs i) = Zmod.unsigned (N.v36412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36412 s i)) at 1.
  unfold R.v36412, N.v36412.
  rewrite ?node_36407.
  rewrite ?node_36411.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36413 (s : N.State) (i : N.Inputs) :
  R.v36413 (state s) (inputs i) = Zmod.unsigned (N.v36413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36413 s i)) at 1.
  unfold R.v36413, N.v36413.
  unfold R.v6, N.v6.
  rewrite ?node_36412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36414 (s : N.State) (i : N.Inputs) :
  R.v36414 (state s) (inputs i) = Zmod.unsigned (N.v36414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36414 s i)) at 1.
  unfold R.v36414, N.v36414.
  rewrite ?node_15400.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36415 (s : N.State) (i : N.Inputs) :
  R.v36415 (state s) (inputs i) = Zmod.unsigned (N.v36415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36415 s i)) at 1.
  unfold R.v36415, N.v36415.
  unfold R.v6, N.v6.
  rewrite ?node_15481.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36416 (s : N.State) (i : N.Inputs) :
  R.v36416 (state s) (inputs i) = Zmod.unsigned (N.v36416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36416 s i)) at 1.
  unfold R.v36416, N.v36416.
  rewrite ?node_36414.
  rewrite ?node_36415.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36417 (s : N.State) (i : N.Inputs) :
  R.v36417 (state s) (inputs i) = Zmod.unsigned (N.v36417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36417 s i)) at 1.
  unfold R.v36417, N.v36417.
  rewrite ?node_36413.
  rewrite ?node_36416.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36418 (s : N.State) (i : N.Inputs) :
  R.v36418 (state s) (inputs i) = Zmod.unsigned (N.v36418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36418 s i)) at 1.
  unfold R.v36418, N.v36418.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36419 (s : N.State) (i : N.Inputs) :
  R.v36419 (state s) (inputs i) = Zmod.unsigned (N.v36419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36419 s i)) at 1.
  unfold R.v36419, N.v36419.
  rewrite ?node_15406.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36420 (s : N.State) (i : N.Inputs) :
  R.v36420 (state s) (inputs i) = Zmod.unsigned (N.v36420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36420 s i)) at 1.
  unfold R.v36420, N.v36420.
  unfold R.v16463, N.v16463.
  rewrite !state_r2142_nr_5F2162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2142_nr_5F2162 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36421 (s : N.State) (i : N.Inputs) :
  R.v36421 (state s) (inputs i) = Zmod.unsigned (N.v36421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36421 s i)) at 1.
  unfold R.v36421, N.v36421.
  unfold R.v16463, N.v16463.
  rewrite !state_r2141_nr_5F2161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2141_nr_5F2161 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36422 (s : N.State) (i : N.Inputs) :
  R.v36422 (state s) (inputs i) = Zmod.unsigned (N.v36422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36422 s i)) at 1.
  unfold R.v36422, N.v36422.
  unfold R.v6, N.v6.
  rewrite !state_r2140_nr_5F2160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2140_nr_5F2160 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36423 (s : N.State) (i : N.Inputs) :
  R.v36423 (state s) (inputs i) = Zmod.unsigned (N.v36423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36423 s i)) at 1.
  unfold R.v36423, N.v36423.
  unfold R.v6, N.v6.
  rewrite !state_r2139_nr_5F2159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2139_nr_5F2159 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36424 (s : N.State) (i : N.Inputs) :
  R.v36424 (state s) (inputs i) = Zmod.unsigned (N.v36424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36424 s i)) at 1.
  unfold R.v36424, N.v36424.
  rewrite ?node_36422.
  rewrite ?node_36423.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36425 (s : N.State) (i : N.Inputs) :
  R.v36425 (state s) (inputs i) = Zmod.unsigned (N.v36425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36425 s i)) at 1.
  unfold R.v36425, N.v36425.
  unfold R.v16484, N.v16484.
  rewrite ?node_36424.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36426 (s : N.State) (i : N.Inputs) :
  R.v36426 (state s) (inputs i) = Zmod.unsigned (N.v36426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36426 s i)) at 1.
  unfold R.v36426, N.v36426.
  rewrite ?node_36419.
  rewrite ?node_36420.
  rewrite ?node_36421.
  rewrite ?node_36425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36427 (s : N.State) (i : N.Inputs) :
  R.v36427 (state s) (inputs i) = Zmod.unsigned (N.v36427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36427 s i)) at 1.
  unfold R.v36427, N.v36427.
  unfold R.v6, N.v6.
  rewrite ?node_36426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36428 (s : N.State) (i : N.Inputs) :
  R.v36428 (state s) (inputs i) = Zmod.unsigned (N.v36428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36428 s i)) at 1.
  unfold R.v36428, N.v36428.
  rewrite ?node_15407.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36429 (s : N.State) (i : N.Inputs) :
  R.v36429 (state s) (inputs i) = Zmod.unsigned (N.v36429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36429 s i)) at 1.
  unfold R.v36429, N.v36429.
  unfold R.v6, N.v6.
  rewrite ?node_15468.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36430 (s : N.State) (i : N.Inputs) :
  R.v36430 (state s) (inputs i) = Zmod.unsigned (N.v36430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36430 s i)) at 1.
  unfold R.v36430, N.v36430.
  unfold R.v6, N.v6.
  rewrite ?node_15489.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36431 (s : N.State) (i : N.Inputs) :
  R.v36431 (state s) (inputs i) = Zmod.unsigned (N.v36431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36431 s i)) at 1.
  unfold R.v36431, N.v36431.
  rewrite ?node_36428.
  rewrite ?node_36429.
  rewrite ?node_36430.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36432 (s : N.State) (i : N.Inputs) :
  R.v36432 (state s) (inputs i) = Zmod.unsigned (N.v36432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36432 s i)) at 1.
  unfold R.v36432, N.v36432.
  rewrite ?node_36427.
  rewrite ?node_36431.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36433 (s : N.State) (i : N.Inputs) :
  R.v36433 (state s) (inputs i) = Zmod.unsigned (N.v36433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36433 s i)) at 1.
  unfold R.v36433, N.v36433.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36434 (s : N.State) (i : N.Inputs) :
  R.v36434 (state s) (inputs i) = Zmod.unsigned (N.v36434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36434 s i)) at 1.
  unfold R.v36434, N.v36434.
  unfold R.v16463, N.v16463.
  rewrite !state_r2141_nr_5F2161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2141_nr_5F2161 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36435 (s : N.State) (i : N.Inputs) :
  R.v36435 (state s) (inputs i) = Zmod.unsigned (N.v36435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36435 s i)) at 1.
  unfold R.v36435, N.v36435.
  unfold R.v6, N.v6.
  rewrite !state_r2140_nr_5F2160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2140_nr_5F2160 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36436 (s : N.State) (i : N.Inputs) :
  R.v36436 (state s) (inputs i) = Zmod.unsigned (N.v36436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36436 s i)) at 1.
  unfold R.v36436, N.v36436.
  unfold R.v6, N.v6.
  rewrite !state_r2139_nr_5F2159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2139_nr_5F2159 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36437 (s : N.State) (i : N.Inputs) :
  R.v36437 (state s) (inputs i) = Zmod.unsigned (N.v36437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36437 s i)) at 1.
  unfold R.v36437, N.v36437.
  rewrite ?node_36435.
  rewrite ?node_36436.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36438 (s : N.State) (i : N.Inputs) :
  R.v36438 (state s) (inputs i) = Zmod.unsigned (N.v36438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36438 s i)) at 1.
  unfold R.v36438, N.v36438.
  unfold R.v16484, N.v16484.
  rewrite ?node_36437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36439 (s : N.State) (i : N.Inputs) :
  R.v36439 (state s) (inputs i) = Zmod.unsigned (N.v36439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36439 s i)) at 1.
  unfold R.v36439, N.v36439.
  rewrite ?node_36434.
  rewrite ?node_36438.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36440 (s : N.State) (i : N.Inputs) :
  R.v36440 (state s) (inputs i) = Zmod.unsigned (N.v36440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36440 s i)) at 1.
  unfold R.v36440, N.v36440.
  unfold R.v6, N.v6.
  rewrite ?node_36439.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36441 (s : N.State) (i : N.Inputs) :
  R.v36441 (state s) (inputs i) = Zmod.unsigned (N.v36441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36441 s i)) at 1.
  unfold R.v36441, N.v36441.
  rewrite ?node_15402.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36442 (s : N.State) (i : N.Inputs) :
  R.v36442 (state s) (inputs i) = Zmod.unsigned (N.v36442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36442 s i)) at 1.
  unfold R.v36442, N.v36442.
  unfold R.v6, N.v6.
  rewrite ?node_15468.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36443 (s : N.State) (i : N.Inputs) :
  R.v36443 (state s) (inputs i) = Zmod.unsigned (N.v36443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36443 s i)) at 1.
  unfold R.v36443, N.v36443.
  rewrite ?node_36441.
  rewrite ?node_36442.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36444 (s : N.State) (i : N.Inputs) :
  R.v36444 (state s) (inputs i) = Zmod.unsigned (N.v36444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36444 s i)) at 1.
  unfold R.v36444, N.v36444.
  rewrite ?node_36440.
  rewrite ?node_36443.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36445 (s : N.State) (i : N.Inputs) :
  R.v36445 (state s) (inputs i) = Zmod.unsigned (N.v36445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36445 s i)) at 1.
  unfold R.v36445, N.v36445.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36446 (s : N.State) (i : N.Inputs) :
  R.v36446 (state s) (inputs i) = Zmod.unsigned (N.v36446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36446 s i)) at 1.
  unfold R.v36446, N.v36446.
  rewrite ?node_15406.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36447 (s : N.State) (i : N.Inputs) :
  R.v36447 (state s) (inputs i) = Zmod.unsigned (N.v36447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36447 s i)) at 1.
  unfold R.v36447, N.v36447.
  unfold R.v6, N.v6.
  rewrite !state_r2142_nr_5F2162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2142_nr_5F2162 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36448 (s : N.State) (i : N.Inputs) :
  R.v36448 (state s) (inputs i) = Zmod.unsigned (N.v36448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36448 s i)) at 1.
  unfold R.v36448, N.v36448.
  unfold R.v6, N.v6.
  rewrite ?node_15402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36449 (s : N.State) (i : N.Inputs) :
  R.v36449 (state s) (inputs i) = Zmod.unsigned (N.v36449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36449 s i)) at 1.
  unfold R.v36449, N.v36449.
  rewrite ?node_36447.
  rewrite ?node_36448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36450 (s : N.State) (i : N.Inputs) :
  R.v36450 (state s) (inputs i) = Zmod.unsigned (N.v36450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36450 s i)) at 1.
  unfold R.v36450, N.v36450.
  unfold R.v16484, N.v16484.
  rewrite ?node_36449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36451 (s : N.State) (i : N.Inputs) :
  R.v36451 (state s) (inputs i) = Zmod.unsigned (N.v36451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36451 s i)) at 1.
  unfold R.v36451, N.v36451.
  rewrite ?node_36446.
  rewrite ?node_36450.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36452 (s : N.State) (i : N.Inputs) :
  R.v36452 (state s) (inputs i) = Zmod.unsigned (N.v36452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36452 s i)) at 1.
  unfold R.v36452, N.v36452.
  unfold R.v6, N.v6.
  rewrite ?node_36451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36453 (s : N.State) (i : N.Inputs) :
  R.v36453 (state s) (inputs i) = Zmod.unsigned (N.v36453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36453 s i)) at 1.
  unfold R.v36453, N.v36453.
  rewrite ?node_15407.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36454 (s : N.State) (i : N.Inputs) :
  R.v36454 (state s) (inputs i) = Zmod.unsigned (N.v36454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36454 s i)) at 1.
  unfold R.v36454, N.v36454.
  unfold R.v6, N.v6.
  rewrite ?node_15489.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36455 (s : N.State) (i : N.Inputs) :
  R.v36455 (state s) (inputs i) = Zmod.unsigned (N.v36455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36455 s i)) at 1.
  unfold R.v36455, N.v36455.
  rewrite ?node_36453.
  rewrite ?node_36454.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36456 (s : N.State) (i : N.Inputs) :
  R.v36456 (state s) (inputs i) = Zmod.unsigned (N.v36456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36456 s i)) at 1.
  unfold R.v36456, N.v36456.
  rewrite ?node_36452.
  rewrite ?node_36455.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36457 (s : N.State) (i : N.Inputs) :
  R.v36457 (state s) (inputs i) = Zmod.unsigned (N.v36457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36457 s i)) at 1.
  unfold R.v36457, N.v36457.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36458 (s : N.State) (i : N.Inputs) :
  R.v36458 (state s) (inputs i) = Zmod.unsigned (N.v36458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36458 s i)) at 1.
  unfold R.v36458, N.v36458.
  rewrite ?node_15414.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36459 (s : N.State) (i : N.Inputs) :
  R.v36459 (state s) (inputs i) = Zmod.unsigned (N.v36459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36459 s i)) at 1.
  unfold R.v36459, N.v36459.
  unfold R.v16463, N.v16463.
  rewrite !state_r2146_nr_5F2166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2146_nr_5F2166 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36460 (s : N.State) (i : N.Inputs) :
  R.v36460 (state s) (inputs i) = Zmod.unsigned (N.v36460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36460 s i)) at 1.
  unfold R.v36460, N.v36460.
  unfold R.v16463, N.v16463.
  rewrite !state_r2145_nr_5F2165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2145_nr_5F2165 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36461 (s : N.State) (i : N.Inputs) :
  R.v36461 (state s) (inputs i) = Zmod.unsigned (N.v36461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36461 s i)) at 1.
  unfold R.v36461, N.v36461.
  unfold R.v6, N.v6.
  rewrite !state_r2144_nr_5F2164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2144_nr_5F2164 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36462 (s : N.State) (i : N.Inputs) :
  R.v36462 (state s) (inputs i) = Zmod.unsigned (N.v36462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36462 s i)) at 1.
  unfold R.v36462, N.v36462.
  unfold R.v6, N.v6.
  rewrite !state_r2143_nr_5F2163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2143_nr_5F2163 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36463 (s : N.State) (i : N.Inputs) :
  R.v36463 (state s) (inputs i) = Zmod.unsigned (N.v36463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36463 s i)) at 1.
  unfold R.v36463, N.v36463.
  rewrite ?node_36461.
  rewrite ?node_36462.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36464 (s : N.State) (i : N.Inputs) :
  R.v36464 (state s) (inputs i) = Zmod.unsigned (N.v36464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36464 s i)) at 1.
  unfold R.v36464, N.v36464.
  unfold R.v16484, N.v16484.
  rewrite ?node_36463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36465 (s : N.State) (i : N.Inputs) :
  R.v36465 (state s) (inputs i) = Zmod.unsigned (N.v36465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36465 s i)) at 1.
  unfold R.v36465, N.v36465.
  rewrite ?node_36458.
  rewrite ?node_36459.
  rewrite ?node_36460.
  rewrite ?node_36464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36466 (s : N.State) (i : N.Inputs) :
  R.v36466 (state s) (inputs i) = Zmod.unsigned (N.v36466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36466 s i)) at 1.
  unfold R.v36466, N.v36466.
  unfold R.v6, N.v6.
  rewrite ?node_36465.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36467 (s : N.State) (i : N.Inputs) :
  R.v36467 (state s) (inputs i) = Zmod.unsigned (N.v36467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36467 s i)) at 1.
  unfold R.v36467, N.v36467.
  rewrite ?node_15415.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36468 (s : N.State) (i : N.Inputs) :
  R.v36468 (state s) (inputs i) = Zmod.unsigned (N.v36468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36468 s i)) at 1.
  unfold R.v36468, N.v36468.
  unfold R.v6, N.v6.
  rewrite ?node_15476.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36469 (s : N.State) (i : N.Inputs) :
  R.v36469 (state s) (inputs i) = Zmod.unsigned (N.v36469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36469 s i)) at 1.
  unfold R.v36469, N.v36469.
  unfold R.v6, N.v6.
  rewrite ?node_15492.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36470 (s : N.State) (i : N.Inputs) :
  R.v36470 (state s) (inputs i) = Zmod.unsigned (N.v36470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36470 s i)) at 1.
  unfold R.v36470, N.v36470.
  rewrite ?node_36467.
  rewrite ?node_36468.
  rewrite ?node_36469.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36471 (s : N.State) (i : N.Inputs) :
  R.v36471 (state s) (inputs i) = Zmod.unsigned (N.v36471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36471 s i)) at 1.
  unfold R.v36471, N.v36471.
  rewrite ?node_36466.
  rewrite ?node_36470.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36472 (s : N.State) (i : N.Inputs) :
  R.v36472 (state s) (inputs i) = Zmod.unsigned (N.v36472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36472 s i)) at 1.
  unfold R.v36472, N.v36472.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36473 (s : N.State) (i : N.Inputs) :
  R.v36473 (state s) (inputs i) = Zmod.unsigned (N.v36473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36473 s i)) at 1.
  unfold R.v36473, N.v36473.
  unfold R.v16463, N.v16463.
  rewrite !state_r2145_nr_5F2165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2145_nr_5F2165 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36474 (s : N.State) (i : N.Inputs) :
  R.v36474 (state s) (inputs i) = Zmod.unsigned (N.v36474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36474 s i)) at 1.
  unfold R.v36474, N.v36474.
  unfold R.v6, N.v6.
  rewrite !state_r2144_nr_5F2164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2144_nr_5F2164 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36475 (s : N.State) (i : N.Inputs) :
  R.v36475 (state s) (inputs i) = Zmod.unsigned (N.v36475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36475 s i)) at 1.
  unfold R.v36475, N.v36475.
  unfold R.v6, N.v6.
  rewrite !state_r2143_nr_5F2163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2143_nr_5F2163 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36476 (s : N.State) (i : N.Inputs) :
  R.v36476 (state s) (inputs i) = Zmod.unsigned (N.v36476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36476 s i)) at 1.
  unfold R.v36476, N.v36476.
  rewrite ?node_36474.
  rewrite ?node_36475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36477 (s : N.State) (i : N.Inputs) :
  R.v36477 (state s) (inputs i) = Zmod.unsigned (N.v36477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36477 s i)) at 1.
  unfold R.v36477, N.v36477.
  unfold R.v16484, N.v16484.
  rewrite ?node_36476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36478 (s : N.State) (i : N.Inputs) :
  R.v36478 (state s) (inputs i) = Zmod.unsigned (N.v36478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36478 s i)) at 1.
  unfold R.v36478, N.v36478.
  rewrite ?node_36473.
  rewrite ?node_36477.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36479 (s : N.State) (i : N.Inputs) :
  R.v36479 (state s) (inputs i) = Zmod.unsigned (N.v36479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36479 s i)) at 1.
  unfold R.v36479, N.v36479.
  unfold R.v6, N.v6.
  rewrite ?node_36478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36480 (s : N.State) (i : N.Inputs) :
  R.v36480 (state s) (inputs i) = Zmod.unsigned (N.v36480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36480 s i)) at 1.
  unfold R.v36480, N.v36480.
  rewrite ?node_15410.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36481 (s : N.State) (i : N.Inputs) :
  R.v36481 (state s) (inputs i) = Zmod.unsigned (N.v36481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36481 s i)) at 1.
  unfold R.v36481, N.v36481.
  unfold R.v6, N.v6.
  rewrite ?node_15476.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36482 (s : N.State) (i : N.Inputs) :
  R.v36482 (state s) (inputs i) = Zmod.unsigned (N.v36482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36482 s i)) at 1.
  unfold R.v36482, N.v36482.
  rewrite ?node_36480.
  rewrite ?node_36481.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36483 (s : N.State) (i : N.Inputs) :
  R.v36483 (state s) (inputs i) = Zmod.unsigned (N.v36483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36483 s i)) at 1.
  unfold R.v36483, N.v36483.
  rewrite ?node_36479.
  rewrite ?node_36482.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36484 (s : N.State) (i : N.Inputs) :
  R.v36484 (state s) (inputs i) = Zmod.unsigned (N.v36484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36484 s i)) at 1.
  unfold R.v36484, N.v36484.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36485 (s : N.State) (i : N.Inputs) :
  R.v36485 (state s) (inputs i) = Zmod.unsigned (N.v36485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36485 s i)) at 1.
  unfold R.v36485, N.v36485.
  rewrite ?node_15414.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36486 (s : N.State) (i : N.Inputs) :
  R.v36486 (state s) (inputs i) = Zmod.unsigned (N.v36486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36486 s i)) at 1.
  unfold R.v36486, N.v36486.
  unfold R.v6, N.v6.
  rewrite !state_r2146_nr_5F2166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2146_nr_5F2166 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36487 (s : N.State) (i : N.Inputs) :
  R.v36487 (state s) (inputs i) = Zmod.unsigned (N.v36487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36487 s i)) at 1.
  unfold R.v36487, N.v36487.
  unfold R.v6, N.v6.
  rewrite ?node_15410.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36488 (s : N.State) (i : N.Inputs) :
  R.v36488 (state s) (inputs i) = Zmod.unsigned (N.v36488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36488 s i)) at 1.
  unfold R.v36488, N.v36488.
  rewrite ?node_36486.
  rewrite ?node_36487.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36489 (s : N.State) (i : N.Inputs) :
  R.v36489 (state s) (inputs i) = Zmod.unsigned (N.v36489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36489 s i)) at 1.
  unfold R.v36489, N.v36489.
  unfold R.v16484, N.v16484.
  rewrite ?node_36488.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36490 (s : N.State) (i : N.Inputs) :
  R.v36490 (state s) (inputs i) = Zmod.unsigned (N.v36490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36490 s i)) at 1.
  unfold R.v36490, N.v36490.
  rewrite ?node_36485.
  rewrite ?node_36489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36491 (s : N.State) (i : N.Inputs) :
  R.v36491 (state s) (inputs i) = Zmod.unsigned (N.v36491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36491 s i)) at 1.
  unfold R.v36491, N.v36491.
  unfold R.v6, N.v6.
  rewrite ?node_36490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36492 (s : N.State) (i : N.Inputs) :
  R.v36492 (state s) (inputs i) = Zmod.unsigned (N.v36492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36492 s i)) at 1.
  unfold R.v36492, N.v36492.
  rewrite ?node_15415.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36493 (s : N.State) (i : N.Inputs) :
  R.v36493 (state s) (inputs i) = Zmod.unsigned (N.v36493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36493 s i)) at 1.
  unfold R.v36493, N.v36493.
  unfold R.v6, N.v6.
  rewrite ?node_15492.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36494 (s : N.State) (i : N.Inputs) :
  R.v36494 (state s) (inputs i) = Zmod.unsigned (N.v36494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36494 s i)) at 1.
  unfold R.v36494, N.v36494.
  rewrite ?node_36492.
  rewrite ?node_36493.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36495 (s : N.State) (i : N.Inputs) :
  R.v36495 (state s) (inputs i) = Zmod.unsigned (N.v36495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36495 s i)) at 1.
  unfold R.v36495, N.v36495.
  rewrite ?node_36491.
  rewrite ?node_36494.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36496 (s : N.State) (i : N.Inputs) :
  R.v36496 (state s) (inputs i) = Zmod.unsigned (N.v36496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36496 s i)) at 1.
  unfold R.v36496, N.v36496.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36497 (s : N.State) (i : N.Inputs) :
  R.v36497 (state s) (inputs i) = Zmod.unsigned (N.v36497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36497 s i)) at 1.
  unfold R.v36497, N.v36497.
  rewrite ?node_15461.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36498 (s : N.State) (i : N.Inputs) :
  R.v36498 (state s) (inputs i) = Zmod.unsigned (N.v36498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36498 s i)) at 1.
  unfold R.v36498, N.v36498.
  unfold R.v16463, N.v16463.
  rewrite !state_r2149_nr_5F2170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2149_nr_5F2170 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36499 (s : N.State) (i : N.Inputs) :
  R.v36499 (state s) (inputs i) = Zmod.unsigned (N.v36499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36499 s i)) at 1.
  unfold R.v36499, N.v36499.
  unfold R.v16463, N.v16463.
  rewrite !state_r2148_nr_5F2169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2148_nr_5F2169 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36500 (s : N.State) (i : N.Inputs) :
  R.v36500 (state s) (inputs i) = Zmod.unsigned (N.v36500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36500 s i)) at 1.
  unfold R.v36500, N.v36500.
  unfold R.v6, N.v6.
  rewrite !state_r2147_nr_5F2168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2147_nr_5F2168 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36501 (s : N.State) (i : N.Inputs) :
  R.v36501 (state s) (inputs i) = Zmod.unsigned (N.v36501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36501 s i)) at 1.
  unfold R.v36501, N.v36501.
  unfold R.v19, N.v19.
  rewrite ?node_36500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36502 (s : N.State) (i : N.Inputs) :
  R.v36502 (state s) (inputs i) = Zmod.unsigned (N.v36502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36502 s i)) at 1.
  unfold R.v36502, N.v36502.
  unfold R.v16484, N.v16484.
  rewrite ?node_36501.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36503 (s : N.State) (i : N.Inputs) :
  R.v36503 (state s) (inputs i) = Zmod.unsigned (N.v36503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36503 s i)) at 1.
  unfold R.v36503, N.v36503.
  rewrite ?node_36497.
  rewrite ?node_36498.
  rewrite ?node_36499.
  rewrite ?node_36502.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36504 (s : N.State) (i : N.Inputs) :
  R.v36504 (state s) (inputs i) = Zmod.unsigned (N.v36504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36504 s i)) at 1.
  unfold R.v36504, N.v36504.
  unfold R.v6, N.v6.
  rewrite ?node_36503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36505 (s : N.State) (i : N.Inputs) :
  R.v36505 (state s) (inputs i) = Zmod.unsigned (N.v36505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36505 s i)) at 1.
  unfold R.v36505, N.v36505.
  rewrite ?node_15462.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36506 (s : N.State) (i : N.Inputs) :
  R.v36506 (state s) (inputs i) = Zmod.unsigned (N.v36506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36506 s i)) at 1.
  unfold R.v36506, N.v36506.
  unfold R.v6, N.v6.
  rewrite ?node_15518.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36507 (s : N.State) (i : N.Inputs) :
  R.v36507 (state s) (inputs i) = Zmod.unsigned (N.v36507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36507 s i)) at 1.
  unfold R.v36507, N.v36507.
  unfold R.v6, N.v6.
  rewrite ?node_15541.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36508 (s : N.State) (i : N.Inputs) :
  R.v36508 (state s) (inputs i) = Zmod.unsigned (N.v36508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36508 s i)) at 1.
  unfold R.v36508, N.v36508.
  rewrite ?node_36505.
  rewrite ?node_36506.
  rewrite ?node_36507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36509 (s : N.State) (i : N.Inputs) :
  R.v36509 (state s) (inputs i) = Zmod.unsigned (N.v36509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36509 s i)) at 1.
  unfold R.v36509, N.v36509.
  rewrite ?node_36504.
  rewrite ?node_36508.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36510 (s : N.State) (i : N.Inputs) :
  R.v36510 (state s) (inputs i) = Zmod.unsigned (N.v36510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36510 s i)) at 1.
  unfold R.v36510, N.v36510.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36511 (s : N.State) (i : N.Inputs) :
  R.v36511 (state s) (inputs i) = Zmod.unsigned (N.v36511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36511 s i)) at 1.
  unfold R.v36511, N.v36511.
  unfold R.v16463, N.v16463.
  rewrite !state_r2148_nr_5F2169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2148_nr_5F2169 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36512 (s : N.State) (i : N.Inputs) :
  R.v36512 (state s) (inputs i) = Zmod.unsigned (N.v36512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36512 s i)) at 1.
  unfold R.v36512, N.v36512.
  unfold R.v6, N.v6.
  rewrite !state_r2147_nr_5F2168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2147_nr_5F2168 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36513 (s : N.State) (i : N.Inputs) :
  R.v36513 (state s) (inputs i) = Zmod.unsigned (N.v36513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36513 s i)) at 1.
  unfold R.v36513, N.v36513.
  unfold R.v19, N.v19.
  rewrite ?node_36512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36514 (s : N.State) (i : N.Inputs) :
  R.v36514 (state s) (inputs i) = Zmod.unsigned (N.v36514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36514 s i)) at 1.
  unfold R.v36514, N.v36514.
  unfold R.v16484, N.v16484.
  rewrite ?node_36513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36515 (s : N.State) (i : N.Inputs) :
  R.v36515 (state s) (inputs i) = Zmod.unsigned (N.v36515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36515 s i)) at 1.
  unfold R.v36515, N.v36515.
  rewrite ?node_36511.
  rewrite ?node_36514.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36516 (s : N.State) (i : N.Inputs) :
  R.v36516 (state s) (inputs i) = Zmod.unsigned (N.v36516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36516 s i)) at 1.
  unfold R.v36516, N.v36516.
  unfold R.v6, N.v6.
  rewrite ?node_36515.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36517 (s : N.State) (i : N.Inputs) :
  R.v36517 (state s) (inputs i) = Zmod.unsigned (N.v36517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36517 s i)) at 1.
  unfold R.v36517, N.v36517.
  rewrite ?node_15457.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36518 (s : N.State) (i : N.Inputs) :
  R.v36518 (state s) (inputs i) = Zmod.unsigned (N.v36518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36518 s i)) at 1.
  unfold R.v36518, N.v36518.
  unfold R.v6, N.v6.
  rewrite ?node_15518.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36519 (s : N.State) (i : N.Inputs) :
  R.v36519 (state s) (inputs i) = Zmod.unsigned (N.v36519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36519 s i)) at 1.
  unfold R.v36519, N.v36519.
  rewrite ?node_36517.
  rewrite ?node_36518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36520 (s : N.State) (i : N.Inputs) :
  R.v36520 (state s) (inputs i) = Zmod.unsigned (N.v36520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36520 s i)) at 1.
  unfold R.v36520, N.v36520.
  rewrite ?node_36516.
  rewrite ?node_36519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36521 (s : N.State) (i : N.Inputs) :
  R.v36521 (state s) (inputs i) = Zmod.unsigned (N.v36521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36521 s i)) at 1.
  unfold R.v36521, N.v36521.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36522 (s : N.State) (i : N.Inputs) :
  R.v36522 (state s) (inputs i) = Zmod.unsigned (N.v36522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36522 s i)) at 1.
  unfold R.v36522, N.v36522.
  rewrite ?node_15461.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36523 (s : N.State) (i : N.Inputs) :
  R.v36523 (state s) (inputs i) = Zmod.unsigned (N.v36523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36523 s i)) at 1.
  unfold R.v36523, N.v36523.
  unfold R.v6, N.v6.
  rewrite !state_r2149_nr_5F2170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2149_nr_5F2170 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36524 (s : N.State) (i : N.Inputs) :
  R.v36524 (state s) (inputs i) = Zmod.unsigned (N.v36524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36524 s i)) at 1.
  unfold R.v36524, N.v36524.
  unfold R.v6, N.v6.
  rewrite ?node_15457.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36525 (s : N.State) (i : N.Inputs) :
  R.v36525 (state s) (inputs i) = Zmod.unsigned (N.v36525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36525 s i)) at 1.
  unfold R.v36525, N.v36525.
  rewrite ?node_36523.
  rewrite ?node_36524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36526 (s : N.State) (i : N.Inputs) :
  R.v36526 (state s) (inputs i) = Zmod.unsigned (N.v36526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36526 s i)) at 1.
  unfold R.v36526, N.v36526.
  unfold R.v16484, N.v16484.
  rewrite ?node_36525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36527 (s : N.State) (i : N.Inputs) :
  R.v36527 (state s) (inputs i) = Zmod.unsigned (N.v36527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36527 s i)) at 1.
  unfold R.v36527, N.v36527.
  rewrite ?node_36522.
  rewrite ?node_36526.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36528 (s : N.State) (i : N.Inputs) :
  R.v36528 (state s) (inputs i) = Zmod.unsigned (N.v36528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36528 s i)) at 1.
  unfold R.v36528, N.v36528.
  unfold R.v6, N.v6.
  rewrite ?node_36527.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36529 (s : N.State) (i : N.Inputs) :
  R.v36529 (state s) (inputs i) = Zmod.unsigned (N.v36529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36529 s i)) at 1.
  unfold R.v36529, N.v36529.
  rewrite ?node_15462.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36530 (s : N.State) (i : N.Inputs) :
  R.v36530 (state s) (inputs i) = Zmod.unsigned (N.v36530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36530 s i)) at 1.
  unfold R.v36530, N.v36530.
  unfold R.v6, N.v6.
  rewrite ?node_15541.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36531 (s : N.State) (i : N.Inputs) :
  R.v36531 (state s) (inputs i) = Zmod.unsigned (N.v36531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36531 s i)) at 1.
  unfold R.v36531, N.v36531.
  rewrite ?node_36529.
  rewrite ?node_36530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36532 (s : N.State) (i : N.Inputs) :
  R.v36532 (state s) (inputs i) = Zmod.unsigned (N.v36532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36532 s i)) at 1.
  unfold R.v36532, N.v36532.
  rewrite ?node_36528.
  rewrite ?node_36531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36533 (s : N.State) (i : N.Inputs) :
  R.v36533 (state s) (inputs i) = Zmod.unsigned (N.v36533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36533 s i)) at 1.
  unfold R.v36533, N.v36533.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36534 (s : N.State) (i : N.Inputs) :
  R.v36534 (state s) (inputs i) = Zmod.unsigned (N.v36534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36534 s i)) at 1.
  unfold R.v36534, N.v36534.
  rewrite ?node_15468.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36535 (s : N.State) (i : N.Inputs) :
  R.v36535 (state s) (inputs i) = Zmod.unsigned (N.v36535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36535 s i)) at 1.
  unfold R.v36535, N.v36535.
  unfold R.v16463, N.v16463.
  rewrite !state_r2153_nr_5F2174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2153_nr_5F2174 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36536 (s : N.State) (i : N.Inputs) :
  R.v36536 (state s) (inputs i) = Zmod.unsigned (N.v36536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36536 s i)) at 1.
  unfold R.v36536, N.v36536.
  unfold R.v16463, N.v16463.
  rewrite !state_r2152_nr_5F2173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2152_nr_5F2173 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36537 (s : N.State) (i : N.Inputs) :
  R.v36537 (state s) (inputs i) = Zmod.unsigned (N.v36537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36537 s i)) at 1.
  unfold R.v36537, N.v36537.
  unfold R.v6, N.v6.
  rewrite !state_r2151_nr_5F2172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2151_nr_5F2172 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36538 (s : N.State) (i : N.Inputs) :
  R.v36538 (state s) (inputs i) = Zmod.unsigned (N.v36538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36538 s i)) at 1.
  unfold R.v36538, N.v36538.
  unfold R.v6, N.v6.
  rewrite !state_r2150_nr_5F2171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2150_nr_5F2171 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36539 (s : N.State) (i : N.Inputs) :
  R.v36539 (state s) (inputs i) = Zmod.unsigned (N.v36539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36539 s i)) at 1.
  unfold R.v36539, N.v36539.
  rewrite ?node_36537.
  rewrite ?node_36538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36540 (s : N.State) (i : N.Inputs) :
  R.v36540 (state s) (inputs i) = Zmod.unsigned (N.v36540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36540 s i)) at 1.
  unfold R.v36540, N.v36540.
  unfold R.v16484, N.v16484.
  rewrite ?node_36539.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36541 (s : N.State) (i : N.Inputs) :
  R.v36541 (state s) (inputs i) = Zmod.unsigned (N.v36541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36541 s i)) at 1.
  unfold R.v36541, N.v36541.
  rewrite ?node_36534.
  rewrite ?node_36535.
  rewrite ?node_36536.
  rewrite ?node_36540.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36542 (s : N.State) (i : N.Inputs) :
  R.v36542 (state s) (inputs i) = Zmod.unsigned (N.v36542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36542 s i)) at 1.
  unfold R.v36542, N.v36542.
  unfold R.v6, N.v6.
  rewrite ?node_36541.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36543 (s : N.State) (i : N.Inputs) :
  R.v36543 (state s) (inputs i) = Zmod.unsigned (N.v36543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36543 s i)) at 1.
  unfold R.v36543, N.v36543.
  rewrite ?node_15469.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36544 (s : N.State) (i : N.Inputs) :
  R.v36544 (state s) (inputs i) = Zmod.unsigned (N.v36544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36544 s i)) at 1.
  unfold R.v36544, N.v36544.
  unfold R.v6, N.v6.
  rewrite ?node_15525.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36545 (s : N.State) (i : N.Inputs) :
  R.v36545 (state s) (inputs i) = Zmod.unsigned (N.v36545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36545 s i)) at 1.
  unfold R.v36545, N.v36545.
  unfold R.v6, N.v6.
  rewrite ?node_15544.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36546 (s : N.State) (i : N.Inputs) :
  R.v36546 (state s) (inputs i) = Zmod.unsigned (N.v36546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36546 s i)) at 1.
  unfold R.v36546, N.v36546.
  rewrite ?node_36543.
  rewrite ?node_36544.
  rewrite ?node_36545.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36547 (s : N.State) (i : N.Inputs) :
  R.v36547 (state s) (inputs i) = Zmod.unsigned (N.v36547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36547 s i)) at 1.
  unfold R.v36547, N.v36547.
  rewrite ?node_36542.
  rewrite ?node_36546.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36548 (s : N.State) (i : N.Inputs) :
  R.v36548 (state s) (inputs i) = Zmod.unsigned (N.v36548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36548 s i)) at 1.
  unfold R.v36548, N.v36548.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36549 (s : N.State) (i : N.Inputs) :
  R.v36549 (state s) (inputs i) = Zmod.unsigned (N.v36549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36549 s i)) at 1.
  unfold R.v36549, N.v36549.
  unfold R.v16463, N.v16463.
  rewrite !state_r2152_nr_5F2173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2152_nr_5F2173 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36550 (s : N.State) (i : N.Inputs) :
  R.v36550 (state s) (inputs i) = Zmod.unsigned (N.v36550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36550 s i)) at 1.
  unfold R.v36550, N.v36550.
  unfold R.v6, N.v6.
  rewrite !state_r2151_nr_5F2172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2151_nr_5F2172 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36551 (s : N.State) (i : N.Inputs) :
  R.v36551 (state s) (inputs i) = Zmod.unsigned (N.v36551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36551 s i)) at 1.
  unfold R.v36551, N.v36551.
  unfold R.v6, N.v6.
  rewrite !state_r2150_nr_5F2171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2150_nr_5F2171 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36552 (s : N.State) (i : N.Inputs) :
  R.v36552 (state s) (inputs i) = Zmod.unsigned (N.v36552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36552 s i)) at 1.
  unfold R.v36552, N.v36552.
  rewrite ?node_36550.
  rewrite ?node_36551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36553 (s : N.State) (i : N.Inputs) :
  R.v36553 (state s) (inputs i) = Zmod.unsigned (N.v36553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36553 s i)) at 1.
  unfold R.v36553, N.v36553.
  unfold R.v16484, N.v16484.
  rewrite ?node_36552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36554 (s : N.State) (i : N.Inputs) :
  R.v36554 (state s) (inputs i) = Zmod.unsigned (N.v36554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36554 s i)) at 1.
  unfold R.v36554, N.v36554.
  rewrite ?node_36549.
  rewrite ?node_36553.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36555 (s : N.State) (i : N.Inputs) :
  R.v36555 (state s) (inputs i) = Zmod.unsigned (N.v36555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36555 s i)) at 1.
  unfold R.v36555, N.v36555.
  unfold R.v6, N.v6.
  rewrite ?node_36554.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36556 (s : N.State) (i : N.Inputs) :
  R.v36556 (state s) (inputs i) = Zmod.unsigned (N.v36556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36556 s i)) at 1.
  unfold R.v36556, N.v36556.
  rewrite ?node_15464.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36557 (s : N.State) (i : N.Inputs) :
  R.v36557 (state s) (inputs i) = Zmod.unsigned (N.v36557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36557 s i)) at 1.
  unfold R.v36557, N.v36557.
  unfold R.v6, N.v6.
  rewrite ?node_15525.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36558 (s : N.State) (i : N.Inputs) :
  R.v36558 (state s) (inputs i) = Zmod.unsigned (N.v36558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36558 s i)) at 1.
  unfold R.v36558, N.v36558.
  rewrite ?node_36556.
  rewrite ?node_36557.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36559 (s : N.State) (i : N.Inputs) :
  R.v36559 (state s) (inputs i) = Zmod.unsigned (N.v36559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36559 s i)) at 1.
  unfold R.v36559, N.v36559.
  rewrite ?node_36555.
  rewrite ?node_36558.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36560 (s : N.State) (i : N.Inputs) :
  R.v36560 (state s) (inputs i) = Zmod.unsigned (N.v36560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36560 s i)) at 1.
  unfold R.v36560, N.v36560.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36561 (s : N.State) (i : N.Inputs) :
  R.v36561 (state s) (inputs i) = Zmod.unsigned (N.v36561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36561 s i)) at 1.
  unfold R.v36561, N.v36561.
  rewrite ?node_15468.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36562 (s : N.State) (i : N.Inputs) :
  R.v36562 (state s) (inputs i) = Zmod.unsigned (N.v36562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36562 s i)) at 1.
  unfold R.v36562, N.v36562.
  unfold R.v6, N.v6.
  rewrite !state_r2153_nr_5F2174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2153_nr_5F2174 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36563 (s : N.State) (i : N.Inputs) :
  R.v36563 (state s) (inputs i) = Zmod.unsigned (N.v36563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36563 s i)) at 1.
  unfold R.v36563, N.v36563.
  unfold R.v6, N.v6.
  rewrite ?node_15464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36564 (s : N.State) (i : N.Inputs) :
  R.v36564 (state s) (inputs i) = Zmod.unsigned (N.v36564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36564 s i)) at 1.
  unfold R.v36564, N.v36564.
  rewrite ?node_36562.
  rewrite ?node_36563.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36565 (s : N.State) (i : N.Inputs) :
  R.v36565 (state s) (inputs i) = Zmod.unsigned (N.v36565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36565 s i)) at 1.
  unfold R.v36565, N.v36565.
  unfold R.v16484, N.v16484.
  rewrite ?node_36564.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36566 (s : N.State) (i : N.Inputs) :
  R.v36566 (state s) (inputs i) = Zmod.unsigned (N.v36566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36566 s i)) at 1.
  unfold R.v36566, N.v36566.
  rewrite ?node_36561.
  rewrite ?node_36565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36567 (s : N.State) (i : N.Inputs) :
  R.v36567 (state s) (inputs i) = Zmod.unsigned (N.v36567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36567 s i)) at 1.
  unfold R.v36567, N.v36567.
  unfold R.v6, N.v6.
  rewrite ?node_36566.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36568 (s : N.State) (i : N.Inputs) :
  R.v36568 (state s) (inputs i) = Zmod.unsigned (N.v36568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36568 s i)) at 1.
  unfold R.v36568, N.v36568.
  rewrite ?node_15469.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36569 (s : N.State) (i : N.Inputs) :
  R.v36569 (state s) (inputs i) = Zmod.unsigned (N.v36569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36569 s i)) at 1.
  unfold R.v36569, N.v36569.
  unfold R.v6, N.v6.
  rewrite ?node_15544.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36570 (s : N.State) (i : N.Inputs) :
  R.v36570 (state s) (inputs i) = Zmod.unsigned (N.v36570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36570 s i)) at 1.
  unfold R.v36570, N.v36570.
  rewrite ?node_36568.
  rewrite ?node_36569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36571 (s : N.State) (i : N.Inputs) :
  R.v36571 (state s) (inputs i) = Zmod.unsigned (N.v36571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36571 s i)) at 1.
  unfold R.v36571, N.v36571.
  rewrite ?node_36567.
  rewrite ?node_36570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36572 (s : N.State) (i : N.Inputs) :
  R.v36572 (state s) (inputs i) = Zmod.unsigned (N.v36572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36572 s i)) at 1.
  unfold R.v36572, N.v36572.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36573 (s : N.State) (i : N.Inputs) :
  R.v36573 (state s) (inputs i) = Zmod.unsigned (N.v36573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36573 s i)) at 1.
  unfold R.v36573, N.v36573.
  rewrite ?node_15476.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36574 (s : N.State) (i : N.Inputs) :
  R.v36574 (state s) (inputs i) = Zmod.unsigned (N.v36574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36574 s i)) at 1.
  unfold R.v36574, N.v36574.
  unfold R.v16463, N.v16463.
  rewrite !state_r2157_nr_5F2178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2157_nr_5F2178 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36575 (s : N.State) (i : N.Inputs) :
  R.v36575 (state s) (inputs i) = Zmod.unsigned (N.v36575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36575 s i)) at 1.
  unfold R.v36575, N.v36575.
  unfold R.v16463, N.v16463.
  rewrite !state_r2156_nr_5F2177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2156_nr_5F2177 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36576 (s : N.State) (i : N.Inputs) :
  R.v36576 (state s) (inputs i) = Zmod.unsigned (N.v36576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36576 s i)) at 1.
  unfold R.v36576, N.v36576.
  unfold R.v6, N.v6.
  rewrite !state_r2155_nr_5F2176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2155_nr_5F2176 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36577 (s : N.State) (i : N.Inputs) :
  R.v36577 (state s) (inputs i) = Zmod.unsigned (N.v36577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36577 s i)) at 1.
  unfold R.v36577, N.v36577.
  unfold R.v6, N.v6.
  rewrite !state_r2154_nr_5F2175.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2154_nr_5F2175 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36578 (s : N.State) (i : N.Inputs) :
  R.v36578 (state s) (inputs i) = Zmod.unsigned (N.v36578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36578 s i)) at 1.
  unfold R.v36578, N.v36578.
  rewrite ?node_36576.
  rewrite ?node_36577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36579 (s : N.State) (i : N.Inputs) :
  R.v36579 (state s) (inputs i) = Zmod.unsigned (N.v36579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36579 s i)) at 1.
  unfold R.v36579, N.v36579.
  unfold R.v16484, N.v16484.
  rewrite ?node_36578.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36580 (s : N.State) (i : N.Inputs) :
  R.v36580 (state s) (inputs i) = Zmod.unsigned (N.v36580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36580 s i)) at 1.
  unfold R.v36580, N.v36580.
  rewrite ?node_36573.
  rewrite ?node_36574.
  rewrite ?node_36575.
  rewrite ?node_36579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36581 (s : N.State) (i : N.Inputs) :
  R.v36581 (state s) (inputs i) = Zmod.unsigned (N.v36581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36581 s i)) at 1.
  unfold R.v36581, N.v36581.
  unfold R.v6, N.v6.
  rewrite ?node_36580.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36582 (s : N.State) (i : N.Inputs) :
  R.v36582 (state s) (inputs i) = Zmod.unsigned (N.v36582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36582 s i)) at 1.
  unfold R.v36582, N.v36582.
  rewrite ?node_15477.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36583 (s : N.State) (i : N.Inputs) :
  R.v36583 (state s) (inputs i) = Zmod.unsigned (N.v36583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36583 s i)) at 1.
  unfold R.v36583, N.v36583.
  unfold R.v6, N.v6.
  rewrite ?node_15533.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36584 (s : N.State) (i : N.Inputs) :
  R.v36584 (state s) (inputs i) = Zmod.unsigned (N.v36584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36584 s i)) at 1.
  unfold R.v36584, N.v36584.
  unfold R.v6, N.v6.
  rewrite ?node_15548.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36585 (s : N.State) (i : N.Inputs) :
  R.v36585 (state s) (inputs i) = Zmod.unsigned (N.v36585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36585 s i)) at 1.
  unfold R.v36585, N.v36585.
  rewrite ?node_36582.
  rewrite ?node_36583.
  rewrite ?node_36584.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36586 (s : N.State) (i : N.Inputs) :
  R.v36586 (state s) (inputs i) = Zmod.unsigned (N.v36586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36586 s i)) at 1.
  unfold R.v36586, N.v36586.
  rewrite ?node_36581.
  rewrite ?node_36585.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36587 (s : N.State) (i : N.Inputs) :
  R.v36587 (state s) (inputs i) = Zmod.unsigned (N.v36587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36587 s i)) at 1.
  unfold R.v36587, N.v36587.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36588 (s : N.State) (i : N.Inputs) :
  R.v36588 (state s) (inputs i) = Zmod.unsigned (N.v36588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36588 s i)) at 1.
  unfold R.v36588, N.v36588.
  unfold R.v16463, N.v16463.
  rewrite !state_r2156_nr_5F2177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2156_nr_5F2177 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36589 (s : N.State) (i : N.Inputs) :
  R.v36589 (state s) (inputs i) = Zmod.unsigned (N.v36589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36589 s i)) at 1.
  unfold R.v36589, N.v36589.
  unfold R.v6, N.v6.
  rewrite !state_r2155_nr_5F2176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2155_nr_5F2176 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36590 (s : N.State) (i : N.Inputs) :
  R.v36590 (state s) (inputs i) = Zmod.unsigned (N.v36590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36590 s i)) at 1.
  unfold R.v36590, N.v36590.
  unfold R.v6, N.v6.
  rewrite !state_r2154_nr_5F2175.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2154_nr_5F2175 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36591 (s : N.State) (i : N.Inputs) :
  R.v36591 (state s) (inputs i) = Zmod.unsigned (N.v36591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36591 s i)) at 1.
  unfold R.v36591, N.v36591.
  rewrite ?node_36589.
  rewrite ?node_36590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36592 (s : N.State) (i : N.Inputs) :
  R.v36592 (state s) (inputs i) = Zmod.unsigned (N.v36592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36592 s i)) at 1.
  unfold R.v36592, N.v36592.
  unfold R.v16484, N.v16484.
  rewrite ?node_36591.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36593 (s : N.State) (i : N.Inputs) :
  R.v36593 (state s) (inputs i) = Zmod.unsigned (N.v36593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36593 s i)) at 1.
  unfold R.v36593, N.v36593.
  rewrite ?node_36588.
  rewrite ?node_36592.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36594 (s : N.State) (i : N.Inputs) :
  R.v36594 (state s) (inputs i) = Zmod.unsigned (N.v36594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36594 s i)) at 1.
  unfold R.v36594, N.v36594.
  unfold R.v6, N.v6.
  rewrite ?node_36593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36595 (s : N.State) (i : N.Inputs) :
  R.v36595 (state s) (inputs i) = Zmod.unsigned (N.v36595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36595 s i)) at 1.
  unfold R.v36595, N.v36595.
  rewrite ?node_15472.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36596 (s : N.State) (i : N.Inputs) :
  R.v36596 (state s) (inputs i) = Zmod.unsigned (N.v36596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36596 s i)) at 1.
  unfold R.v36596, N.v36596.
  unfold R.v6, N.v6.
  rewrite ?node_15533.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36597 (s : N.State) (i : N.Inputs) :
  R.v36597 (state s) (inputs i) = Zmod.unsigned (N.v36597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36597 s i)) at 1.
  unfold R.v36597, N.v36597.
  rewrite ?node_36595.
  rewrite ?node_36596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36598 (s : N.State) (i : N.Inputs) :
  R.v36598 (state s) (inputs i) = Zmod.unsigned (N.v36598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36598 s i)) at 1.
  unfold R.v36598, N.v36598.
  rewrite ?node_36594.
  rewrite ?node_36597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36599 (s : N.State) (i : N.Inputs) :
  R.v36599 (state s) (inputs i) = Zmod.unsigned (N.v36599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36599 s i)) at 1.
  unfold R.v36599, N.v36599.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36600 (s : N.State) (i : N.Inputs) :
  R.v36600 (state s) (inputs i) = Zmod.unsigned (N.v36600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36600 s i)) at 1.
  unfold R.v36600, N.v36600.
  rewrite ?node_15476.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36601 (s : N.State) (i : N.Inputs) :
  R.v36601 (state s) (inputs i) = Zmod.unsigned (N.v36601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36601 s i)) at 1.
  unfold R.v36601, N.v36601.
  unfold R.v6, N.v6.
  rewrite !state_r2157_nr_5F2178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2157_nr_5F2178 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36602 (s : N.State) (i : N.Inputs) :
  R.v36602 (state s) (inputs i) = Zmod.unsigned (N.v36602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36602 s i)) at 1.
  unfold R.v36602, N.v36602.
  unfold R.v6, N.v6.
  rewrite ?node_15472.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36603 (s : N.State) (i : N.Inputs) :
  R.v36603 (state s) (inputs i) = Zmod.unsigned (N.v36603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36603 s i)) at 1.
  unfold R.v36603, N.v36603.
  rewrite ?node_36601.
  rewrite ?node_36602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36604 (s : N.State) (i : N.Inputs) :
  R.v36604 (state s) (inputs i) = Zmod.unsigned (N.v36604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36604 s i)) at 1.
  unfold R.v36604, N.v36604.
  unfold R.v16484, N.v16484.
  rewrite ?node_36603.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36605 (s : N.State) (i : N.Inputs) :
  R.v36605 (state s) (inputs i) = Zmod.unsigned (N.v36605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36605 s i)) at 1.
  unfold R.v36605, N.v36605.
  rewrite ?node_36600.
  rewrite ?node_36604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36606 (s : N.State) (i : N.Inputs) :
  R.v36606 (state s) (inputs i) = Zmod.unsigned (N.v36606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36606 s i)) at 1.
  unfold R.v36606, N.v36606.
  unfold R.v6, N.v6.
  rewrite ?node_36605.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36607 (s : N.State) (i : N.Inputs) :
  R.v36607 (state s) (inputs i) = Zmod.unsigned (N.v36607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36607 s i)) at 1.
  unfold R.v36607, N.v36607.
  rewrite ?node_15477.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36608 (s : N.State) (i : N.Inputs) :
  R.v36608 (state s) (inputs i) = Zmod.unsigned (N.v36608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36608 s i)) at 1.
  unfold R.v36608, N.v36608.
  unfold R.v6, N.v6.
  rewrite ?node_15548.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36609 (s : N.State) (i : N.Inputs) :
  R.v36609 (state s) (inputs i) = Zmod.unsigned (N.v36609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36609 s i)) at 1.
  unfold R.v36609, N.v36609.
  rewrite ?node_36607.
  rewrite ?node_36608.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36610 (s : N.State) (i : N.Inputs) :
  R.v36610 (state s) (inputs i) = Zmod.unsigned (N.v36610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36610 s i)) at 1.
  unfold R.v36610, N.v36610.
  rewrite ?node_36606.
  rewrite ?node_36609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36611 (s : N.State) (i : N.Inputs) :
  R.v36611 (state s) (inputs i) = Zmod.unsigned (N.v36611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36611 s i)) at 1.
  unfold R.v36611, N.v36611.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36612 (s : N.State) (i : N.Inputs) :
  R.v36612 (state s) (inputs i) = Zmod.unsigned (N.v36612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36612 s i)) at 1.
  unfold R.v36612, N.v36612.
  rewrite ?node_15518.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36613 (s : N.State) (i : N.Inputs) :
  R.v36613 (state s) (inputs i) = Zmod.unsigned (N.v36613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36613 s i)) at 1.
  unfold R.v36613, N.v36613.
  unfold R.v16463, N.v16463.
  rewrite !state_r2161_nr_5F2182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2161_nr_5F2182 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36614 (s : N.State) (i : N.Inputs) :
  R.v36614 (state s) (inputs i) = Zmod.unsigned (N.v36614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36614 s i)) at 1.
  unfold R.v36614, N.v36614.
  unfold R.v16463, N.v16463.
  rewrite !state_r2160_nr_5F2181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2160_nr_5F2181 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36615 (s : N.State) (i : N.Inputs) :
  R.v36615 (state s) (inputs i) = Zmod.unsigned (N.v36615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36615 s i)) at 1.
  unfold R.v36615, N.v36615.
  unfold R.v6, N.v6.
  rewrite !state_r2159_nr_5F2180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2159_nr_5F2180 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36616 (s : N.State) (i : N.Inputs) :
  R.v36616 (state s) (inputs i) = Zmod.unsigned (N.v36616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36616 s i)) at 1.
  unfold R.v36616, N.v36616.
  unfold R.v6, N.v6.
  rewrite !state_r2158_nr_5F2179.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2158_nr_5F2179 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36617 (s : N.State) (i : N.Inputs) :
  R.v36617 (state s) (inputs i) = Zmod.unsigned (N.v36617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36617 s i)) at 1.
  unfold R.v36617, N.v36617.
  rewrite ?node_36615.
  rewrite ?node_36616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36618 (s : N.State) (i : N.Inputs) :
  R.v36618 (state s) (inputs i) = Zmod.unsigned (N.v36618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36618 s i)) at 1.
  unfold R.v36618, N.v36618.
  unfold R.v16484, N.v16484.
  rewrite ?node_36617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36619 (s : N.State) (i : N.Inputs) :
  R.v36619 (state s) (inputs i) = Zmod.unsigned (N.v36619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36619 s i)) at 1.
  unfold R.v36619, N.v36619.
  rewrite ?node_36612.
  rewrite ?node_36613.
  rewrite ?node_36614.
  rewrite ?node_36618.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36620 (s : N.State) (i : N.Inputs) :
  R.v36620 (state s) (inputs i) = Zmod.unsigned (N.v36620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36620 s i)) at 1.
  unfold R.v36620, N.v36620.
  unfold R.v6, N.v6.
  rewrite ?node_36619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36621 (s : N.State) (i : N.Inputs) :
  R.v36621 (state s) (inputs i) = Zmod.unsigned (N.v36621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36621 s i)) at 1.
  unfold R.v36621, N.v36621.
  rewrite ?node_15519.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36622 (s : N.State) (i : N.Inputs) :
  R.v36622 (state s) (inputs i) = Zmod.unsigned (N.v36622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36622 s i)) at 1.
  unfold R.v36622, N.v36622.
  unfold R.v6, N.v6.
  rewrite ?node_15575.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36623 (s : N.State) (i : N.Inputs) :
  R.v36623 (state s) (inputs i) = Zmod.unsigned (N.v36623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36623 s i)) at 1.
  unfold R.v36623, N.v36623.
  unfold R.v6, N.v6.
  rewrite ?node_15590.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36624 (s : N.State) (i : N.Inputs) :
  R.v36624 (state s) (inputs i) = Zmod.unsigned (N.v36624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36624 s i)) at 1.
  unfold R.v36624, N.v36624.
  rewrite ?node_36621.
  rewrite ?node_36622.
  rewrite ?node_36623.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36625 (s : N.State) (i : N.Inputs) :
  R.v36625 (state s) (inputs i) = Zmod.unsigned (N.v36625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36625 s i)) at 1.
  unfold R.v36625, N.v36625.
  rewrite ?node_36620.
  rewrite ?node_36624.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36626 (s : N.State) (i : N.Inputs) :
  R.v36626 (state s) (inputs i) = Zmod.unsigned (N.v36626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36626 s i)) at 1.
  unfold R.v36626, N.v36626.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36627 (s : N.State) (i : N.Inputs) :
  R.v36627 (state s) (inputs i) = Zmod.unsigned (N.v36627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36627 s i)) at 1.
  unfold R.v36627, N.v36627.
  unfold R.v16463, N.v16463.
  rewrite !state_r2160_nr_5F2181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2160_nr_5F2181 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36628 (s : N.State) (i : N.Inputs) :
  R.v36628 (state s) (inputs i) = Zmod.unsigned (N.v36628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36628 s i)) at 1.
  unfold R.v36628, N.v36628.
  unfold R.v6, N.v6.
  rewrite !state_r2159_nr_5F2180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2159_nr_5F2180 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36629 (s : N.State) (i : N.Inputs) :
  R.v36629 (state s) (inputs i) = Zmod.unsigned (N.v36629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36629 s i)) at 1.
  unfold R.v36629, N.v36629.
  unfold R.v6, N.v6.
  rewrite !state_r2158_nr_5F2179.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2158_nr_5F2179 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36630 (s : N.State) (i : N.Inputs) :
  R.v36630 (state s) (inputs i) = Zmod.unsigned (N.v36630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36630 s i)) at 1.
  unfold R.v36630, N.v36630.
  rewrite ?node_36628.
  rewrite ?node_36629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36631 (s : N.State) (i : N.Inputs) :
  R.v36631 (state s) (inputs i) = Zmod.unsigned (N.v36631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36631 s i)) at 1.
  unfold R.v36631, N.v36631.
  unfold R.v16484, N.v16484.
  rewrite ?node_36630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36632 (s : N.State) (i : N.Inputs) :
  R.v36632 (state s) (inputs i) = Zmod.unsigned (N.v36632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36632 s i)) at 1.
  unfold R.v36632, N.v36632.
  rewrite ?node_36627.
  rewrite ?node_36631.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36633 (s : N.State) (i : N.Inputs) :
  R.v36633 (state s) (inputs i) = Zmod.unsigned (N.v36633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36633 s i)) at 1.
  unfold R.v36633, N.v36633.
  unfold R.v6, N.v6.
  rewrite ?node_36632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36634 (s : N.State) (i : N.Inputs) :
  R.v36634 (state s) (inputs i) = Zmod.unsigned (N.v36634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36634 s i)) at 1.
  unfold R.v36634, N.v36634.
  rewrite ?node_15515.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36635 (s : N.State) (i : N.Inputs) :
  R.v36635 (state s) (inputs i) = Zmod.unsigned (N.v36635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36635 s i)) at 1.
  unfold R.v36635, N.v36635.
  unfold R.v6, N.v6.
  rewrite ?node_15575.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36636 (s : N.State) (i : N.Inputs) :
  R.v36636 (state s) (inputs i) = Zmod.unsigned (N.v36636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36636 s i)) at 1.
  unfold R.v36636, N.v36636.
  rewrite ?node_36634.
  rewrite ?node_36635.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36637 (s : N.State) (i : N.Inputs) :
  R.v36637 (state s) (inputs i) = Zmod.unsigned (N.v36637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36637 s i)) at 1.
  unfold R.v36637, N.v36637.
  rewrite ?node_36633.
  rewrite ?node_36636.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36638 (s : N.State) (i : N.Inputs) :
  R.v36638 (state s) (inputs i) = Zmod.unsigned (N.v36638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36638 s i)) at 1.
  unfold R.v36638, N.v36638.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36639 (s : N.State) (i : N.Inputs) :
  R.v36639 (state s) (inputs i) = Zmod.unsigned (N.v36639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36639 s i)) at 1.
  unfold R.v36639, N.v36639.
  rewrite ?node_15518.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36640 (s : N.State) (i : N.Inputs) :
  R.v36640 (state s) (inputs i) = Zmod.unsigned (N.v36640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36640 s i)) at 1.
  unfold R.v36640, N.v36640.
  unfold R.v6, N.v6.
  rewrite !state_r2161_nr_5F2182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2161_nr_5F2182 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36641 (s : N.State) (i : N.Inputs) :
  R.v36641 (state s) (inputs i) = Zmod.unsigned (N.v36641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36641 s i)) at 1.
  unfold R.v36641, N.v36641.
  unfold R.v6, N.v6.
  rewrite ?node_15515.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36642 (s : N.State) (i : N.Inputs) :
  R.v36642 (state s) (inputs i) = Zmod.unsigned (N.v36642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36642 s i)) at 1.
  unfold R.v36642, N.v36642.
  rewrite ?node_36640.
  rewrite ?node_36641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36643 (s : N.State) (i : N.Inputs) :
  R.v36643 (state s) (inputs i) = Zmod.unsigned (N.v36643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36643 s i)) at 1.
  unfold R.v36643, N.v36643.
  unfold R.v16484, N.v16484.
  rewrite ?node_36642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36644 (s : N.State) (i : N.Inputs) :
  R.v36644 (state s) (inputs i) = Zmod.unsigned (N.v36644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36644 s i)) at 1.
  unfold R.v36644, N.v36644.
  rewrite ?node_36639.
  rewrite ?node_36643.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36645 (s : N.State) (i : N.Inputs) :
  R.v36645 (state s) (inputs i) = Zmod.unsigned (N.v36645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36645 s i)) at 1.
  unfold R.v36645, N.v36645.
  unfold R.v6, N.v6.
  rewrite ?node_36644.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36646 (s : N.State) (i : N.Inputs) :
  R.v36646 (state s) (inputs i) = Zmod.unsigned (N.v36646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36646 s i)) at 1.
  unfold R.v36646, N.v36646.
  rewrite ?node_15519.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36647 (s : N.State) (i : N.Inputs) :
  R.v36647 (state s) (inputs i) = Zmod.unsigned (N.v36647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36647 s i)) at 1.
  unfold R.v36647, N.v36647.
  unfold R.v6, N.v6.
  rewrite ?node_15590.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36648 (s : N.State) (i : N.Inputs) :
  R.v36648 (state s) (inputs i) = Zmod.unsigned (N.v36648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36648 s i)) at 1.
  unfold R.v36648, N.v36648.
  rewrite ?node_36646.
  rewrite ?node_36647.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36649 (s : N.State) (i : N.Inputs) :
  R.v36649 (state s) (inputs i) = Zmod.unsigned (N.v36649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36649 s i)) at 1.
  unfold R.v36649, N.v36649.
  rewrite ?node_36645.
  rewrite ?node_36648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36650 (s : N.State) (i : N.Inputs) :
  R.v36650 (state s) (inputs i) = Zmod.unsigned (N.v36650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36650 s i)) at 1.
  unfold R.v36650, N.v36650.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36651 (s : N.State) (i : N.Inputs) :
  R.v36651 (state s) (inputs i) = Zmod.unsigned (N.v36651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36651 s i)) at 1.
  unfold R.v36651, N.v36651.
  rewrite ?node_15525.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36652 (s : N.State) (i : N.Inputs) :
  R.v36652 (state s) (inputs i) = Zmod.unsigned (N.v36652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36652 s i)) at 1.
  unfold R.v36652, N.v36652.
  unfold R.v16463, N.v16463.
  rewrite !state_r2165_nr_5F2186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2165_nr_5F2186 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36653 (s : N.State) (i : N.Inputs) :
  R.v36653 (state s) (inputs i) = Zmod.unsigned (N.v36653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36653 s i)) at 1.
  unfold R.v36653, N.v36653.
  unfold R.v16463, N.v16463.
  rewrite !state_r2164_nr_5F2185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2164_nr_5F2185 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36654 (s : N.State) (i : N.Inputs) :
  R.v36654 (state s) (inputs i) = Zmod.unsigned (N.v36654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36654 s i)) at 1.
  unfold R.v36654, N.v36654.
  unfold R.v6, N.v6.
  rewrite !state_r2163_nr_5F2184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2163_nr_5F2184 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36655 (s : N.State) (i : N.Inputs) :
  R.v36655 (state s) (inputs i) = Zmod.unsigned (N.v36655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36655 s i)) at 1.
  unfold R.v36655, N.v36655.
  unfold R.v6, N.v6.
  rewrite !state_r2162_nr_5F2183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2162_nr_5F2183 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36656 (s : N.State) (i : N.Inputs) :
  R.v36656 (state s) (inputs i) = Zmod.unsigned (N.v36656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36656 s i)) at 1.
  unfold R.v36656, N.v36656.
  rewrite ?node_36654.
  rewrite ?node_36655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36657 (s : N.State) (i : N.Inputs) :
  R.v36657 (state s) (inputs i) = Zmod.unsigned (N.v36657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36657 s i)) at 1.
  unfold R.v36657, N.v36657.
  unfold R.v16484, N.v16484.
  rewrite ?node_36656.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36658 (s : N.State) (i : N.Inputs) :
  R.v36658 (state s) (inputs i) = Zmod.unsigned (N.v36658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36658 s i)) at 1.
  unfold R.v36658, N.v36658.
  rewrite ?node_36651.
  rewrite ?node_36652.
  rewrite ?node_36653.
  rewrite ?node_36657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36659 (s : N.State) (i : N.Inputs) :
  R.v36659 (state s) (inputs i) = Zmod.unsigned (N.v36659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36659 s i)) at 1.
  unfold R.v36659, N.v36659.
  unfold R.v6, N.v6.
  rewrite ?node_36658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36660 (s : N.State) (i : N.Inputs) :
  R.v36660 (state s) (inputs i) = Zmod.unsigned (N.v36660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36660 s i)) at 1.
  unfold R.v36660, N.v36660.
  rewrite ?node_15526.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36661 (s : N.State) (i : N.Inputs) :
  R.v36661 (state s) (inputs i) = Zmod.unsigned (N.v36661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36661 s i)) at 1.
  unfold R.v36661, N.v36661.
  unfold R.v6, N.v6.
  rewrite ?node_15582.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36662 (s : N.State) (i : N.Inputs) :
  R.v36662 (state s) (inputs i) = Zmod.unsigned (N.v36662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36662 s i)) at 1.
  unfold R.v36662, N.v36662.
  unfold R.v6, N.v6.
  rewrite ?node_15598.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36663 (s : N.State) (i : N.Inputs) :
  R.v36663 (state s) (inputs i) = Zmod.unsigned (N.v36663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36663 s i)) at 1.
  unfold R.v36663, N.v36663.
  rewrite ?node_36660.
  rewrite ?node_36661.
  rewrite ?node_36662.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36664 (s : N.State) (i : N.Inputs) :
  R.v36664 (state s) (inputs i) = Zmod.unsigned (N.v36664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36664 s i)) at 1.
  unfold R.v36664, N.v36664.
  rewrite ?node_36659.
  rewrite ?node_36663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36665 (s : N.State) (i : N.Inputs) :
  R.v36665 (state s) (inputs i) = Zmod.unsigned (N.v36665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36665 s i)) at 1.
  unfold R.v36665, N.v36665.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36666 (s : N.State) (i : N.Inputs) :
  R.v36666 (state s) (inputs i) = Zmod.unsigned (N.v36666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36666 s i)) at 1.
  unfold R.v36666, N.v36666.
  unfold R.v16463, N.v16463.
  rewrite !state_r2164_nr_5F2185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2164_nr_5F2185 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36667 (s : N.State) (i : N.Inputs) :
  R.v36667 (state s) (inputs i) = Zmod.unsigned (N.v36667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36667 s i)) at 1.
  unfold R.v36667, N.v36667.
  unfold R.v6, N.v6.
  rewrite !state_r2163_nr_5F2184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2163_nr_5F2184 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36668 (s : N.State) (i : N.Inputs) :
  R.v36668 (state s) (inputs i) = Zmod.unsigned (N.v36668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36668 s i)) at 1.
  unfold R.v36668, N.v36668.
  unfold R.v6, N.v6.
  rewrite !state_r2162_nr_5F2183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2162_nr_5F2183 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36669 (s : N.State) (i : N.Inputs) :
  R.v36669 (state s) (inputs i) = Zmod.unsigned (N.v36669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36669 s i)) at 1.
  unfold R.v36669, N.v36669.
  rewrite ?node_36667.
  rewrite ?node_36668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36670 (s : N.State) (i : N.Inputs) :
  R.v36670 (state s) (inputs i) = Zmod.unsigned (N.v36670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36670 s i)) at 1.
  unfold R.v36670, N.v36670.
  unfold R.v16484, N.v16484.
  rewrite ?node_36669.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36671 (s : N.State) (i : N.Inputs) :
  R.v36671 (state s) (inputs i) = Zmod.unsigned (N.v36671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36671 s i)) at 1.
  unfold R.v36671, N.v36671.
  rewrite ?node_36666.
  rewrite ?node_36670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36672 (s : N.State) (i : N.Inputs) :
  R.v36672 (state s) (inputs i) = Zmod.unsigned (N.v36672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36672 s i)) at 1.
  unfold R.v36672, N.v36672.
  unfold R.v6, N.v6.
  rewrite ?node_36671.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36673 (s : N.State) (i : N.Inputs) :
  R.v36673 (state s) (inputs i) = Zmod.unsigned (N.v36673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36673 s i)) at 1.
  unfold R.v36673, N.v36673.
  rewrite ?node_15521.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36674 (s : N.State) (i : N.Inputs) :
  R.v36674 (state s) (inputs i) = Zmod.unsigned (N.v36674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36674 s i)) at 1.
  unfold R.v36674, N.v36674.
  unfold R.v6, N.v6.
  rewrite ?node_15582.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36675 (s : N.State) (i : N.Inputs) :
  R.v36675 (state s) (inputs i) = Zmod.unsigned (N.v36675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36675 s i)) at 1.
  unfold R.v36675, N.v36675.
  rewrite ?node_36673.
  rewrite ?node_36674.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36676 (s : N.State) (i : N.Inputs) :
  R.v36676 (state s) (inputs i) = Zmod.unsigned (N.v36676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36676 s i)) at 1.
  unfold R.v36676, N.v36676.
  rewrite ?node_36672.
  rewrite ?node_36675.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36677 (s : N.State) (i : N.Inputs) :
  R.v36677 (state s) (inputs i) = Zmod.unsigned (N.v36677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36677 s i)) at 1.
  unfold R.v36677, N.v36677.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36678 (s : N.State) (i : N.Inputs) :
  R.v36678 (state s) (inputs i) = Zmod.unsigned (N.v36678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36678 s i)) at 1.
  unfold R.v36678, N.v36678.
  rewrite ?node_15525.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36679 (s : N.State) (i : N.Inputs) :
  R.v36679 (state s) (inputs i) = Zmod.unsigned (N.v36679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36679 s i)) at 1.
  unfold R.v36679, N.v36679.
  unfold R.v6, N.v6.
  rewrite !state_r2165_nr_5F2186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2165_nr_5F2186 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36680 (s : N.State) (i : N.Inputs) :
  R.v36680 (state s) (inputs i) = Zmod.unsigned (N.v36680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36680 s i)) at 1.
  unfold R.v36680, N.v36680.
  unfold R.v6, N.v6.
  rewrite ?node_15521.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36681 (s : N.State) (i : N.Inputs) :
  R.v36681 (state s) (inputs i) = Zmod.unsigned (N.v36681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36681 s i)) at 1.
  unfold R.v36681, N.v36681.
  rewrite ?node_36679.
  rewrite ?node_36680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36682 (s : N.State) (i : N.Inputs) :
  R.v36682 (state s) (inputs i) = Zmod.unsigned (N.v36682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36682 s i)) at 1.
  unfold R.v36682, N.v36682.
  unfold R.v16484, N.v16484.
  rewrite ?node_36681.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36683 (s : N.State) (i : N.Inputs) :
  R.v36683 (state s) (inputs i) = Zmod.unsigned (N.v36683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36683 s i)) at 1.
  unfold R.v36683, N.v36683.
  rewrite ?node_36678.
  rewrite ?node_36682.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36684 (s : N.State) (i : N.Inputs) :
  R.v36684 (state s) (inputs i) = Zmod.unsigned (N.v36684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36684 s i)) at 1.
  unfold R.v36684, N.v36684.
  unfold R.v6, N.v6.
  rewrite ?node_36683.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36685 (s : N.State) (i : N.Inputs) :
  R.v36685 (state s) (inputs i) = Zmod.unsigned (N.v36685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36685 s i)) at 1.
  unfold R.v36685, N.v36685.
  rewrite ?node_15526.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36686 (s : N.State) (i : N.Inputs) :
  R.v36686 (state s) (inputs i) = Zmod.unsigned (N.v36686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36686 s i)) at 1.
  unfold R.v36686, N.v36686.
  unfold R.v6, N.v6.
  rewrite ?node_15598.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36687 (s : N.State) (i : N.Inputs) :
  R.v36687 (state s) (inputs i) = Zmod.unsigned (N.v36687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36687 s i)) at 1.
  unfold R.v36687, N.v36687.
  rewrite ?node_36685.
  rewrite ?node_36686.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36688 (s : N.State) (i : N.Inputs) :
  R.v36688 (state s) (inputs i) = Zmod.unsigned (N.v36688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36688 s i)) at 1.
  unfold R.v36688, N.v36688.
  rewrite ?node_36684.
  rewrite ?node_36687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36689 (s : N.State) (i : N.Inputs) :
  R.v36689 (state s) (inputs i) = Zmod.unsigned (N.v36689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36689 s i)) at 1.
  unfold R.v36689, N.v36689.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36690 (s : N.State) (i : N.Inputs) :
  R.v36690 (state s) (inputs i) = Zmod.unsigned (N.v36690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36690 s i)) at 1.
  unfold R.v36690, N.v36690.
  unfold R.v16463, N.v16463.
  rewrite !state_r2168_nr_5F2189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2168_nr_5F2189 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36691 (s : N.State) (i : N.Inputs) :
  R.v36691 (state s) (inputs i) = Zmod.unsigned (N.v36691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36691 s i)) at 1.
  unfold R.v36691, N.v36691.
  unfold R.v6, N.v6.
  rewrite !state_r2167_nr_5F2188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2167_nr_5F2188 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36692 (s : N.State) (i : N.Inputs) :
  R.v36692 (state s) (inputs i) = Zmod.unsigned (N.v36692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36692 s i)) at 1.
  unfold R.v36692, N.v36692.
  unfold R.v6, N.v6.
  rewrite !state_r2166_nr_5F2187.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2166_nr_5F2187 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36693 (s : N.State) (i : N.Inputs) :
  R.v36693 (state s) (inputs i) = Zmod.unsigned (N.v36693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36693 s i)) at 1.
  unfold R.v36693, N.v36693.
  rewrite ?node_36691.
  rewrite ?node_36692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36694 (s : N.State) (i : N.Inputs) :
  R.v36694 (state s) (inputs i) = Zmod.unsigned (N.v36694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36694 s i)) at 1.
  unfold R.v36694, N.v36694.
  unfold R.v16484, N.v16484.
  rewrite ?node_36693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36695 (s : N.State) (i : N.Inputs) :
  R.v36695 (state s) (inputs i) = Zmod.unsigned (N.v36695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36695 s i)) at 1.
  unfold R.v36695, N.v36695.
  rewrite ?node_36690.
  rewrite ?node_36694.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36696 (s : N.State) (i : N.Inputs) :
  R.v36696 (state s) (inputs i) = Zmod.unsigned (N.v36696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36696 s i)) at 1.
  unfold R.v36696, N.v36696.
  unfold R.v6, N.v6.
  rewrite ?node_36695.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36697 (s : N.State) (i : N.Inputs) :
  R.v36697 (state s) (inputs i) = Zmod.unsigned (N.v36697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36697 s i)) at 1.
  unfold R.v36697, N.v36697.
  rewrite ?node_15529.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36698 (s : N.State) (i : N.Inputs) :
  R.v36698 (state s) (inputs i) = Zmod.unsigned (N.v36698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36698 s i)) at 1.
  unfold R.v36698, N.v36698.
  unfold R.v6, N.v6.
  rewrite ?node_15601.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36699 (s : N.State) (i : N.Inputs) :
  R.v36699 (state s) (inputs i) = Zmod.unsigned (N.v36699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36699 s i)) at 1.
  unfold R.v36699, N.v36699.
  rewrite ?node_36697.
  rewrite ?node_36698.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36700 (s : N.State) (i : N.Inputs) :
  R.v36700 (state s) (inputs i) = Zmod.unsigned (N.v36700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36700 s i)) at 1.
  unfold R.v36700, N.v36700.
  rewrite ?node_36696.
  rewrite ?node_36699.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36701 (s : N.State) (i : N.Inputs) :
  R.v36701 (state s) (inputs i) = Zmod.unsigned (N.v36701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36701 s i)) at 1.
  unfold R.v36701, N.v36701.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36702 (s : N.State) (i : N.Inputs) :
  R.v36702 (state s) (inputs i) = Zmod.unsigned (N.v36702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36702 s i)) at 1.
  unfold R.v36702, N.v36702.
  rewrite ?node_15575.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36703 (s : N.State) (i : N.Inputs) :
  R.v36703 (state s) (inputs i) = Zmod.unsigned (N.v36703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36703 s i)) at 1.
  unfold R.v36703, N.v36703.
  unfold R.v16463, N.v16463.
  rewrite !state_r2171_nr_5F2193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2171_nr_5F2193 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36704 (s : N.State) (i : N.Inputs) :
  R.v36704 (state s) (inputs i) = Zmod.unsigned (N.v36704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36704 s i)) at 1.
  unfold R.v36704, N.v36704.
  unfold R.v16463, N.v16463.
  rewrite !state_r2170_nr_5F2192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2170_nr_5F2192 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36705 (s : N.State) (i : N.Inputs) :
  R.v36705 (state s) (inputs i) = Zmod.unsigned (N.v36705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36705 s i)) at 1.
  unfold R.v36705, N.v36705.
  unfold R.v6, N.v6.
  rewrite !state_r2169_nr_5F2191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2169_nr_5F2191 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36706 (s : N.State) (i : N.Inputs) :
  R.v36706 (state s) (inputs i) = Zmod.unsigned (N.v36706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36706 s i)) at 1.
  unfold R.v36706, N.v36706.
  unfold R.v19, N.v19.
  rewrite ?node_36705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36707 (s : N.State) (i : N.Inputs) :
  R.v36707 (state s) (inputs i) = Zmod.unsigned (N.v36707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36707 s i)) at 1.
  unfold R.v36707, N.v36707.
  unfold R.v16484, N.v16484.
  rewrite ?node_36706.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36708 (s : N.State) (i : N.Inputs) :
  R.v36708 (state s) (inputs i) = Zmod.unsigned (N.v36708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36708 s i)) at 1.
  unfold R.v36708, N.v36708.
  rewrite ?node_36702.
  rewrite ?node_36703.
  rewrite ?node_36704.
  rewrite ?node_36707.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36709 (s : N.State) (i : N.Inputs) :
  R.v36709 (state s) (inputs i) = Zmod.unsigned (N.v36709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36709 s i)) at 1.
  unfold R.v36709, N.v36709.
  unfold R.v6, N.v6.
  rewrite ?node_36708.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36710 (s : N.State) (i : N.Inputs) :
  R.v36710 (state s) (inputs i) = Zmod.unsigned (N.v36710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36710 s i)) at 1.
  unfold R.v36710, N.v36710.
  rewrite ?node_15576.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36711 (s : N.State) (i : N.Inputs) :
  R.v36711 (state s) (inputs i) = Zmod.unsigned (N.v36711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36711 s i)) at 1.
  unfold R.v36711, N.v36711.
  unfold R.v6, N.v6.
  rewrite ?node_15629.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36712 (s : N.State) (i : N.Inputs) :
  R.v36712 (state s) (inputs i) = Zmod.unsigned (N.v36712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36712 s i)) at 1.
  unfold R.v36712, N.v36712.
  unfold R.v6, N.v6.
  rewrite ?node_15643.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36713 (s : N.State) (i : N.Inputs) :
  R.v36713 (state s) (inputs i) = Zmod.unsigned (N.v36713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36713 s i)) at 1.
  unfold R.v36713, N.v36713.
  rewrite ?node_36710.
  rewrite ?node_36711.
  rewrite ?node_36712.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36714 (s : N.State) (i : N.Inputs) :
  R.v36714 (state s) (inputs i) = Zmod.unsigned (N.v36714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36714 s i)) at 1.
  unfold R.v36714, N.v36714.
  rewrite ?node_36709.
  rewrite ?node_36713.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36715 (s : N.State) (i : N.Inputs) :
  R.v36715 (state s) (inputs i) = Zmod.unsigned (N.v36715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36715 s i)) at 1.
  unfold R.v36715, N.v36715.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36716 (s : N.State) (i : N.Inputs) :
  R.v36716 (state s) (inputs i) = Zmod.unsigned (N.v36716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36716 s i)) at 1.
  unfold R.v36716, N.v36716.
  unfold R.v16463, N.v16463.
  rewrite !state_r2170_nr_5F2192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2170_nr_5F2192 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36717 (s : N.State) (i : N.Inputs) :
  R.v36717 (state s) (inputs i) = Zmod.unsigned (N.v36717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36717 s i)) at 1.
  unfold R.v36717, N.v36717.
  unfold R.v6, N.v6.
  rewrite !state_r2169_nr_5F2191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2169_nr_5F2191 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36718 (s : N.State) (i : N.Inputs) :
  R.v36718 (state s) (inputs i) = Zmod.unsigned (N.v36718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36718 s i)) at 1.
  unfold R.v36718, N.v36718.
  unfold R.v19, N.v19.
  rewrite ?node_36717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36719 (s : N.State) (i : N.Inputs) :
  R.v36719 (state s) (inputs i) = Zmod.unsigned (N.v36719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36719 s i)) at 1.
  unfold R.v36719, N.v36719.
  unfold R.v16484, N.v16484.
  rewrite ?node_36718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36720 (s : N.State) (i : N.Inputs) :
  R.v36720 (state s) (inputs i) = Zmod.unsigned (N.v36720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36720 s i)) at 1.
  unfold R.v36720, N.v36720.
  rewrite ?node_36716.
  rewrite ?node_36719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36721 (s : N.State) (i : N.Inputs) :
  R.v36721 (state s) (inputs i) = Zmod.unsigned (N.v36721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36721 s i)) at 1.
  unfold R.v36721, N.v36721.
  unfold R.v6, N.v6.
  rewrite ?node_36720.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36722 (s : N.State) (i : N.Inputs) :
  R.v36722 (state s) (inputs i) = Zmod.unsigned (N.v36722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36722 s i)) at 1.
  unfold R.v36722, N.v36722.
  rewrite ?node_15571.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36723 (s : N.State) (i : N.Inputs) :
  R.v36723 (state s) (inputs i) = Zmod.unsigned (N.v36723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36723 s i)) at 1.
  unfold R.v36723, N.v36723.
  unfold R.v6, N.v6.
  rewrite ?node_15629.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36724 (s : N.State) (i : N.Inputs) :
  R.v36724 (state s) (inputs i) = Zmod.unsigned (N.v36724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36724 s i)) at 1.
  unfold R.v36724, N.v36724.
  rewrite ?node_36722.
  rewrite ?node_36723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36725 (s : N.State) (i : N.Inputs) :
  R.v36725 (state s) (inputs i) = Zmod.unsigned (N.v36725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36725 s i)) at 1.
  unfold R.v36725, N.v36725.
  rewrite ?node_36721.
  rewrite ?node_36724.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36726 (s : N.State) (i : N.Inputs) :
  R.v36726 (state s) (inputs i) = Zmod.unsigned (N.v36726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36726 s i)) at 1.
  unfold R.v36726, N.v36726.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36727 (s : N.State) (i : N.Inputs) :
  R.v36727 (state s) (inputs i) = Zmod.unsigned (N.v36727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36727 s i)) at 1.
  unfold R.v36727, N.v36727.
  rewrite ?node_15575.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36728 (s : N.State) (i : N.Inputs) :
  R.v36728 (state s) (inputs i) = Zmod.unsigned (N.v36728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36728 s i)) at 1.
  unfold R.v36728, N.v36728.
  unfold R.v6, N.v6.
  rewrite !state_r2171_nr_5F2193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2171_nr_5F2193 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36729 (s : N.State) (i : N.Inputs) :
  R.v36729 (state s) (inputs i) = Zmod.unsigned (N.v36729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36729 s i)) at 1.
  unfold R.v36729, N.v36729.
  unfold R.v6, N.v6.
  rewrite ?node_15571.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36730 (s : N.State) (i : N.Inputs) :
  R.v36730 (state s) (inputs i) = Zmod.unsigned (N.v36730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36730 s i)) at 1.
  unfold R.v36730, N.v36730.
  rewrite ?node_36728.
  rewrite ?node_36729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36731 (s : N.State) (i : N.Inputs) :
  R.v36731 (state s) (inputs i) = Zmod.unsigned (N.v36731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36731 s i)) at 1.
  unfold R.v36731, N.v36731.
  unfold R.v16484, N.v16484.
  rewrite ?node_36730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36732 (s : N.State) (i : N.Inputs) :
  R.v36732 (state s) (inputs i) = Zmod.unsigned (N.v36732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36732 s i)) at 1.
  unfold R.v36732, N.v36732.
  rewrite ?node_36727.
  rewrite ?node_36731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36733 (s : N.State) (i : N.Inputs) :
  R.v36733 (state s) (inputs i) = Zmod.unsigned (N.v36733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36733 s i)) at 1.
  unfold R.v36733, N.v36733.
  unfold R.v6, N.v6.
  rewrite ?node_36732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36734 (s : N.State) (i : N.Inputs) :
  R.v36734 (state s) (inputs i) = Zmod.unsigned (N.v36734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36734 s i)) at 1.
  unfold R.v36734, N.v36734.
  rewrite ?node_15576.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36735 (s : N.State) (i : N.Inputs) :
  R.v36735 (state s) (inputs i) = Zmod.unsigned (N.v36735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36735 s i)) at 1.
  unfold R.v36735, N.v36735.
  unfold R.v6, N.v6.
  rewrite ?node_15643.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36736 (s : N.State) (i : N.Inputs) :
  R.v36736 (state s) (inputs i) = Zmod.unsigned (N.v36736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36736 s i)) at 1.
  unfold R.v36736, N.v36736.
  rewrite ?node_36734.
  rewrite ?node_36735.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36737 (s : N.State) (i : N.Inputs) :
  R.v36737 (state s) (inputs i) = Zmod.unsigned (N.v36737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36737 s i)) at 1.
  unfold R.v36737, N.v36737.
  rewrite ?node_36733.
  rewrite ?node_36736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36738 (s : N.State) (i : N.Inputs) :
  R.v36738 (state s) (inputs i) = Zmod.unsigned (N.v36738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36738 s i)) at 1.
  unfold R.v36738, N.v36738.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36739 (s : N.State) (i : N.Inputs) :
  R.v36739 (state s) (inputs i) = Zmod.unsigned (N.v36739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36739 s i)) at 1.
  unfold R.v36739, N.v36739.
  rewrite ?node_15582.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36740 (s : N.State) (i : N.Inputs) :
  R.v36740 (state s) (inputs i) = Zmod.unsigned (N.v36740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36740 s i)) at 1.
  unfold R.v36740, N.v36740.
  unfold R.v16463, N.v16463.
  rewrite !state_r2175_nr_5F2197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2175_nr_5F2197 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36741 (s : N.State) (i : N.Inputs) :
  R.v36741 (state s) (inputs i) = Zmod.unsigned (N.v36741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36741 s i)) at 1.
  unfold R.v36741, N.v36741.
  unfold R.v16463, N.v16463.
  rewrite !state_r2174_nr_5F2196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2174_nr_5F2196 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36742 (s : N.State) (i : N.Inputs) :
  R.v36742 (state s) (inputs i) = Zmod.unsigned (N.v36742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36742 s i)) at 1.
  unfold R.v36742, N.v36742.
  unfold R.v6, N.v6.
  rewrite !state_r2173_nr_5F2195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2173_nr_5F2195 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36743 (s : N.State) (i : N.Inputs) :
  R.v36743 (state s) (inputs i) = Zmod.unsigned (N.v36743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36743 s i)) at 1.
  unfold R.v36743, N.v36743.
  unfold R.v6, N.v6.
  rewrite !state_r2172_nr_5F2194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2172_nr_5F2194 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36744 (s : N.State) (i : N.Inputs) :
  R.v36744 (state s) (inputs i) = Zmod.unsigned (N.v36744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36744 s i)) at 1.
  unfold R.v36744, N.v36744.
  rewrite ?node_36742.
  rewrite ?node_36743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36745 (s : N.State) (i : N.Inputs) :
  R.v36745 (state s) (inputs i) = Zmod.unsigned (N.v36745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36745 s i)) at 1.
  unfold R.v36745, N.v36745.
  unfold R.v16484, N.v16484.
  rewrite ?node_36744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36746 (s : N.State) (i : N.Inputs) :
  R.v36746 (state s) (inputs i) = Zmod.unsigned (N.v36746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36746 s i)) at 1.
  unfold R.v36746, N.v36746.
  rewrite ?node_36739.
  rewrite ?node_36740.
  rewrite ?node_36741.
  rewrite ?node_36745.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36747 (s : N.State) (i : N.Inputs) :
  R.v36747 (state s) (inputs i) = Zmod.unsigned (N.v36747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36747 s i)) at 1.
  unfold R.v36747, N.v36747.
  unfold R.v6, N.v6.
  rewrite ?node_36746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36748 (s : N.State) (i : N.Inputs) :
  R.v36748 (state s) (inputs i) = Zmod.unsigned (N.v36748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36748 s i)) at 1.
  unfold R.v36748, N.v36748.
  rewrite ?node_15583.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36749 (s : N.State) (i : N.Inputs) :
  R.v36749 (state s) (inputs i) = Zmod.unsigned (N.v36749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36749 s i)) at 1.
  unfold R.v36749, N.v36749.
  unfold R.v6, N.v6.
  rewrite ?node_15636.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36750 (s : N.State) (i : N.Inputs) :
  R.v36750 (state s) (inputs i) = Zmod.unsigned (N.v36750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36750 s i)) at 1.
  unfold R.v36750, N.v36750.
  unfold R.v6, N.v6.
  rewrite ?node_15651.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36751 (s : N.State) (i : N.Inputs) :
  R.v36751 (state s) (inputs i) = Zmod.unsigned (N.v36751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36751 s i)) at 1.
  unfold R.v36751, N.v36751.
  rewrite ?node_36748.
  rewrite ?node_36749.
  rewrite ?node_36750.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36752 (s : N.State) (i : N.Inputs) :
  R.v36752 (state s) (inputs i) = Zmod.unsigned (N.v36752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36752 s i)) at 1.
  unfold R.v36752, N.v36752.
  rewrite ?node_36747.
  rewrite ?node_36751.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36753 (s : N.State) (i : N.Inputs) :
  R.v36753 (state s) (inputs i) = Zmod.unsigned (N.v36753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36753 s i)) at 1.
  unfold R.v36753, N.v36753.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36754 (s : N.State) (i : N.Inputs) :
  R.v36754 (state s) (inputs i) = Zmod.unsigned (N.v36754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36754 s i)) at 1.
  unfold R.v36754, N.v36754.
  unfold R.v16463, N.v16463.
  rewrite !state_r2174_nr_5F2196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2174_nr_5F2196 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36755 (s : N.State) (i : N.Inputs) :
  R.v36755 (state s) (inputs i) = Zmod.unsigned (N.v36755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36755 s i)) at 1.
  unfold R.v36755, N.v36755.
  unfold R.v6, N.v6.
  rewrite !state_r2173_nr_5F2195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2173_nr_5F2195 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36756 (s : N.State) (i : N.Inputs) :
  R.v36756 (state s) (inputs i) = Zmod.unsigned (N.v36756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36756 s i)) at 1.
  unfold R.v36756, N.v36756.
  unfold R.v6, N.v6.
  rewrite !state_r2172_nr_5F2194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2172_nr_5F2194 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36757 (s : N.State) (i : N.Inputs) :
  R.v36757 (state s) (inputs i) = Zmod.unsigned (N.v36757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36757 s i)) at 1.
  unfold R.v36757, N.v36757.
  rewrite ?node_36755.
  rewrite ?node_36756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36758 (s : N.State) (i : N.Inputs) :
  R.v36758 (state s) (inputs i) = Zmod.unsigned (N.v36758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36758 s i)) at 1.
  unfold R.v36758, N.v36758.
  unfold R.v16484, N.v16484.
  rewrite ?node_36757.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36759 (s : N.State) (i : N.Inputs) :
  R.v36759 (state s) (inputs i) = Zmod.unsigned (N.v36759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36759 s i)) at 1.
  unfold R.v36759, N.v36759.
  rewrite ?node_36754.
  rewrite ?node_36758.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36760 (s : N.State) (i : N.Inputs) :
  R.v36760 (state s) (inputs i) = Zmod.unsigned (N.v36760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36760 s i)) at 1.
  unfold R.v36760, N.v36760.
  unfold R.v6, N.v6.
  rewrite ?node_36759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36761 (s : N.State) (i : N.Inputs) :
  R.v36761 (state s) (inputs i) = Zmod.unsigned (N.v36761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36761 s i)) at 1.
  unfold R.v36761, N.v36761.
  rewrite ?node_15578.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36762 (s : N.State) (i : N.Inputs) :
  R.v36762 (state s) (inputs i) = Zmod.unsigned (N.v36762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36762 s i)) at 1.
  unfold R.v36762, N.v36762.
  unfold R.v6, N.v6.
  rewrite ?node_15636.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36763 (s : N.State) (i : N.Inputs) :
  R.v36763 (state s) (inputs i) = Zmod.unsigned (N.v36763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36763 s i)) at 1.
  unfold R.v36763, N.v36763.
  rewrite ?node_36761.
  rewrite ?node_36762.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36764 (s : N.State) (i : N.Inputs) :
  R.v36764 (state s) (inputs i) = Zmod.unsigned (N.v36764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36764 s i)) at 1.
  unfold R.v36764, N.v36764.
  rewrite ?node_36760.
  rewrite ?node_36763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36765 (s : N.State) (i : N.Inputs) :
  R.v36765 (state s) (inputs i) = Zmod.unsigned (N.v36765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36765 s i)) at 1.
  unfold R.v36765, N.v36765.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36766 (s : N.State) (i : N.Inputs) :
  R.v36766 (state s) (inputs i) = Zmod.unsigned (N.v36766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36766 s i)) at 1.
  unfold R.v36766, N.v36766.
  rewrite ?node_15582.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36767 (s : N.State) (i : N.Inputs) :
  R.v36767 (state s) (inputs i) = Zmod.unsigned (N.v36767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36767 s i)) at 1.
  unfold R.v36767, N.v36767.
  unfold R.v6, N.v6.
  rewrite !state_r2175_nr_5F2197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2175_nr_5F2197 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36768 (s : N.State) (i : N.Inputs) :
  R.v36768 (state s) (inputs i) = Zmod.unsigned (N.v36768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36768 s i)) at 1.
  unfold R.v36768, N.v36768.
  unfold R.v6, N.v6.
  rewrite ?node_15578.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36769 (s : N.State) (i : N.Inputs) :
  R.v36769 (state s) (inputs i) = Zmod.unsigned (N.v36769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36769 s i)) at 1.
  unfold R.v36769, N.v36769.
  rewrite ?node_36767.
  rewrite ?node_36768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36770 (s : N.State) (i : N.Inputs) :
  R.v36770 (state s) (inputs i) = Zmod.unsigned (N.v36770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36770 s i)) at 1.
  unfold R.v36770, N.v36770.
  unfold R.v16484, N.v16484.
  rewrite ?node_36769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36771 (s : N.State) (i : N.Inputs) :
  R.v36771 (state s) (inputs i) = Zmod.unsigned (N.v36771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36771 s i)) at 1.
  unfold R.v36771, N.v36771.
  rewrite ?node_36766.
  rewrite ?node_36770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36772 (s : N.State) (i : N.Inputs) :
  R.v36772 (state s) (inputs i) = Zmod.unsigned (N.v36772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36772 s i)) at 1.
  unfold R.v36772, N.v36772.
  unfold R.v6, N.v6.
  rewrite ?node_36771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36773 (s : N.State) (i : N.Inputs) :
  R.v36773 (state s) (inputs i) = Zmod.unsigned (N.v36773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36773 s i)) at 1.
  unfold R.v36773, N.v36773.
  rewrite ?node_15583.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36774 (s : N.State) (i : N.Inputs) :
  R.v36774 (state s) (inputs i) = Zmod.unsigned (N.v36774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36774 s i)) at 1.
  unfold R.v36774, N.v36774.
  unfold R.v6, N.v6.
  rewrite ?node_15651.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36775 (s : N.State) (i : N.Inputs) :
  R.v36775 (state s) (inputs i) = Zmod.unsigned (N.v36775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36775 s i)) at 1.
  unfold R.v36775, N.v36775.
  rewrite ?node_36773.
  rewrite ?node_36774.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36776 (s : N.State) (i : N.Inputs) :
  R.v36776 (state s) (inputs i) = Zmod.unsigned (N.v36776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36776 s i)) at 1.
  unfold R.v36776, N.v36776.
  rewrite ?node_36772.
  rewrite ?node_36775.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36777 (s : N.State) (i : N.Inputs) :
  R.v36777 (state s) (inputs i) = Zmod.unsigned (N.v36777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36777 s i)) at 1.
  unfold R.v36777, N.v36777.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36778 (s : N.State) (i : N.Inputs) :
  R.v36778 (state s) (inputs i) = Zmod.unsigned (N.v36778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36778 s i)) at 1.
  unfold R.v36778, N.v36778.
  unfold R.v16463, N.v16463.
  rewrite !state_r2178_nr_5F2200.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2178_nr_5F2200 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36779 (s : N.State) (i : N.Inputs) :
  R.v36779 (state s) (inputs i) = Zmod.unsigned (N.v36779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36779 s i)) at 1.
  unfold R.v36779, N.v36779.
  unfold R.v6, N.v6.
  rewrite !state_r2177_nr_5F2199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2177_nr_5F2199 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36780 (s : N.State) (i : N.Inputs) :
  R.v36780 (state s) (inputs i) = Zmod.unsigned (N.v36780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36780 s i)) at 1.
  unfold R.v36780, N.v36780.
  unfold R.v6, N.v6.
  rewrite !state_r2176_nr_5F2198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2176_nr_5F2198 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36781 (s : N.State) (i : N.Inputs) :
  R.v36781 (state s) (inputs i) = Zmod.unsigned (N.v36781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36781 s i)) at 1.
  unfold R.v36781, N.v36781.
  rewrite ?node_36779.
  rewrite ?node_36780.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36782 (s : N.State) (i : N.Inputs) :
  R.v36782 (state s) (inputs i) = Zmod.unsigned (N.v36782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36782 s i)) at 1.
  unfold R.v36782, N.v36782.
  unfold R.v16484, N.v16484.
  rewrite ?node_36781.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36783 (s : N.State) (i : N.Inputs) :
  R.v36783 (state s) (inputs i) = Zmod.unsigned (N.v36783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36783 s i)) at 1.
  unfold R.v36783, N.v36783.
  rewrite ?node_36778.
  rewrite ?node_36782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36784 (s : N.State) (i : N.Inputs) :
  R.v36784 (state s) (inputs i) = Zmod.unsigned (N.v36784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36784 s i)) at 1.
  unfold R.v36784, N.v36784.
  unfold R.v6, N.v6.
  rewrite ?node_36783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36785 (s : N.State) (i : N.Inputs) :
  R.v36785 (state s) (inputs i) = Zmod.unsigned (N.v36785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36785 s i)) at 1.
  unfold R.v36785, N.v36785.
  rewrite ?node_15586.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36786 (s : N.State) (i : N.Inputs) :
  R.v36786 (state s) (inputs i) = Zmod.unsigned (N.v36786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36786 s i)) at 1.
  unfold R.v36786, N.v36786.
  unfold R.v6, N.v6.
  rewrite ?node_15654.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36787 (s : N.State) (i : N.Inputs) :
  R.v36787 (state s) (inputs i) = Zmod.unsigned (N.v36787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36787 s i)) at 1.
  unfold R.v36787, N.v36787.
  rewrite ?node_36785.
  rewrite ?node_36786.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36788 (s : N.State) (i : N.Inputs) :
  R.v36788 (state s) (inputs i) = Zmod.unsigned (N.v36788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36788 s i)) at 1.
  unfold R.v36788, N.v36788.
  rewrite ?node_36784.
  rewrite ?node_36787.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36789 (s : N.State) (i : N.Inputs) :
  R.v36789 (state s) (inputs i) = Zmod.unsigned (N.v36789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36789 s i)) at 1.
  unfold R.v36789, N.v36789.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36790 (s : N.State) (i : N.Inputs) :
  R.v36790 (state s) (inputs i) = Zmod.unsigned (N.v36790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36790 s i)) at 1.
  unfold R.v36790, N.v36790.
  rewrite ?node_15629.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36791 (s : N.State) (i : N.Inputs) :
  R.v36791 (state s) (inputs i) = Zmod.unsigned (N.v36791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36791 s i)) at 1.
  unfold R.v36791, N.v36791.
  unfold R.v16463, N.v16463.
  rewrite !state_r2182_nr_5F2204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2182_nr_5F2204 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36792 (s : N.State) (i : N.Inputs) :
  R.v36792 (state s) (inputs i) = Zmod.unsigned (N.v36792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36792 s i)) at 1.
  unfold R.v36792, N.v36792.
  unfold R.v16463, N.v16463.
  rewrite !state_r2181_nr_5F2203.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2181_nr_5F2203 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36793 (s : N.State) (i : N.Inputs) :
  R.v36793 (state s) (inputs i) = Zmod.unsigned (N.v36793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36793 s i)) at 1.
  unfold R.v36793, N.v36793.
  unfold R.v6, N.v6.
  rewrite !state_r2180_nr_5F2202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2180_nr_5F2202 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36794 (s : N.State) (i : N.Inputs) :
  R.v36794 (state s) (inputs i) = Zmod.unsigned (N.v36794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36794 s i)) at 1.
  unfold R.v36794, N.v36794.
  unfold R.v6, N.v6.
  rewrite !state_r2179_nr_5F2201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2179_nr_5F2201 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36795 (s : N.State) (i : N.Inputs) :
  R.v36795 (state s) (inputs i) = Zmod.unsigned (N.v36795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36795 s i)) at 1.
  unfold R.v36795, N.v36795.
  rewrite ?node_36793.
  rewrite ?node_36794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36796 (s : N.State) (i : N.Inputs) :
  R.v36796 (state s) (inputs i) = Zmod.unsigned (N.v36796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36796 s i)) at 1.
  unfold R.v36796, N.v36796.
  unfold R.v16484, N.v16484.
  rewrite ?node_36795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36797 (s : N.State) (i : N.Inputs) :
  R.v36797 (state s) (inputs i) = Zmod.unsigned (N.v36797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36797 s i)) at 1.
  unfold R.v36797, N.v36797.
  rewrite ?node_36790.
  rewrite ?node_36791.
  rewrite ?node_36792.
  rewrite ?node_36796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36798 (s : N.State) (i : N.Inputs) :
  R.v36798 (state s) (inputs i) = Zmod.unsigned (N.v36798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36798 s i)) at 1.
  unfold R.v36798, N.v36798.
  unfold R.v6, N.v6.
  rewrite ?node_36797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36799 (s : N.State) (i : N.Inputs) :
  R.v36799 (state s) (inputs i) = Zmod.unsigned (N.v36799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36799 s i)) at 1.
  unfold R.v36799, N.v36799.
  rewrite ?node_15630.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36800 (s : N.State) (i : N.Inputs) :
  R.v36800 (state s) (inputs i) = Zmod.unsigned (N.v36800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36800 s i)) at 1.
  unfold R.v36800, N.v36800.
  unfold R.v6, N.v6.
  rewrite ?node_15681.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36801 (s : N.State) (i : N.Inputs) :
  R.v36801 (state s) (inputs i) = Zmod.unsigned (N.v36801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36801 s i)) at 1.
  unfold R.v36801, N.v36801.
  unfold R.v6, N.v6.
  rewrite ?node_15695.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36802 (s : N.State) (i : N.Inputs) :
  R.v36802 (state s) (inputs i) = Zmod.unsigned (N.v36802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36802 s i)) at 1.
  unfold R.v36802, N.v36802.
  rewrite ?node_36799.
  rewrite ?node_36800.
  rewrite ?node_36801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36803 (s : N.State) (i : N.Inputs) :
  R.v36803 (state s) (inputs i) = Zmod.unsigned (N.v36803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36803 s i)) at 1.
  unfold R.v36803, N.v36803.
  rewrite ?node_36798.
  rewrite ?node_36802.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36804 (s : N.State) (i : N.Inputs) :
  R.v36804 (state s) (inputs i) = Zmod.unsigned (N.v36804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36804 s i)) at 1.
  unfold R.v36804, N.v36804.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36805 (s : N.State) (i : N.Inputs) :
  R.v36805 (state s) (inputs i) = Zmod.unsigned (N.v36805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36805 s i)) at 1.
  unfold R.v36805, N.v36805.
  unfold R.v16463, N.v16463.
  rewrite !state_r2181_nr_5F2203.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2181_nr_5F2203 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36806 (s : N.State) (i : N.Inputs) :
  R.v36806 (state s) (inputs i) = Zmod.unsigned (N.v36806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36806 s i)) at 1.
  unfold R.v36806, N.v36806.
  unfold R.v6, N.v6.
  rewrite !state_r2180_nr_5F2202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2180_nr_5F2202 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36807 (s : N.State) (i : N.Inputs) :
  R.v36807 (state s) (inputs i) = Zmod.unsigned (N.v36807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36807 s i)) at 1.
  unfold R.v36807, N.v36807.
  unfold R.v6, N.v6.
  rewrite !state_r2179_nr_5F2201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2179_nr_5F2201 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36808 (s : N.State) (i : N.Inputs) :
  R.v36808 (state s) (inputs i) = Zmod.unsigned (N.v36808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36808 s i)) at 1.
  unfold R.v36808, N.v36808.
  rewrite ?node_36806.
  rewrite ?node_36807.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36809 (s : N.State) (i : N.Inputs) :
  R.v36809 (state s) (inputs i) = Zmod.unsigned (N.v36809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36809 s i)) at 1.
  unfold R.v36809, N.v36809.
  unfold R.v16484, N.v16484.
  rewrite ?node_36808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36810 (s : N.State) (i : N.Inputs) :
  R.v36810 (state s) (inputs i) = Zmod.unsigned (N.v36810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36810 s i)) at 1.
  unfold R.v36810, N.v36810.
  rewrite ?node_36805.
  rewrite ?node_36809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36811 (s : N.State) (i : N.Inputs) :
  R.v36811 (state s) (inputs i) = Zmod.unsigned (N.v36811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36811 s i)) at 1.
  unfold R.v36811, N.v36811.
  unfold R.v6, N.v6.
  rewrite ?node_36810.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36812 (s : N.State) (i : N.Inputs) :
  R.v36812 (state s) (inputs i) = Zmod.unsigned (N.v36812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36812 s i)) at 1.
  unfold R.v36812, N.v36812.
  rewrite ?node_15626.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36813 (s : N.State) (i : N.Inputs) :
  R.v36813 (state s) (inputs i) = Zmod.unsigned (N.v36813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36813 s i)) at 1.
  unfold R.v36813, N.v36813.
  unfold R.v6, N.v6.
  rewrite ?node_15681.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36814 (s : N.State) (i : N.Inputs) :
  R.v36814 (state s) (inputs i) = Zmod.unsigned (N.v36814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36814 s i)) at 1.
  unfold R.v36814, N.v36814.
  rewrite ?node_36812.
  rewrite ?node_36813.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36815 (s : N.State) (i : N.Inputs) :
  R.v36815 (state s) (inputs i) = Zmod.unsigned (N.v36815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36815 s i)) at 1.
  unfold R.v36815, N.v36815.
  rewrite ?node_36811.
  rewrite ?node_36814.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36816 (s : N.State) (i : N.Inputs) :
  R.v36816 (state s) (inputs i) = Zmod.unsigned (N.v36816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36816 s i)) at 1.
  unfold R.v36816, N.v36816.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36817 (s : N.State) (i : N.Inputs) :
  R.v36817 (state s) (inputs i) = Zmod.unsigned (N.v36817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36817 s i)) at 1.
  unfold R.v36817, N.v36817.
  rewrite ?node_15629.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36818 (s : N.State) (i : N.Inputs) :
  R.v36818 (state s) (inputs i) = Zmod.unsigned (N.v36818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36818 s i)) at 1.
  unfold R.v36818, N.v36818.
  unfold R.v6, N.v6.
  rewrite !state_r2182_nr_5F2204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2182_nr_5F2204 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36819 (s : N.State) (i : N.Inputs) :
  R.v36819 (state s) (inputs i) = Zmod.unsigned (N.v36819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36819 s i)) at 1.
  unfold R.v36819, N.v36819.
  unfold R.v6, N.v6.
  rewrite ?node_15626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36820 (s : N.State) (i : N.Inputs) :
  R.v36820 (state s) (inputs i) = Zmod.unsigned (N.v36820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36820 s i)) at 1.
  unfold R.v36820, N.v36820.
  rewrite ?node_36818.
  rewrite ?node_36819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36821 (s : N.State) (i : N.Inputs) :
  R.v36821 (state s) (inputs i) = Zmod.unsigned (N.v36821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36821 s i)) at 1.
  unfold R.v36821, N.v36821.
  unfold R.v16484, N.v16484.
  rewrite ?node_36820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36822 (s : N.State) (i : N.Inputs) :
  R.v36822 (state s) (inputs i) = Zmod.unsigned (N.v36822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36822 s i)) at 1.
  unfold R.v36822, N.v36822.
  rewrite ?node_36817.
  rewrite ?node_36821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36823 (s : N.State) (i : N.Inputs) :
  R.v36823 (state s) (inputs i) = Zmod.unsigned (N.v36823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36823 s i)) at 1.
  unfold R.v36823, N.v36823.
  unfold R.v6, N.v6.
  rewrite ?node_36822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36824 (s : N.State) (i : N.Inputs) :
  R.v36824 (state s) (inputs i) = Zmod.unsigned (N.v36824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36824 s i)) at 1.
  unfold R.v36824, N.v36824.
  rewrite ?node_15630.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36825 (s : N.State) (i : N.Inputs) :
  R.v36825 (state s) (inputs i) = Zmod.unsigned (N.v36825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36825 s i)) at 1.
  unfold R.v36825, N.v36825.
  unfold R.v6, N.v6.
  rewrite ?node_15695.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36826 (s : N.State) (i : N.Inputs) :
  R.v36826 (state s) (inputs i) = Zmod.unsigned (N.v36826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36826 s i)) at 1.
  unfold R.v36826, N.v36826.
  rewrite ?node_36824.
  rewrite ?node_36825.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36827 (s : N.State) (i : N.Inputs) :
  R.v36827 (state s) (inputs i) = Zmod.unsigned (N.v36827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36827 s i)) at 1.
  unfold R.v36827, N.v36827.
  rewrite ?node_36823.
  rewrite ?node_36826.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36828 (s : N.State) (i : N.Inputs) :
  R.v36828 (state s) (inputs i) = Zmod.unsigned (N.v36828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36828 s i)) at 1.
  unfold R.v36828, N.v36828.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36829 (s : N.State) (i : N.Inputs) :
  R.v36829 (state s) (inputs i) = Zmod.unsigned (N.v36829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36829 s i)) at 1.
  unfold R.v36829, N.v36829.
  rewrite ?node_15636.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36830 (s : N.State) (i : N.Inputs) :
  R.v36830 (state s) (inputs i) = Zmod.unsigned (N.v36830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36830 s i)) at 1.
  unfold R.v36830, N.v36830.
  unfold R.v16463, N.v16463.
  rewrite !state_r2186_nr_5F2208.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2186_nr_5F2208 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36831 (s : N.State) (i : N.Inputs) :
  R.v36831 (state s) (inputs i) = Zmod.unsigned (N.v36831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36831 s i)) at 1.
  unfold R.v36831, N.v36831.
  unfold R.v16463, N.v16463.
  rewrite !state_r2185_nr_5F2207.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2185_nr_5F2207 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36832 (s : N.State) (i : N.Inputs) :
  R.v36832 (state s) (inputs i) = Zmod.unsigned (N.v36832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36832 s i)) at 1.
  unfold R.v36832, N.v36832.
  unfold R.v6, N.v6.
  rewrite !state_r2184_nr_5F2206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2184_nr_5F2206 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36833 (s : N.State) (i : N.Inputs) :
  R.v36833 (state s) (inputs i) = Zmod.unsigned (N.v36833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36833 s i)) at 1.
  unfold R.v36833, N.v36833.
  unfold R.v6, N.v6.
  rewrite !state_r2183_nr_5F2205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2183_nr_5F2205 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36834 (s : N.State) (i : N.Inputs) :
  R.v36834 (state s) (inputs i) = Zmod.unsigned (N.v36834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36834 s i)) at 1.
  unfold R.v36834, N.v36834.
  rewrite ?node_36832.
  rewrite ?node_36833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36835 (s : N.State) (i : N.Inputs) :
  R.v36835 (state s) (inputs i) = Zmod.unsigned (N.v36835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36835 s i)) at 1.
  unfold R.v36835, N.v36835.
  unfold R.v16484, N.v16484.
  rewrite ?node_36834.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36836 (s : N.State) (i : N.Inputs) :
  R.v36836 (state s) (inputs i) = Zmod.unsigned (N.v36836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36836 s i)) at 1.
  unfold R.v36836, N.v36836.
  rewrite ?node_36829.
  rewrite ?node_36830.
  rewrite ?node_36831.
  rewrite ?node_36835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36837 (s : N.State) (i : N.Inputs) :
  R.v36837 (state s) (inputs i) = Zmod.unsigned (N.v36837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36837 s i)) at 1.
  unfold R.v36837, N.v36837.
  unfold R.v6, N.v6.
  rewrite ?node_36836.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36838 (s : N.State) (i : N.Inputs) :
  R.v36838 (state s) (inputs i) = Zmod.unsigned (N.v36838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36838 s i)) at 1.
  unfold R.v36838, N.v36838.
  rewrite ?node_15637.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36839 (s : N.State) (i : N.Inputs) :
  R.v36839 (state s) (inputs i) = Zmod.unsigned (N.v36839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36839 s i)) at 1.
  unfold R.v36839, N.v36839.
  unfold R.v6, N.v6.
  rewrite ?node_15688.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36840 (s : N.State) (i : N.Inputs) :
  R.v36840 (state s) (inputs i) = Zmod.unsigned (N.v36840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36840 s i)) at 1.
  unfold R.v36840, N.v36840.
  unfold R.v6, N.v6.
  rewrite ?node_15703.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36841 (s : N.State) (i : N.Inputs) :
  R.v36841 (state s) (inputs i) = Zmod.unsigned (N.v36841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36841 s i)) at 1.
  unfold R.v36841, N.v36841.
  rewrite ?node_36838.
  rewrite ?node_36839.
  rewrite ?node_36840.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36842 (s : N.State) (i : N.Inputs) :
  R.v36842 (state s) (inputs i) = Zmod.unsigned (N.v36842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36842 s i)) at 1.
  unfold R.v36842, N.v36842.
  rewrite ?node_36837.
  rewrite ?node_36841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36843 (s : N.State) (i : N.Inputs) :
  R.v36843 (state s) (inputs i) = Zmod.unsigned (N.v36843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36843 s i)) at 1.
  unfold R.v36843, N.v36843.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36844 (s : N.State) (i : N.Inputs) :
  R.v36844 (state s) (inputs i) = Zmod.unsigned (N.v36844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36844 s i)) at 1.
  unfold R.v36844, N.v36844.
  unfold R.v16463, N.v16463.
  rewrite !state_r2185_nr_5F2207.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2185_nr_5F2207 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36845 (s : N.State) (i : N.Inputs) :
  R.v36845 (state s) (inputs i) = Zmod.unsigned (N.v36845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36845 s i)) at 1.
  unfold R.v36845, N.v36845.
  unfold R.v6, N.v6.
  rewrite !state_r2184_nr_5F2206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2184_nr_5F2206 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36846 (s : N.State) (i : N.Inputs) :
  R.v36846 (state s) (inputs i) = Zmod.unsigned (N.v36846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36846 s i)) at 1.
  unfold R.v36846, N.v36846.
  unfold R.v6, N.v6.
  rewrite !state_r2183_nr_5F2205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2183_nr_5F2205 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36847 (s : N.State) (i : N.Inputs) :
  R.v36847 (state s) (inputs i) = Zmod.unsigned (N.v36847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36847 s i)) at 1.
  unfold R.v36847, N.v36847.
  rewrite ?node_36845.
  rewrite ?node_36846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36848 (s : N.State) (i : N.Inputs) :
  R.v36848 (state s) (inputs i) = Zmod.unsigned (N.v36848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36848 s i)) at 1.
  unfold R.v36848, N.v36848.
  unfold R.v16484, N.v16484.
  rewrite ?node_36847.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36849 (s : N.State) (i : N.Inputs) :
  R.v36849 (state s) (inputs i) = Zmod.unsigned (N.v36849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36849 s i)) at 1.
  unfold R.v36849, N.v36849.
  rewrite ?node_36844.
  rewrite ?node_36848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36850 (s : N.State) (i : N.Inputs) :
  R.v36850 (state s) (inputs i) = Zmod.unsigned (N.v36850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36850 s i)) at 1.
  unfold R.v36850, N.v36850.
  unfold R.v6, N.v6.
  rewrite ?node_36849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36851 (s : N.State) (i : N.Inputs) :
  R.v36851 (state s) (inputs i) = Zmod.unsigned (N.v36851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36851 s i)) at 1.
  unfold R.v36851, N.v36851.
  rewrite ?node_15632.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36852 (s : N.State) (i : N.Inputs) :
  R.v36852 (state s) (inputs i) = Zmod.unsigned (N.v36852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36852 s i)) at 1.
  unfold R.v36852, N.v36852.
  unfold R.v6, N.v6.
  rewrite ?node_15688.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36853 (s : N.State) (i : N.Inputs) :
  R.v36853 (state s) (inputs i) = Zmod.unsigned (N.v36853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36853 s i)) at 1.
  unfold R.v36853, N.v36853.
  rewrite ?node_36851.
  rewrite ?node_36852.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36854 (s : N.State) (i : N.Inputs) :
  R.v36854 (state s) (inputs i) = Zmod.unsigned (N.v36854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36854 s i)) at 1.
  unfold R.v36854, N.v36854.
  rewrite ?node_36850.
  rewrite ?node_36853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36855 (s : N.State) (i : N.Inputs) :
  R.v36855 (state s) (inputs i) = Zmod.unsigned (N.v36855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36855 s i)) at 1.
  unfold R.v36855, N.v36855.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36856 (s : N.State) (i : N.Inputs) :
  R.v36856 (state s) (inputs i) = Zmod.unsigned (N.v36856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36856 s i)) at 1.
  unfold R.v36856, N.v36856.
  rewrite ?node_15636.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36857 (s : N.State) (i : N.Inputs) :
  R.v36857 (state s) (inputs i) = Zmod.unsigned (N.v36857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36857 s i)) at 1.
  unfold R.v36857, N.v36857.
  unfold R.v6, N.v6.
  rewrite !state_r2186_nr_5F2208.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2186_nr_5F2208 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36858 (s : N.State) (i : N.Inputs) :
  R.v36858 (state s) (inputs i) = Zmod.unsigned (N.v36858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36858 s i)) at 1.
  unfold R.v36858, N.v36858.
  unfold R.v6, N.v6.
  rewrite ?node_15632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36859 (s : N.State) (i : N.Inputs) :
  R.v36859 (state s) (inputs i) = Zmod.unsigned (N.v36859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36859 s i)) at 1.
  unfold R.v36859, N.v36859.
  rewrite ?node_36857.
  rewrite ?node_36858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36860 (s : N.State) (i : N.Inputs) :
  R.v36860 (state s) (inputs i) = Zmod.unsigned (N.v36860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36860 s i)) at 1.
  unfold R.v36860, N.v36860.
  unfold R.v16484, N.v16484.
  rewrite ?node_36859.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36861 (s : N.State) (i : N.Inputs) :
  R.v36861 (state s) (inputs i) = Zmod.unsigned (N.v36861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36861 s i)) at 1.
  unfold R.v36861, N.v36861.
  rewrite ?node_36856.
  rewrite ?node_36860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36862 (s : N.State) (i : N.Inputs) :
  R.v36862 (state s) (inputs i) = Zmod.unsigned (N.v36862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36862 s i)) at 1.
  unfold R.v36862, N.v36862.
  unfold R.v6, N.v6.
  rewrite ?node_36861.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36863 (s : N.State) (i : N.Inputs) :
  R.v36863 (state s) (inputs i) = Zmod.unsigned (N.v36863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36863 s i)) at 1.
  unfold R.v36863, N.v36863.
  rewrite ?node_15637.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36864 (s : N.State) (i : N.Inputs) :
  R.v36864 (state s) (inputs i) = Zmod.unsigned (N.v36864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36864 s i)) at 1.
  unfold R.v36864, N.v36864.
  unfold R.v6, N.v6.
  rewrite ?node_15703.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36865 (s : N.State) (i : N.Inputs) :
  R.v36865 (state s) (inputs i) = Zmod.unsigned (N.v36865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36865 s i)) at 1.
  unfold R.v36865, N.v36865.
  rewrite ?node_36863.
  rewrite ?node_36864.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36866 (s : N.State) (i : N.Inputs) :
  R.v36866 (state s) (inputs i) = Zmod.unsigned (N.v36866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36866 s i)) at 1.
  unfold R.v36866, N.v36866.
  rewrite ?node_36862.
  rewrite ?node_36865.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36867 (s : N.State) (i : N.Inputs) :
  R.v36867 (state s) (inputs i) = Zmod.unsigned (N.v36867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36867 s i)) at 1.
  unfold R.v36867, N.v36867.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36868 (s : N.State) (i : N.Inputs) :
  R.v36868 (state s) (inputs i) = Zmod.unsigned (N.v36868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36868 s i)) at 1.
  unfold R.v36868, N.v36868.
  unfold R.v6, N.v6.
  rewrite !state_r2188_nr_5F2210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2188_nr_5F2210 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36869 (s : N.State) (i : N.Inputs) :
  R.v36869 (state s) (inputs i) = Zmod.unsigned (N.v36869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36869 s i)) at 1.
  unfold R.v36869, N.v36869.
  unfold R.v6, N.v6.
  rewrite !state_r2187_nr_5F2209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2187_nr_5F2209 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36870 (s : N.State) (i : N.Inputs) :
  R.v36870 (state s) (inputs i) = Zmod.unsigned (N.v36870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36870 s i)) at 1.
  unfold R.v36870, N.v36870.
  rewrite ?node_36868.
  rewrite ?node_36869.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36871 (s : N.State) (i : N.Inputs) :
  R.v36871 (state s) (inputs i) = Zmod.unsigned (N.v36871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36871 s i)) at 1.
  unfold R.v36871, N.v36871.
  unfold R.v16463, N.v16463.
  rewrite ?node_36870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36872 (s : N.State) (i : N.Inputs) :
  R.v36872 (state s) (inputs i) = Zmod.unsigned (N.v36872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36872 s i)) at 1.
  unfold R.v36872, N.v36872.
  rewrite ?node_15639.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36873 (s : N.State) (i : N.Inputs) :
  R.v36873 (state s) (inputs i) = Zmod.unsigned (N.v36873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36873 s i)) at 1.
  unfold R.v36873, N.v36873.
  unfold R.v6, N.v6.
  rewrite ?node_15704.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36874 (s : N.State) (i : N.Inputs) :
  R.v36874 (state s) (inputs i) = Zmod.unsigned (N.v36874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36874 s i)) at 1.
  unfold R.v36874, N.v36874.
  rewrite ?node_36872.
  rewrite ?node_36873.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36875 (s : N.State) (i : N.Inputs) :
  R.v36875 (state s) (inputs i) = Zmod.unsigned (N.v36875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36875 s i)) at 1.
  unfold R.v36875, N.v36875.
  rewrite ?node_36871.
  rewrite ?node_36874.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36876 (s : N.State) (i : N.Inputs) :
  R.v36876 (state s) (inputs i) = Zmod.unsigned (N.v36876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36876 s i)) at 1.
  unfold R.v36876, N.v36876.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36877 (s : N.State) (i : N.Inputs) :
  R.v36877 (state s) (inputs i) = Zmod.unsigned (N.v36877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36877 s i)) at 1.
  unfold R.v36877, N.v36877.
  rewrite ?node_15681.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36878 (s : N.State) (i : N.Inputs) :
  R.v36878 (state s) (inputs i) = Zmod.unsigned (N.v36878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36878 s i)) at 1.
  unfold R.v36878, N.v36878.
  unfold R.v16463, N.v16463.
  rewrite !state_r2191_nr_5F2214.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2191_nr_5F2214 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36879 (s : N.State) (i : N.Inputs) :
  R.v36879 (state s) (inputs i) = Zmod.unsigned (N.v36879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36879 s i)) at 1.
  unfold R.v36879, N.v36879.
  unfold R.v16463, N.v16463.
  rewrite !state_r2190_nr_5F2213.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2190_nr_5F2213 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36880 (s : N.State) (i : N.Inputs) :
  R.v36880 (state s) (inputs i) = Zmod.unsigned (N.v36880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36880 s i)) at 1.
  unfold R.v36880, N.v36880.
  unfold R.v6, N.v6.
  rewrite !state_r2189_nr_5F2212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2189_nr_5F2212 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36881 (s : N.State) (i : N.Inputs) :
  R.v36881 (state s) (inputs i) = Zmod.unsigned (N.v36881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36881 s i)) at 1.
  unfold R.v36881, N.v36881.
  unfold R.v19, N.v19.
  rewrite ?node_36880.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36882 (s : N.State) (i : N.Inputs) :
  R.v36882 (state s) (inputs i) = Zmod.unsigned (N.v36882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36882 s i)) at 1.
  unfold R.v36882, N.v36882.
  unfold R.v16484, N.v16484.
  rewrite ?node_36881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36883 (s : N.State) (i : N.Inputs) :
  R.v36883 (state s) (inputs i) = Zmod.unsigned (N.v36883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36883 s i)) at 1.
  unfold R.v36883, N.v36883.
  rewrite ?node_36877.
  rewrite ?node_36878.
  rewrite ?node_36879.
  rewrite ?node_36882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36884 (s : N.State) (i : N.Inputs) :
  R.v36884 (state s) (inputs i) = Zmod.unsigned (N.v36884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36884 s i)) at 1.
  unfold R.v36884, N.v36884.
  unfold R.v6, N.v6.
  rewrite ?node_36883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36885 (s : N.State) (i : N.Inputs) :
  R.v36885 (state s) (inputs i) = Zmod.unsigned (N.v36885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36885 s i)) at 1.
  unfold R.v36885, N.v36885.
  rewrite ?node_15682.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36886 (s : N.State) (i : N.Inputs) :
  R.v36886 (state s) (inputs i) = Zmod.unsigned (N.v36886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36886 s i)) at 1.
  unfold R.v36886, N.v36886.
  unfold R.v6, N.v6.
  rewrite ?node_15730.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36887 (s : N.State) (i : N.Inputs) :
  R.v36887 (state s) (inputs i) = Zmod.unsigned (N.v36887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36887 s i)) at 1.
  unfold R.v36887, N.v36887.
  unfold R.v6, N.v6.
  rewrite ?node_15743.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36888 (s : N.State) (i : N.Inputs) :
  R.v36888 (state s) (inputs i) = Zmod.unsigned (N.v36888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36888 s i)) at 1.
  unfold R.v36888, N.v36888.
  rewrite ?node_36885.
  rewrite ?node_36886.
  rewrite ?node_36887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36889 (s : N.State) (i : N.Inputs) :
  R.v36889 (state s) (inputs i) = Zmod.unsigned (N.v36889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36889 s i)) at 1.
  unfold R.v36889, N.v36889.
  rewrite ?node_36884.
  rewrite ?node_36888.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36890 (s : N.State) (i : N.Inputs) :
  R.v36890 (state s) (inputs i) = Zmod.unsigned (N.v36890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36890 s i)) at 1.
  unfold R.v36890, N.v36890.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36891 (s : N.State) (i : N.Inputs) :
  R.v36891 (state s) (inputs i) = Zmod.unsigned (N.v36891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36891 s i)) at 1.
  unfold R.v36891, N.v36891.
  unfold R.v16463, N.v16463.
  rewrite !state_r2190_nr_5F2213.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2190_nr_5F2213 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36892 (s : N.State) (i : N.Inputs) :
  R.v36892 (state s) (inputs i) = Zmod.unsigned (N.v36892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36892 s i)) at 1.
  unfold R.v36892, N.v36892.
  unfold R.v6, N.v6.
  rewrite !state_r2189_nr_5F2212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2189_nr_5F2212 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36893 (s : N.State) (i : N.Inputs) :
  R.v36893 (state s) (inputs i) = Zmod.unsigned (N.v36893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36893 s i)) at 1.
  unfold R.v36893, N.v36893.
  unfold R.v19, N.v19.
  rewrite ?node_36892.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36894 (s : N.State) (i : N.Inputs) :
  R.v36894 (state s) (inputs i) = Zmod.unsigned (N.v36894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36894 s i)) at 1.
  unfold R.v36894, N.v36894.
  unfold R.v16484, N.v16484.
  rewrite ?node_36893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36895 (s : N.State) (i : N.Inputs) :
  R.v36895 (state s) (inputs i) = Zmod.unsigned (N.v36895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36895 s i)) at 1.
  unfold R.v36895, N.v36895.
  rewrite ?node_36891.
  rewrite ?node_36894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36896 (s : N.State) (i : N.Inputs) :
  R.v36896 (state s) (inputs i) = Zmod.unsigned (N.v36896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36896 s i)) at 1.
  unfold R.v36896, N.v36896.
  unfold R.v6, N.v6.
  rewrite ?node_36895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36897 (s : N.State) (i : N.Inputs) :
  R.v36897 (state s) (inputs i) = Zmod.unsigned (N.v36897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36897 s i)) at 1.
  unfold R.v36897, N.v36897.
  rewrite ?node_15677.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36898 (s : N.State) (i : N.Inputs) :
  R.v36898 (state s) (inputs i) = Zmod.unsigned (N.v36898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36898 s i)) at 1.
  unfold R.v36898, N.v36898.
  unfold R.v6, N.v6.
  rewrite ?node_15730.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36899 (s : N.State) (i : N.Inputs) :
  R.v36899 (state s) (inputs i) = Zmod.unsigned (N.v36899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36899 s i)) at 1.
  unfold R.v36899, N.v36899.
  rewrite ?node_36897.
  rewrite ?node_36898.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36900 (s : N.State) (i : N.Inputs) :
  R.v36900 (state s) (inputs i) = Zmod.unsigned (N.v36900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36900 s i)) at 1.
  unfold R.v36900, N.v36900.
  rewrite ?node_36896.
  rewrite ?node_36899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36901 (s : N.State) (i : N.Inputs) :
  R.v36901 (state s) (inputs i) = Zmod.unsigned (N.v36901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36901 s i)) at 1.
  unfold R.v36901, N.v36901.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36902 (s : N.State) (i : N.Inputs) :
  R.v36902 (state s) (inputs i) = Zmod.unsigned (N.v36902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36902 s i)) at 1.
  unfold R.v36902, N.v36902.
  rewrite ?node_15681.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36903 (s : N.State) (i : N.Inputs) :
  R.v36903 (state s) (inputs i) = Zmod.unsigned (N.v36903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36903 s i)) at 1.
  unfold R.v36903, N.v36903.
  unfold R.v6, N.v6.
  rewrite !state_r2191_nr_5F2214.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2191_nr_5F2214 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36904 (s : N.State) (i : N.Inputs) :
  R.v36904 (state s) (inputs i) = Zmod.unsigned (N.v36904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36904 s i)) at 1.
  unfold R.v36904, N.v36904.
  unfold R.v6, N.v6.
  rewrite ?node_15677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36905 (s : N.State) (i : N.Inputs) :
  R.v36905 (state s) (inputs i) = Zmod.unsigned (N.v36905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36905 s i)) at 1.
  unfold R.v36905, N.v36905.
  rewrite ?node_36903.
  rewrite ?node_36904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36906 (s : N.State) (i : N.Inputs) :
  R.v36906 (state s) (inputs i) = Zmod.unsigned (N.v36906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36906 s i)) at 1.
  unfold R.v36906, N.v36906.
  unfold R.v16484, N.v16484.
  rewrite ?node_36905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36907 (s : N.State) (i : N.Inputs) :
  R.v36907 (state s) (inputs i) = Zmod.unsigned (N.v36907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36907 s i)) at 1.
  unfold R.v36907, N.v36907.
  rewrite ?node_36902.
  rewrite ?node_36906.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36908 (s : N.State) (i : N.Inputs) :
  R.v36908 (state s) (inputs i) = Zmod.unsigned (N.v36908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36908 s i)) at 1.
  unfold R.v36908, N.v36908.
  unfold R.v6, N.v6.
  rewrite ?node_36907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36909 (s : N.State) (i : N.Inputs) :
  R.v36909 (state s) (inputs i) = Zmod.unsigned (N.v36909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36909 s i)) at 1.
  unfold R.v36909, N.v36909.
  rewrite ?node_15682.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36910 (s : N.State) (i : N.Inputs) :
  R.v36910 (state s) (inputs i) = Zmod.unsigned (N.v36910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36910 s i)) at 1.
  unfold R.v36910, N.v36910.
  unfold R.v6, N.v6.
  rewrite ?node_15743.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36911 (s : N.State) (i : N.Inputs) :
  R.v36911 (state s) (inputs i) = Zmod.unsigned (N.v36911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36911 s i)) at 1.
  unfold R.v36911, N.v36911.
  rewrite ?node_36909.
  rewrite ?node_36910.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36912 (s : N.State) (i : N.Inputs) :
  R.v36912 (state s) (inputs i) = Zmod.unsigned (N.v36912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36912 s i)) at 1.
  unfold R.v36912, N.v36912.
  rewrite ?node_36908.
  rewrite ?node_36911.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36913 (s : N.State) (i : N.Inputs) :
  R.v36913 (state s) (inputs i) = Zmod.unsigned (N.v36913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36913 s i)) at 1.
  unfold R.v36913, N.v36913.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36914 (s : N.State) (i : N.Inputs) :
  R.v36914 (state s) (inputs i) = Zmod.unsigned (N.v36914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36914 s i)) at 1.
  unfold R.v36914, N.v36914.
  rewrite ?node_15688.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36915 (s : N.State) (i : N.Inputs) :
  R.v36915 (state s) (inputs i) = Zmod.unsigned (N.v36915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36915 s i)) at 1.
  unfold R.v36915, N.v36915.
  unfold R.v16463, N.v16463.
  rewrite !state_r2195_nr_5F2218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2195_nr_5F2218 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36916 (s : N.State) (i : N.Inputs) :
  R.v36916 (state s) (inputs i) = Zmod.unsigned (N.v36916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36916 s i)) at 1.
  unfold R.v36916, N.v36916.
  unfold R.v16463, N.v16463.
  rewrite !state_r2194_nr_5F2217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2194_nr_5F2217 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36917 (s : N.State) (i : N.Inputs) :
  R.v36917 (state s) (inputs i) = Zmod.unsigned (N.v36917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36917 s i)) at 1.
  unfold R.v36917, N.v36917.
  unfold R.v6, N.v6.
  rewrite !state_r2193_nr_5F2216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2193_nr_5F2216 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36918 (s : N.State) (i : N.Inputs) :
  R.v36918 (state s) (inputs i) = Zmod.unsigned (N.v36918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36918 s i)) at 1.
  unfold R.v36918, N.v36918.
  unfold R.v6, N.v6.
  rewrite !state_r2192_nr_5F2215.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2192_nr_5F2215 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36919 (s : N.State) (i : N.Inputs) :
  R.v36919 (state s) (inputs i) = Zmod.unsigned (N.v36919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36919 s i)) at 1.
  unfold R.v36919, N.v36919.
  rewrite ?node_36917.
  rewrite ?node_36918.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36920 (s : N.State) (i : N.Inputs) :
  R.v36920 (state s) (inputs i) = Zmod.unsigned (N.v36920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36920 s i)) at 1.
  unfold R.v36920, N.v36920.
  unfold R.v16484, N.v16484.
  rewrite ?node_36919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36921 (s : N.State) (i : N.Inputs) :
  R.v36921 (state s) (inputs i) = Zmod.unsigned (N.v36921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36921 s i)) at 1.
  unfold R.v36921, N.v36921.
  rewrite ?node_36914.
  rewrite ?node_36915.
  rewrite ?node_36916.
  rewrite ?node_36920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36922 (s : N.State) (i : N.Inputs) :
  R.v36922 (state s) (inputs i) = Zmod.unsigned (N.v36922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36922 s i)) at 1.
  unfold R.v36922, N.v36922.
  unfold R.v6, N.v6.
  rewrite ?node_36921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36923 (s : N.State) (i : N.Inputs) :
  R.v36923 (state s) (inputs i) = Zmod.unsigned (N.v36923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36923 s i)) at 1.
  unfold R.v36923, N.v36923.
  rewrite ?node_15689.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36924 (s : N.State) (i : N.Inputs) :
  R.v36924 (state s) (inputs i) = Zmod.unsigned (N.v36924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36924 s i)) at 1.
  unfold R.v36924, N.v36924.
  unfold R.v6, N.v6.
  rewrite ?node_15737.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36925 (s : N.State) (i : N.Inputs) :
  R.v36925 (state s) (inputs i) = Zmod.unsigned (N.v36925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36925 s i)) at 1.
  unfold R.v36925, N.v36925.
  unfold R.v6, N.v6.
  rewrite ?node_15751.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36926 (s : N.State) (i : N.Inputs) :
  R.v36926 (state s) (inputs i) = Zmod.unsigned (N.v36926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36926 s i)) at 1.
  unfold R.v36926, N.v36926.
  rewrite ?node_36923.
  rewrite ?node_36924.
  rewrite ?node_36925.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36927 (s : N.State) (i : N.Inputs) :
  R.v36927 (state s) (inputs i) = Zmod.unsigned (N.v36927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36927 s i)) at 1.
  unfold R.v36927, N.v36927.
  rewrite ?node_36922.
  rewrite ?node_36926.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36928 (s : N.State) (i : N.Inputs) :
  R.v36928 (state s) (inputs i) = Zmod.unsigned (N.v36928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36928 s i)) at 1.
  unfold R.v36928, N.v36928.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36929 (s : N.State) (i : N.Inputs) :
  R.v36929 (state s) (inputs i) = Zmod.unsigned (N.v36929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36929 s i)) at 1.
  unfold R.v36929, N.v36929.
  unfold R.v16463, N.v16463.
  rewrite !state_r2194_nr_5F2217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2194_nr_5F2217 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36930 (s : N.State) (i : N.Inputs) :
  R.v36930 (state s) (inputs i) = Zmod.unsigned (N.v36930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36930 s i)) at 1.
  unfold R.v36930, N.v36930.
  unfold R.v6, N.v6.
  rewrite !state_r2193_nr_5F2216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2193_nr_5F2216 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36931 (s : N.State) (i : N.Inputs) :
  R.v36931 (state s) (inputs i) = Zmod.unsigned (N.v36931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36931 s i)) at 1.
  unfold R.v36931, N.v36931.
  unfold R.v6, N.v6.
  rewrite !state_r2192_nr_5F2215.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2192_nr_5F2215 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36932 (s : N.State) (i : N.Inputs) :
  R.v36932 (state s) (inputs i) = Zmod.unsigned (N.v36932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36932 s i)) at 1.
  unfold R.v36932, N.v36932.
  rewrite ?node_36930.
  rewrite ?node_36931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36933 (s : N.State) (i : N.Inputs) :
  R.v36933 (state s) (inputs i) = Zmod.unsigned (N.v36933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36933 s i)) at 1.
  unfold R.v36933, N.v36933.
  unfold R.v16484, N.v16484.
  rewrite ?node_36932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36934 (s : N.State) (i : N.Inputs) :
  R.v36934 (state s) (inputs i) = Zmod.unsigned (N.v36934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36934 s i)) at 1.
  unfold R.v36934, N.v36934.
  rewrite ?node_36929.
  rewrite ?node_36933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36935 (s : N.State) (i : N.Inputs) :
  R.v36935 (state s) (inputs i) = Zmod.unsigned (N.v36935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36935 s i)) at 1.
  unfold R.v36935, N.v36935.
  unfold R.v6, N.v6.
  rewrite ?node_36934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36936 (s : N.State) (i : N.Inputs) :
  R.v36936 (state s) (inputs i) = Zmod.unsigned (N.v36936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36936 s i)) at 1.
  unfold R.v36936, N.v36936.
  rewrite ?node_15684.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36937 (s : N.State) (i : N.Inputs) :
  R.v36937 (state s) (inputs i) = Zmod.unsigned (N.v36937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36937 s i)) at 1.
  unfold R.v36937, N.v36937.
  unfold R.v6, N.v6.
  rewrite ?node_15737.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36938 (s : N.State) (i : N.Inputs) :
  R.v36938 (state s) (inputs i) = Zmod.unsigned (N.v36938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36938 s i)) at 1.
  unfold R.v36938, N.v36938.
  rewrite ?node_36936.
  rewrite ?node_36937.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36939 (s : N.State) (i : N.Inputs) :
  R.v36939 (state s) (inputs i) = Zmod.unsigned (N.v36939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36939 s i)) at 1.
  unfold R.v36939, N.v36939.
  rewrite ?node_36935.
  rewrite ?node_36938.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36940 (s : N.State) (i : N.Inputs) :
  R.v36940 (state s) (inputs i) = Zmod.unsigned (N.v36940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36940 s i)) at 1.
  unfold R.v36940, N.v36940.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36941 (s : N.State) (i : N.Inputs) :
  R.v36941 (state s) (inputs i) = Zmod.unsigned (N.v36941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36941 s i)) at 1.
  unfold R.v36941, N.v36941.
  rewrite ?node_15688.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36942 (s : N.State) (i : N.Inputs) :
  R.v36942 (state s) (inputs i) = Zmod.unsigned (N.v36942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36942 s i)) at 1.
  unfold R.v36942, N.v36942.
  unfold R.v6, N.v6.
  rewrite !state_r2195_nr_5F2218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2195_nr_5F2218 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36943 (s : N.State) (i : N.Inputs) :
  R.v36943 (state s) (inputs i) = Zmod.unsigned (N.v36943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36943 s i)) at 1.
  unfold R.v36943, N.v36943.
  unfold R.v6, N.v6.
  rewrite ?node_15684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36944 (s : N.State) (i : N.Inputs) :
  R.v36944 (state s) (inputs i) = Zmod.unsigned (N.v36944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36944 s i)) at 1.
  unfold R.v36944, N.v36944.
  rewrite ?node_36942.
  rewrite ?node_36943.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36945 (s : N.State) (i : N.Inputs) :
  R.v36945 (state s) (inputs i) = Zmod.unsigned (N.v36945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36945 s i)) at 1.
  unfold R.v36945, N.v36945.
  unfold R.v16484, N.v16484.
  rewrite ?node_36944.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36946 (s : N.State) (i : N.Inputs) :
  R.v36946 (state s) (inputs i) = Zmod.unsigned (N.v36946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36946 s i)) at 1.
  unfold R.v36946, N.v36946.
  rewrite ?node_36941.
  rewrite ?node_36945.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36947 (s : N.State) (i : N.Inputs) :
  R.v36947 (state s) (inputs i) = Zmod.unsigned (N.v36947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36947 s i)) at 1.
  unfold R.v36947, N.v36947.
  unfold R.v6, N.v6.
  rewrite ?node_36946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36948 (s : N.State) (i : N.Inputs) :
  R.v36948 (state s) (inputs i) = Zmod.unsigned (N.v36948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36948 s i)) at 1.
  unfold R.v36948, N.v36948.
  rewrite ?node_15689.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36949 (s : N.State) (i : N.Inputs) :
  R.v36949 (state s) (inputs i) = Zmod.unsigned (N.v36949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36949 s i)) at 1.
  unfold R.v36949, N.v36949.
  unfold R.v6, N.v6.
  rewrite ?node_15751.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36950 (s : N.State) (i : N.Inputs) :
  R.v36950 (state s) (inputs i) = Zmod.unsigned (N.v36950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36950 s i)) at 1.
  unfold R.v36950, N.v36950.
  rewrite ?node_36948.
  rewrite ?node_36949.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36951 (s : N.State) (i : N.Inputs) :
  R.v36951 (state s) (inputs i) = Zmod.unsigned (N.v36951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36951 s i)) at 1.
  unfold R.v36951, N.v36951.
  rewrite ?node_36947.
  rewrite ?node_36950.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36952 (s : N.State) (i : N.Inputs) :
  R.v36952 (state s) (inputs i) = Zmod.unsigned (N.v36952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36952 s i)) at 1.
  unfold R.v36952, N.v36952.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36953 (s : N.State) (i : N.Inputs) :
  R.v36953 (state s) (inputs i) = Zmod.unsigned (N.v36953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36953 s i)) at 1.
  unfold R.v36953, N.v36953.
  unfold R.v6, N.v6.
  rewrite !state_r2197_nr_5F2220.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2197_nr_5F2220 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36954 (s : N.State) (i : N.Inputs) :
  R.v36954 (state s) (inputs i) = Zmod.unsigned (N.v36954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36954 s i)) at 1.
  unfold R.v36954, N.v36954.
  unfold R.v6, N.v6.
  rewrite !state_r2196_nr_5F2219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2196_nr_5F2219 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36955 (s : N.State) (i : N.Inputs) :
  R.v36955 (state s) (inputs i) = Zmod.unsigned (N.v36955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36955 s i)) at 1.
  unfold R.v36955, N.v36955.
  rewrite ?node_36953.
  rewrite ?node_36954.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36956 (s : N.State) (i : N.Inputs) :
  R.v36956 (state s) (inputs i) = Zmod.unsigned (N.v36956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36956 s i)) at 1.
  unfold R.v36956, N.v36956.
  unfold R.v16463, N.v16463.
  rewrite ?node_36955.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36957 (s : N.State) (i : N.Inputs) :
  R.v36957 (state s) (inputs i) = Zmod.unsigned (N.v36957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36957 s i)) at 1.
  unfold R.v36957, N.v36957.
  rewrite ?node_15691.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36958 (s : N.State) (i : N.Inputs) :
  R.v36958 (state s) (inputs i) = Zmod.unsigned (N.v36958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36958 s i)) at 1.
  unfold R.v36958, N.v36958.
  unfold R.v6, N.v6.
  rewrite ?node_15752.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36959 (s : N.State) (i : N.Inputs) :
  R.v36959 (state s) (inputs i) = Zmod.unsigned (N.v36959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36959 s i)) at 1.
  unfold R.v36959, N.v36959.
  rewrite ?node_36957.
  rewrite ?node_36958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36960 (s : N.State) (i : N.Inputs) :
  R.v36960 (state s) (inputs i) = Zmod.unsigned (N.v36960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36960 s i)) at 1.
  unfold R.v36960, N.v36960.
  rewrite ?node_36956.
  rewrite ?node_36959.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36961 (s : N.State) (i : N.Inputs) :
  R.v36961 (state s) (inputs i) = Zmod.unsigned (N.v36961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36961 s i)) at 1.
  unfold R.v36961, N.v36961.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36962 (s : N.State) (i : N.Inputs) :
  R.v36962 (state s) (inputs i) = Zmod.unsigned (N.v36962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36962 s i)) at 1.
  unfold R.v36962, N.v36962.
  rewrite ?node_15730.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36963 (s : N.State) (i : N.Inputs) :
  R.v36963 (state s) (inputs i) = Zmod.unsigned (N.v36963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36963 s i)) at 1.
  unfold R.v36963, N.v36963.
  unfold R.v16463, N.v16463.
  rewrite !state_r2201_nr_5F2224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2201_nr_5F2224 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36964 (s : N.State) (i : N.Inputs) :
  R.v36964 (state s) (inputs i) = Zmod.unsigned (N.v36964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36964 s i)) at 1.
  unfold R.v36964, N.v36964.
  unfold R.v16463, N.v16463.
  rewrite !state_r2200_nr_5F2223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2200_nr_5F2223 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36965 (s : N.State) (i : N.Inputs) :
  R.v36965 (state s) (inputs i) = Zmod.unsigned (N.v36965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36965 s i)) at 1.
  unfold R.v36965, N.v36965.
  unfold R.v6, N.v6.
  rewrite !state_r2199_nr_5F2222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2199_nr_5F2222 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36966 (s : N.State) (i : N.Inputs) :
  R.v36966 (state s) (inputs i) = Zmod.unsigned (N.v36966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36966 s i)) at 1.
  unfold R.v36966, N.v36966.
  unfold R.v6, N.v6.
  rewrite !state_r2198_nr_5F2221.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2198_nr_5F2221 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36967 (s : N.State) (i : N.Inputs) :
  R.v36967 (state s) (inputs i) = Zmod.unsigned (N.v36967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36967 s i)) at 1.
  unfold R.v36967, N.v36967.
  rewrite ?node_36965.
  rewrite ?node_36966.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36968 (s : N.State) (i : N.Inputs) :
  R.v36968 (state s) (inputs i) = Zmod.unsigned (N.v36968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36968 s i)) at 1.
  unfold R.v36968, N.v36968.
  unfold R.v16484, N.v16484.
  rewrite ?node_36967.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36969 (s : N.State) (i : N.Inputs) :
  R.v36969 (state s) (inputs i) = Zmod.unsigned (N.v36969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36969 s i)) at 1.
  unfold R.v36969, N.v36969.
  rewrite ?node_36962.
  rewrite ?node_36963.
  rewrite ?node_36964.
  rewrite ?node_36968.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36970 (s : N.State) (i : N.Inputs) :
  R.v36970 (state s) (inputs i) = Zmod.unsigned (N.v36970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36970 s i)) at 1.
  unfold R.v36970, N.v36970.
  unfold R.v6, N.v6.
  rewrite ?node_36969.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36971 (s : N.State) (i : N.Inputs) :
  R.v36971 (state s) (inputs i) = Zmod.unsigned (N.v36971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36971 s i)) at 1.
  unfold R.v36971, N.v36971.
  rewrite ?node_15731.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36972 (s : N.State) (i : N.Inputs) :
  R.v36972 (state s) (inputs i) = Zmod.unsigned (N.v36972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36972 s i)) at 1.
  unfold R.v36972, N.v36972.
  unfold R.v6, N.v6.
  rewrite ?node_15779.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36973 (s : N.State) (i : N.Inputs) :
  R.v36973 (state s) (inputs i) = Zmod.unsigned (N.v36973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36973 s i)) at 1.
  unfold R.v36973, N.v36973.
  unfold R.v6, N.v6.
  rewrite ?node_15792.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36974 (s : N.State) (i : N.Inputs) :
  R.v36974 (state s) (inputs i) = Zmod.unsigned (N.v36974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36974 s i)) at 1.
  unfold R.v36974, N.v36974.
  rewrite ?node_36971.
  rewrite ?node_36972.
  rewrite ?node_36973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36975 (s : N.State) (i : N.Inputs) :
  R.v36975 (state s) (inputs i) = Zmod.unsigned (N.v36975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36975 s i)) at 1.
  unfold R.v36975, N.v36975.
  rewrite ?node_36970.
  rewrite ?node_36974.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36976 (s : N.State) (i : N.Inputs) :
  R.v36976 (state s) (inputs i) = Zmod.unsigned (N.v36976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36976 s i)) at 1.
  unfold R.v36976, N.v36976.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36977 (s : N.State) (i : N.Inputs) :
  R.v36977 (state s) (inputs i) = Zmod.unsigned (N.v36977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36977 s i)) at 1.
  unfold R.v36977, N.v36977.
  unfold R.v16463, N.v16463.
  rewrite !state_r2200_nr_5F2223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2200_nr_5F2223 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36978 (s : N.State) (i : N.Inputs) :
  R.v36978 (state s) (inputs i) = Zmod.unsigned (N.v36978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36978 s i)) at 1.
  unfold R.v36978, N.v36978.
  unfold R.v6, N.v6.
  rewrite !state_r2199_nr_5F2222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2199_nr_5F2222 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36979 (s : N.State) (i : N.Inputs) :
  R.v36979 (state s) (inputs i) = Zmod.unsigned (N.v36979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36979 s i)) at 1.
  unfold R.v36979, N.v36979.
  unfold R.v6, N.v6.
  rewrite !state_r2198_nr_5F2221.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2198_nr_5F2221 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36980 (s : N.State) (i : N.Inputs) :
  R.v36980 (state s) (inputs i) = Zmod.unsigned (N.v36980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36980 s i)) at 1.
  unfold R.v36980, N.v36980.
  rewrite ?node_36978.
  rewrite ?node_36979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36981 (s : N.State) (i : N.Inputs) :
  R.v36981 (state s) (inputs i) = Zmod.unsigned (N.v36981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36981 s i)) at 1.
  unfold R.v36981, N.v36981.
  unfold R.v16484, N.v16484.
  rewrite ?node_36980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36982 (s : N.State) (i : N.Inputs) :
  R.v36982 (state s) (inputs i) = Zmod.unsigned (N.v36982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36982 s i)) at 1.
  unfold R.v36982, N.v36982.
  rewrite ?node_36977.
  rewrite ?node_36981.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36983 (s : N.State) (i : N.Inputs) :
  R.v36983 (state s) (inputs i) = Zmod.unsigned (N.v36983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36983 s i)) at 1.
  unfold R.v36983, N.v36983.
  unfold R.v6, N.v6.
  rewrite ?node_36982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36984 (s : N.State) (i : N.Inputs) :
  R.v36984 (state s) (inputs i) = Zmod.unsigned (N.v36984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36984 s i)) at 1.
  unfold R.v36984, N.v36984.
  rewrite ?node_15727.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36985 (s : N.State) (i : N.Inputs) :
  R.v36985 (state s) (inputs i) = Zmod.unsigned (N.v36985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36985 s i)) at 1.
  unfold R.v36985, N.v36985.
  unfold R.v6, N.v6.
  rewrite ?node_15779.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36986 (s : N.State) (i : N.Inputs) :
  R.v36986 (state s) (inputs i) = Zmod.unsigned (N.v36986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36986 s i)) at 1.
  unfold R.v36986, N.v36986.
  rewrite ?node_36984.
  rewrite ?node_36985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36987 (s : N.State) (i : N.Inputs) :
  R.v36987 (state s) (inputs i) = Zmod.unsigned (N.v36987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36987 s i)) at 1.
  unfold R.v36987, N.v36987.
  rewrite ?node_36983.
  rewrite ?node_36986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36988 (s : N.State) (i : N.Inputs) :
  R.v36988 (state s) (inputs i) = Zmod.unsigned (N.v36988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36988 s i)) at 1.
  unfold R.v36988, N.v36988.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36989 (s : N.State) (i : N.Inputs) :
  R.v36989 (state s) (inputs i) = Zmod.unsigned (N.v36989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36989 s i)) at 1.
  unfold R.v36989, N.v36989.
  rewrite ?node_15730.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36990 (s : N.State) (i : N.Inputs) :
  R.v36990 (state s) (inputs i) = Zmod.unsigned (N.v36990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36990 s i)) at 1.
  unfold R.v36990, N.v36990.
  unfold R.v6, N.v6.
  rewrite !state_r2201_nr_5F2224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2201_nr_5F2224 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36991 (s : N.State) (i : N.Inputs) :
  R.v36991 (state s) (inputs i) = Zmod.unsigned (N.v36991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36991 s i)) at 1.
  unfold R.v36991, N.v36991.
  unfold R.v6, N.v6.
  rewrite ?node_15727.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36992 (s : N.State) (i : N.Inputs) :
  R.v36992 (state s) (inputs i) = Zmod.unsigned (N.v36992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36992 s i)) at 1.
  unfold R.v36992, N.v36992.
  rewrite ?node_36990.
  rewrite ?node_36991.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36993 (s : N.State) (i : N.Inputs) :
  R.v36993 (state s) (inputs i) = Zmod.unsigned (N.v36993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36993 s i)) at 1.
  unfold R.v36993, N.v36993.
  unfold R.v16484, N.v16484.
  rewrite ?node_36992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36994 (s : N.State) (i : N.Inputs) :
  R.v36994 (state s) (inputs i) = Zmod.unsigned (N.v36994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36994 s i)) at 1.
  unfold R.v36994, N.v36994.
  rewrite ?node_36989.
  rewrite ?node_36993.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36995 (s : N.State) (i : N.Inputs) :
  R.v36995 (state s) (inputs i) = Zmod.unsigned (N.v36995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36995 s i)) at 1.
  unfold R.v36995, N.v36995.
  unfold R.v6, N.v6.
  rewrite ?node_36994.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36996 (s : N.State) (i : N.Inputs) :
  R.v36996 (state s) (inputs i) = Zmod.unsigned (N.v36996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36996 s i)) at 1.
  unfold R.v36996, N.v36996.
  rewrite ?node_15731.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36997 (s : N.State) (i : N.Inputs) :
  R.v36997 (state s) (inputs i) = Zmod.unsigned (N.v36997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36997 s i)) at 1.
  unfold R.v36997, N.v36997.
  unfold R.v6, N.v6.
  rewrite ?node_15792.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36998 (s : N.State) (i : N.Inputs) :
  R.v36998 (state s) (inputs i) = Zmod.unsigned (N.v36998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36998 s i)) at 1.
  unfold R.v36998, N.v36998.
  rewrite ?node_36996.
  rewrite ?node_36997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36999 (s : N.State) (i : N.Inputs) :
  R.v36999 (state s) (inputs i) = Zmod.unsigned (N.v36999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36999 s i)) at 1.
  unfold R.v36999, N.v36999.
  rewrite ?node_36995.
  rewrite ?node_36998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
