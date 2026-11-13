(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes037.
Lemma node_38000 (s : N.State) (i : N.Inputs) :
  R.v38000 (state s) (inputs i) = Zmod.unsigned (N.v38000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38000 s i)) at 1.
  unfold R.v38000, N.v38000.
  unfold R.v6, N.v6.
  rewrite ?node_37999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38001 (s : N.State) (i : N.Inputs) :
  R.v38001 (state s) (inputs i) = Zmod.unsigned (N.v38001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38001 s i)) at 1.
  unfold R.v38001, N.v38001.
  rewrite ?node_5445.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38002 (s : N.State) (i : N.Inputs) :
  R.v38002 (state s) (inputs i) = Zmod.unsigned (N.v38002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38002 s i)) at 1.
  unfold R.v38002, N.v38002.
  unfold R.v6, N.v6.
  rewrite ?node_5494.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38003 (s : N.State) (i : N.Inputs) :
  R.v38003 (state s) (inputs i) = Zmod.unsigned (N.v38003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38003 s i)) at 1.
  unfold R.v38003, N.v38003.
  rewrite ?node_38001.
  rewrite ?node_38002.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38004 (s : N.State) (i : N.Inputs) :
  R.v38004 (state s) (inputs i) = Zmod.unsigned (N.v38004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38004 s i)) at 1.
  unfold R.v38004, N.v38004.
  rewrite ?node_38000.
  rewrite ?node_38003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38005 (s : N.State) (i : N.Inputs) :
  R.v38005 (state s) (inputs i) = Zmod.unsigned (N.v38005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38005 s i)) at 1.
  unfold R.v38005, N.v38005.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38006 (s : N.State) (i : N.Inputs) :
  R.v38006 (state s) (inputs i) = Zmod.unsigned (N.v38006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38006 s i)) at 1.
  unfold R.v38006, N.v38006.
  rewrite ?node_5486.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38007 (s : N.State) (i : N.Inputs) :
  R.v38007 (state s) (inputs i) = Zmod.unsigned (N.v38007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38007 s i)) at 1.
  unfold R.v38007, N.v38007.
  rewrite ?node_5482.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38008 (s : N.State) (i : N.Inputs) :
  R.v38008 (state s) (inputs i) = Zmod.unsigned (N.v38008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38008 s i)) at 1.
  unfold R.v38008, N.v38008.
  rewrite ?node_5478.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38009 (s : N.State) (i : N.Inputs) :
  R.v38009 (state s) (inputs i) = Zmod.unsigned (N.v38009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38009 s i)) at 1.
  unfold R.v38009, N.v38009.
  unfold R.v6, N.v6.
  rewrite ?node_5476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38010 (s : N.State) (i : N.Inputs) :
  R.v38010 (state s) (inputs i) = Zmod.unsigned (N.v38010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38010 s i)) at 1.
  unfold R.v38010, N.v38010.
  unfold R.v6, N.v6.
  rewrite ?node_5469.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38011 (s : N.State) (i : N.Inputs) :
  R.v38011 (state s) (inputs i) = Zmod.unsigned (N.v38011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38011 s i)) at 1.
  unfold R.v38011, N.v38011.
  rewrite ?node_38009.
  rewrite ?node_38010.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38012 (s : N.State) (i : N.Inputs) :
  R.v38012 (state s) (inputs i) = Zmod.unsigned (N.v38012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38012 s i)) at 1.
  unfold R.v38012, N.v38012.
  unfold R.v16484, N.v16484.
  rewrite ?node_38011.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38013 (s : N.State) (i : N.Inputs) :
  R.v38013 (state s) (inputs i) = Zmod.unsigned (N.v38013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38013 s i)) at 1.
  unfold R.v38013, N.v38013.
  rewrite ?node_38006.
  rewrite ?node_38007.
  rewrite ?node_38008.
  rewrite ?node_38012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38014 (s : N.State) (i : N.Inputs) :
  R.v38014 (state s) (inputs i) = Zmod.unsigned (N.v38014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38014 s i)) at 1.
  unfold R.v38014, N.v38014.
  unfold R.v6, N.v6.
  rewrite ?node_38013.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38015 (s : N.State) (i : N.Inputs) :
  R.v38015 (state s) (inputs i) = Zmod.unsigned (N.v38015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38015 s i)) at 1.
  unfold R.v38015, N.v38015.
  rewrite ?node_5487.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38016 (s : N.State) (i : N.Inputs) :
  R.v38016 (state s) (inputs i) = Zmod.unsigned (N.v38016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38016 s i)) at 1.
  unfold R.v38016, N.v38016.
  unfold R.v6, N.v6.
  rewrite ?node_5528.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38017 (s : N.State) (i : N.Inputs) :
  R.v38017 (state s) (inputs i) = Zmod.unsigned (N.v38017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38017 s i)) at 1.
  unfold R.v38017, N.v38017.
  unfold R.v6, N.v6.
  rewrite ?node_5538.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38018 (s : N.State) (i : N.Inputs) :
  R.v38018 (state s) (inputs i) = Zmod.unsigned (N.v38018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38018 s i)) at 1.
  unfold R.v38018, N.v38018.
  rewrite ?node_38015.
  rewrite ?node_38016.
  rewrite ?node_38017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38019 (s : N.State) (i : N.Inputs) :
  R.v38019 (state s) (inputs i) = Zmod.unsigned (N.v38019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38019 s i)) at 1.
  unfold R.v38019, N.v38019.
  rewrite ?node_38014.
  rewrite ?node_38018.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38020 (s : N.State) (i : N.Inputs) :
  R.v38020 (state s) (inputs i) = Zmod.unsigned (N.v38020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38020 s i)) at 1.
  unfold R.v38020, N.v38020.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38021 (s : N.State) (i : N.Inputs) :
  R.v38021 (state s) (inputs i) = Zmod.unsigned (N.v38021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38021 s i)) at 1.
  unfold R.v38021, N.v38021.
  rewrite ?node_5478.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38022 (s : N.State) (i : N.Inputs) :
  R.v38022 (state s) (inputs i) = Zmod.unsigned (N.v38022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38022 s i)) at 1.
  unfold R.v38022, N.v38022.
  unfold R.v6, N.v6.
  rewrite ?node_5476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38023 (s : N.State) (i : N.Inputs) :
  R.v38023 (state s) (inputs i) = Zmod.unsigned (N.v38023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38023 s i)) at 1.
  unfold R.v38023, N.v38023.
  unfold R.v6, N.v6.
  rewrite ?node_5469.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38024 (s : N.State) (i : N.Inputs) :
  R.v38024 (state s) (inputs i) = Zmod.unsigned (N.v38024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38024 s i)) at 1.
  unfold R.v38024, N.v38024.
  rewrite ?node_38022.
  rewrite ?node_38023.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38025 (s : N.State) (i : N.Inputs) :
  R.v38025 (state s) (inputs i) = Zmod.unsigned (N.v38025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38025 s i)) at 1.
  unfold R.v38025, N.v38025.
  unfold R.v16484, N.v16484.
  rewrite ?node_38024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38026 (s : N.State) (i : N.Inputs) :
  R.v38026 (state s) (inputs i) = Zmod.unsigned (N.v38026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38026 s i)) at 1.
  unfold R.v38026, N.v38026.
  rewrite ?node_38021.
  rewrite ?node_38025.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38027 (s : N.State) (i : N.Inputs) :
  R.v38027 (state s) (inputs i) = Zmod.unsigned (N.v38027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38027 s i)) at 1.
  unfold R.v38027, N.v38027.
  unfold R.v6, N.v6.
  rewrite ?node_38026.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38028 (s : N.State) (i : N.Inputs) :
  R.v38028 (state s) (inputs i) = Zmod.unsigned (N.v38028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38028 s i)) at 1.
  unfold R.v38028, N.v38028.
  rewrite ?node_5479.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38029 (s : N.State) (i : N.Inputs) :
  R.v38029 (state s) (inputs i) = Zmod.unsigned (N.v38029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38029 s i)) at 1.
  unfold R.v38029, N.v38029.
  unfold R.v6, N.v6.
  rewrite ?node_5528.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38030 (s : N.State) (i : N.Inputs) :
  R.v38030 (state s) (inputs i) = Zmod.unsigned (N.v38030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38030 s i)) at 1.
  unfold R.v38030, N.v38030.
  rewrite ?node_38028.
  rewrite ?node_38029.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38031 (s : N.State) (i : N.Inputs) :
  R.v38031 (state s) (inputs i) = Zmod.unsigned (N.v38031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38031 s i)) at 1.
  unfold R.v38031, N.v38031.
  rewrite ?node_38027.
  rewrite ?node_38030.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38032 (s : N.State) (i : N.Inputs) :
  R.v38032 (state s) (inputs i) = Zmod.unsigned (N.v38032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38032 s i)) at 1.
  unfold R.v38032, N.v38032.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38033 (s : N.State) (i : N.Inputs) :
  R.v38033 (state s) (inputs i) = Zmod.unsigned (N.v38033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38033 s i)) at 1.
  unfold R.v38033, N.v38033.
  rewrite ?node_5486.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38034 (s : N.State) (i : N.Inputs) :
  R.v38034 (state s) (inputs i) = Zmod.unsigned (N.v38034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38034 s i)) at 1.
  unfold R.v38034, N.v38034.
  unfold R.v6, N.v6.
  rewrite ?node_5482.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38035 (s : N.State) (i : N.Inputs) :
  R.v38035 (state s) (inputs i) = Zmod.unsigned (N.v38035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38035 s i)) at 1.
  unfold R.v38035, N.v38035.
  unfold R.v6, N.v6.
  rewrite ?node_5479.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38036 (s : N.State) (i : N.Inputs) :
  R.v38036 (state s) (inputs i) = Zmod.unsigned (N.v38036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38036 s i)) at 1.
  unfold R.v38036, N.v38036.
  rewrite ?node_38034.
  rewrite ?node_38035.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38037 (s : N.State) (i : N.Inputs) :
  R.v38037 (state s) (inputs i) = Zmod.unsigned (N.v38037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38037 s i)) at 1.
  unfold R.v38037, N.v38037.
  unfold R.v16484, N.v16484.
  rewrite ?node_38036.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38038 (s : N.State) (i : N.Inputs) :
  R.v38038 (state s) (inputs i) = Zmod.unsigned (N.v38038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38038 s i)) at 1.
  unfold R.v38038, N.v38038.
  rewrite ?node_38033.
  rewrite ?node_38037.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38039 (s : N.State) (i : N.Inputs) :
  R.v38039 (state s) (inputs i) = Zmod.unsigned (N.v38039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38039 s i)) at 1.
  unfold R.v38039, N.v38039.
  unfold R.v6, N.v6.
  rewrite ?node_38038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38040 (s : N.State) (i : N.Inputs) :
  R.v38040 (state s) (inputs i) = Zmod.unsigned (N.v38040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38040 s i)) at 1.
  unfold R.v38040, N.v38040.
  rewrite ?node_5487.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38041 (s : N.State) (i : N.Inputs) :
  R.v38041 (state s) (inputs i) = Zmod.unsigned (N.v38041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38041 s i)) at 1.
  unfold R.v38041, N.v38041.
  unfold R.v6, N.v6.
  rewrite ?node_5538.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38042 (s : N.State) (i : N.Inputs) :
  R.v38042 (state s) (inputs i) = Zmod.unsigned (N.v38042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38042 s i)) at 1.
  unfold R.v38042, N.v38042.
  rewrite ?node_38040.
  rewrite ?node_38041.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38043 (s : N.State) (i : N.Inputs) :
  R.v38043 (state s) (inputs i) = Zmod.unsigned (N.v38043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38043 s i)) at 1.
  unfold R.v38043, N.v38043.
  rewrite ?node_38039.
  rewrite ?node_38042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38044 (s : N.State) (i : N.Inputs) :
  R.v38044 (state s) (inputs i) = Zmod.unsigned (N.v38044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38044 s i)) at 1.
  unfold R.v38044, N.v38044.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38045 (s : N.State) (i : N.Inputs) :
  R.v38045 (state s) (inputs i) = Zmod.unsigned (N.v38045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38045 s i)) at 1.
  unfold R.v38045, N.v38045.
  rewrite ?node_5528.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38046 (s : N.State) (i : N.Inputs) :
  R.v38046 (state s) (inputs i) = Zmod.unsigned (N.v38046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38046 s i)) at 1.
  unfold R.v38046, N.v38046.
  rewrite ?node_5524.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38047 (s : N.State) (i : N.Inputs) :
  R.v38047 (state s) (inputs i) = Zmod.unsigned (N.v38047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38047 s i)) at 1.
  unfold R.v38047, N.v38047.
  rewrite ?node_5520.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38048 (s : N.State) (i : N.Inputs) :
  R.v38048 (state s) (inputs i) = Zmod.unsigned (N.v38048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38048 s i)) at 1.
  unfold R.v38048, N.v38048.
  unfold R.v6, N.v6.
  rewrite ?node_5518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38049 (s : N.State) (i : N.Inputs) :
  R.v38049 (state s) (inputs i) = Zmod.unsigned (N.v38049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38049 s i)) at 1.
  unfold R.v38049, N.v38049.
  unfold R.v6, N.v6.
  rewrite ?node_5511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38050 (s : N.State) (i : N.Inputs) :
  R.v38050 (state s) (inputs i) = Zmod.unsigned (N.v38050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38050 s i)) at 1.
  unfold R.v38050, N.v38050.
  rewrite ?node_38048.
  rewrite ?node_38049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38051 (s : N.State) (i : N.Inputs) :
  R.v38051 (state s) (inputs i) = Zmod.unsigned (N.v38051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38051 s i)) at 1.
  unfold R.v38051, N.v38051.
  unfold R.v16484, N.v16484.
  rewrite ?node_38050.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38052 (s : N.State) (i : N.Inputs) :
  R.v38052 (state s) (inputs i) = Zmod.unsigned (N.v38052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38052 s i)) at 1.
  unfold R.v38052, N.v38052.
  rewrite ?node_38045.
  rewrite ?node_38046.
  rewrite ?node_38047.
  rewrite ?node_38051.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38053 (s : N.State) (i : N.Inputs) :
  R.v38053 (state s) (inputs i) = Zmod.unsigned (N.v38053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38053 s i)) at 1.
  unfold R.v38053, N.v38053.
  unfold R.v6, N.v6.
  rewrite ?node_38052.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38054 (s : N.State) (i : N.Inputs) :
  R.v38054 (state s) (inputs i) = Zmod.unsigned (N.v38054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38054 s i)) at 1.
  unfold R.v38054, N.v38054.
  rewrite ?node_5529.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38055 (s : N.State) (i : N.Inputs) :
  R.v38055 (state s) (inputs i) = Zmod.unsigned (N.v38055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38055 s i)) at 1.
  unfold R.v38055, N.v38055.
  unfold R.v6, N.v6.
  rewrite ?node_5573.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38056 (s : N.State) (i : N.Inputs) :
  R.v38056 (state s) (inputs i) = Zmod.unsigned (N.v38056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38056 s i)) at 1.
  unfold R.v38056, N.v38056.
  unfold R.v6, N.v6.
  rewrite ?node_5583.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38057 (s : N.State) (i : N.Inputs) :
  R.v38057 (state s) (inputs i) = Zmod.unsigned (N.v38057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38057 s i)) at 1.
  unfold R.v38057, N.v38057.
  rewrite ?node_38054.
  rewrite ?node_38055.
  rewrite ?node_38056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38058 (s : N.State) (i : N.Inputs) :
  R.v38058 (state s) (inputs i) = Zmod.unsigned (N.v38058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38058 s i)) at 1.
  unfold R.v38058, N.v38058.
  rewrite ?node_38053.
  rewrite ?node_38057.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38059 (s : N.State) (i : N.Inputs) :
  R.v38059 (state s) (inputs i) = Zmod.unsigned (N.v38059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38059 s i)) at 1.
  unfold R.v38059, N.v38059.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38060 (s : N.State) (i : N.Inputs) :
  R.v38060 (state s) (inputs i) = Zmod.unsigned (N.v38060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38060 s i)) at 1.
  unfold R.v38060, N.v38060.
  rewrite ?node_5520.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38061 (s : N.State) (i : N.Inputs) :
  R.v38061 (state s) (inputs i) = Zmod.unsigned (N.v38061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38061 s i)) at 1.
  unfold R.v38061, N.v38061.
  unfold R.v6, N.v6.
  rewrite ?node_5518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38062 (s : N.State) (i : N.Inputs) :
  R.v38062 (state s) (inputs i) = Zmod.unsigned (N.v38062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38062 s i)) at 1.
  unfold R.v38062, N.v38062.
  unfold R.v6, N.v6.
  rewrite ?node_5511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38063 (s : N.State) (i : N.Inputs) :
  R.v38063 (state s) (inputs i) = Zmod.unsigned (N.v38063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38063 s i)) at 1.
  unfold R.v38063, N.v38063.
  rewrite ?node_38061.
  rewrite ?node_38062.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38064 (s : N.State) (i : N.Inputs) :
  R.v38064 (state s) (inputs i) = Zmod.unsigned (N.v38064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38064 s i)) at 1.
  unfold R.v38064, N.v38064.
  unfold R.v16484, N.v16484.
  rewrite ?node_38063.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38065 (s : N.State) (i : N.Inputs) :
  R.v38065 (state s) (inputs i) = Zmod.unsigned (N.v38065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38065 s i)) at 1.
  unfold R.v38065, N.v38065.
  rewrite ?node_38060.
  rewrite ?node_38064.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38066 (s : N.State) (i : N.Inputs) :
  R.v38066 (state s) (inputs i) = Zmod.unsigned (N.v38066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38066 s i)) at 1.
  unfold R.v38066, N.v38066.
  unfold R.v6, N.v6.
  rewrite ?node_38065.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38067 (s : N.State) (i : N.Inputs) :
  R.v38067 (state s) (inputs i) = Zmod.unsigned (N.v38067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38067 s i)) at 1.
  unfold R.v38067, N.v38067.
  rewrite ?node_5521.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38068 (s : N.State) (i : N.Inputs) :
  R.v38068 (state s) (inputs i) = Zmod.unsigned (N.v38068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38068 s i)) at 1.
  unfold R.v38068, N.v38068.
  unfold R.v6, N.v6.
  rewrite ?node_5573.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38069 (s : N.State) (i : N.Inputs) :
  R.v38069 (state s) (inputs i) = Zmod.unsigned (N.v38069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38069 s i)) at 1.
  unfold R.v38069, N.v38069.
  rewrite ?node_38067.
  rewrite ?node_38068.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38070 (s : N.State) (i : N.Inputs) :
  R.v38070 (state s) (inputs i) = Zmod.unsigned (N.v38070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38070 s i)) at 1.
  unfold R.v38070, N.v38070.
  rewrite ?node_38066.
  rewrite ?node_38069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38071 (s : N.State) (i : N.Inputs) :
  R.v38071 (state s) (inputs i) = Zmod.unsigned (N.v38071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38071 s i)) at 1.
  unfold R.v38071, N.v38071.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38072 (s : N.State) (i : N.Inputs) :
  R.v38072 (state s) (inputs i) = Zmod.unsigned (N.v38072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38072 s i)) at 1.
  unfold R.v38072, N.v38072.
  rewrite ?node_5528.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38073 (s : N.State) (i : N.Inputs) :
  R.v38073 (state s) (inputs i) = Zmod.unsigned (N.v38073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38073 s i)) at 1.
  unfold R.v38073, N.v38073.
  unfold R.v6, N.v6.
  rewrite ?node_5524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38074 (s : N.State) (i : N.Inputs) :
  R.v38074 (state s) (inputs i) = Zmod.unsigned (N.v38074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38074 s i)) at 1.
  unfold R.v38074, N.v38074.
  unfold R.v6, N.v6.
  rewrite ?node_5521.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38075 (s : N.State) (i : N.Inputs) :
  R.v38075 (state s) (inputs i) = Zmod.unsigned (N.v38075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38075 s i)) at 1.
  unfold R.v38075, N.v38075.
  rewrite ?node_38073.
  rewrite ?node_38074.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38076 (s : N.State) (i : N.Inputs) :
  R.v38076 (state s) (inputs i) = Zmod.unsigned (N.v38076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38076 s i)) at 1.
  unfold R.v38076, N.v38076.
  unfold R.v16484, N.v16484.
  rewrite ?node_38075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38077 (s : N.State) (i : N.Inputs) :
  R.v38077 (state s) (inputs i) = Zmod.unsigned (N.v38077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38077 s i)) at 1.
  unfold R.v38077, N.v38077.
  rewrite ?node_38072.
  rewrite ?node_38076.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38078 (s : N.State) (i : N.Inputs) :
  R.v38078 (state s) (inputs i) = Zmod.unsigned (N.v38078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38078 s i)) at 1.
  unfold R.v38078, N.v38078.
  unfold R.v6, N.v6.
  rewrite ?node_38077.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38079 (s : N.State) (i : N.Inputs) :
  R.v38079 (state s) (inputs i) = Zmod.unsigned (N.v38079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38079 s i)) at 1.
  unfold R.v38079, N.v38079.
  rewrite ?node_5529.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38080 (s : N.State) (i : N.Inputs) :
  R.v38080 (state s) (inputs i) = Zmod.unsigned (N.v38080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38080 s i)) at 1.
  unfold R.v38080, N.v38080.
  unfold R.v6, N.v6.
  rewrite ?node_5583.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38081 (s : N.State) (i : N.Inputs) :
  R.v38081 (state s) (inputs i) = Zmod.unsigned (N.v38081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38081 s i)) at 1.
  unfold R.v38081, N.v38081.
  rewrite ?node_38079.
  rewrite ?node_38080.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38082 (s : N.State) (i : N.Inputs) :
  R.v38082 (state s) (inputs i) = Zmod.unsigned (N.v38082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38082 s i)) at 1.
  unfold R.v38082, N.v38082.
  rewrite ?node_38078.
  rewrite ?node_38081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38083 (s : N.State) (i : N.Inputs) :
  R.v38083 (state s) (inputs i) = Zmod.unsigned (N.v38083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38083 s i)) at 1.
  unfold R.v38083, N.v38083.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38084 (s : N.State) (i : N.Inputs) :
  R.v38084 (state s) (inputs i) = Zmod.unsigned (N.v38084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38084 s i)) at 1.
  unfold R.v38084, N.v38084.
  unfold R.v6, N.v6.
  rewrite ?node_5533.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38085 (s : N.State) (i : N.Inputs) :
  R.v38085 (state s) (inputs i) = Zmod.unsigned (N.v38085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38085 s i)) at 1.
  unfold R.v38085, N.v38085.
  unfold R.v6, N.v6.
  rewrite ?node_5532.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38086 (s : N.State) (i : N.Inputs) :
  R.v38086 (state s) (inputs i) = Zmod.unsigned (N.v38086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38086 s i)) at 1.
  unfold R.v38086, N.v38086.
  rewrite ?node_38084.
  rewrite ?node_38085.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38087 (s : N.State) (i : N.Inputs) :
  R.v38087 (state s) (inputs i) = Zmod.unsigned (N.v38087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38087 s i)) at 1.
  unfold R.v38087, N.v38087.
  unfold R.v16463, N.v16463.
  rewrite ?node_38086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38088 (s : N.State) (i : N.Inputs) :
  R.v38088 (state s) (inputs i) = Zmod.unsigned (N.v38088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38088 s i)) at 1.
  unfold R.v38088, N.v38088.
  rewrite ?node_5534.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38089 (s : N.State) (i : N.Inputs) :
  R.v38089 (state s) (inputs i) = Zmod.unsigned (N.v38089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38089 s i)) at 1.
  unfold R.v38089, N.v38089.
  unfold R.v6, N.v6.
  rewrite ?node_5585.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38090 (s : N.State) (i : N.Inputs) :
  R.v38090 (state s) (inputs i) = Zmod.unsigned (N.v38090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38090 s i)) at 1.
  unfold R.v38090, N.v38090.
  rewrite ?node_38088.
  rewrite ?node_38089.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38091 (s : N.State) (i : N.Inputs) :
  R.v38091 (state s) (inputs i) = Zmod.unsigned (N.v38091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38091 s i)) at 1.
  unfold R.v38091, N.v38091.
  rewrite ?node_38087.
  rewrite ?node_38090.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38092 (s : N.State) (i : N.Inputs) :
  R.v38092 (state s) (inputs i) = Zmod.unsigned (N.v38092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38092 s i)) at 1.
  unfold R.v38092, N.v38092.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38093 (s : N.State) (i : N.Inputs) :
  R.v38093 (state s) (inputs i) = Zmod.unsigned (N.v38093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38093 s i)) at 1.
  unfold R.v38093, N.v38093.
  rewrite ?node_5573.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38094 (s : N.State) (i : N.Inputs) :
  R.v38094 (state s) (inputs i) = Zmod.unsigned (N.v38094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38094 s i)) at 1.
  unfold R.v38094, N.v38094.
  rewrite ?node_5569.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38095 (s : N.State) (i : N.Inputs) :
  R.v38095 (state s) (inputs i) = Zmod.unsigned (N.v38095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38095 s i)) at 1.
  unfold R.v38095, N.v38095.
  rewrite ?node_5565.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38096 (s : N.State) (i : N.Inputs) :
  R.v38096 (state s) (inputs i) = Zmod.unsigned (N.v38096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38096 s i)) at 1.
  unfold R.v38096, N.v38096.
  unfold R.v6, N.v6.
  rewrite ?node_5562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38097 (s : N.State) (i : N.Inputs) :
  R.v38097 (state s) (inputs i) = Zmod.unsigned (N.v38097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38097 s i)) at 1.
  unfold R.v38097, N.v38097.
  unfold R.v6, N.v6.
  rewrite ?node_5555.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38098 (s : N.State) (i : N.Inputs) :
  R.v38098 (state s) (inputs i) = Zmod.unsigned (N.v38098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38098 s i)) at 1.
  unfold R.v38098, N.v38098.
  rewrite ?node_38096.
  rewrite ?node_38097.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38099 (s : N.State) (i : N.Inputs) :
  R.v38099 (state s) (inputs i) = Zmod.unsigned (N.v38099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38099 s i)) at 1.
  unfold R.v38099, N.v38099.
  unfold R.v16484, N.v16484.
  rewrite ?node_38098.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38100 (s : N.State) (i : N.Inputs) :
  R.v38100 (state s) (inputs i) = Zmod.unsigned (N.v38100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38100 s i)) at 1.
  unfold R.v38100, N.v38100.
  rewrite ?node_38093.
  rewrite ?node_38094.
  rewrite ?node_38095.
  rewrite ?node_38099.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38101 (s : N.State) (i : N.Inputs) :
  R.v38101 (state s) (inputs i) = Zmod.unsigned (N.v38101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38101 s i)) at 1.
  unfold R.v38101, N.v38101.
  unfold R.v6, N.v6.
  rewrite ?node_38100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38102 (s : N.State) (i : N.Inputs) :
  R.v38102 (state s) (inputs i) = Zmod.unsigned (N.v38102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38102 s i)) at 1.
  unfold R.v38102, N.v38102.
  rewrite ?node_5574.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38103 (s : N.State) (i : N.Inputs) :
  R.v38103 (state s) (inputs i) = Zmod.unsigned (N.v38103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38103 s i)) at 1.
  unfold R.v38103, N.v38103.
  unfold R.v6, N.v6.
  rewrite ?node_5620.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38104 (s : N.State) (i : N.Inputs) :
  R.v38104 (state s) (inputs i) = Zmod.unsigned (N.v38104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38104 s i)) at 1.
  unfold R.v38104, N.v38104.
  unfold R.v6, N.v6.
  rewrite ?node_5632.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38105 (s : N.State) (i : N.Inputs) :
  R.v38105 (state s) (inputs i) = Zmod.unsigned (N.v38105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38105 s i)) at 1.
  unfold R.v38105, N.v38105.
  rewrite ?node_38102.
  rewrite ?node_38103.
  rewrite ?node_38104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38106 (s : N.State) (i : N.Inputs) :
  R.v38106 (state s) (inputs i) = Zmod.unsigned (N.v38106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38106 s i)) at 1.
  unfold R.v38106, N.v38106.
  rewrite ?node_38101.
  rewrite ?node_38105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38107 (s : N.State) (i : N.Inputs) :
  R.v38107 (state s) (inputs i) = Zmod.unsigned (N.v38107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38107 s i)) at 1.
  unfold R.v38107, N.v38107.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38108 (s : N.State) (i : N.Inputs) :
  R.v38108 (state s) (inputs i) = Zmod.unsigned (N.v38108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38108 s i)) at 1.
  unfold R.v38108, N.v38108.
  rewrite ?node_5565.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38109 (s : N.State) (i : N.Inputs) :
  R.v38109 (state s) (inputs i) = Zmod.unsigned (N.v38109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38109 s i)) at 1.
  unfold R.v38109, N.v38109.
  unfold R.v6, N.v6.
  rewrite ?node_5562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38110 (s : N.State) (i : N.Inputs) :
  R.v38110 (state s) (inputs i) = Zmod.unsigned (N.v38110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38110 s i)) at 1.
  unfold R.v38110, N.v38110.
  unfold R.v6, N.v6.
  rewrite ?node_5555.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38111 (s : N.State) (i : N.Inputs) :
  R.v38111 (state s) (inputs i) = Zmod.unsigned (N.v38111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38111 s i)) at 1.
  unfold R.v38111, N.v38111.
  rewrite ?node_38109.
  rewrite ?node_38110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38112 (s : N.State) (i : N.Inputs) :
  R.v38112 (state s) (inputs i) = Zmod.unsigned (N.v38112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38112 s i)) at 1.
  unfold R.v38112, N.v38112.
  unfold R.v16484, N.v16484.
  rewrite ?node_38111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38113 (s : N.State) (i : N.Inputs) :
  R.v38113 (state s) (inputs i) = Zmod.unsigned (N.v38113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38113 s i)) at 1.
  unfold R.v38113, N.v38113.
  rewrite ?node_38108.
  rewrite ?node_38112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38114 (s : N.State) (i : N.Inputs) :
  R.v38114 (state s) (inputs i) = Zmod.unsigned (N.v38114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38114 s i)) at 1.
  unfold R.v38114, N.v38114.
  unfold R.v6, N.v6.
  rewrite ?node_38113.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38115 (s : N.State) (i : N.Inputs) :
  R.v38115 (state s) (inputs i) = Zmod.unsigned (N.v38115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38115 s i)) at 1.
  unfold R.v38115, N.v38115.
  rewrite ?node_5566.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38116 (s : N.State) (i : N.Inputs) :
  R.v38116 (state s) (inputs i) = Zmod.unsigned (N.v38116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38116 s i)) at 1.
  unfold R.v38116, N.v38116.
  unfold R.v6, N.v6.
  rewrite ?node_5620.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38117 (s : N.State) (i : N.Inputs) :
  R.v38117 (state s) (inputs i) = Zmod.unsigned (N.v38117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38117 s i)) at 1.
  unfold R.v38117, N.v38117.
  rewrite ?node_38115.
  rewrite ?node_38116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38118 (s : N.State) (i : N.Inputs) :
  R.v38118 (state s) (inputs i) = Zmod.unsigned (N.v38118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38118 s i)) at 1.
  unfold R.v38118, N.v38118.
  rewrite ?node_38114.
  rewrite ?node_38117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38119 (s : N.State) (i : N.Inputs) :
  R.v38119 (state s) (inputs i) = Zmod.unsigned (N.v38119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38119 s i)) at 1.
  unfold R.v38119, N.v38119.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38120 (s : N.State) (i : N.Inputs) :
  R.v38120 (state s) (inputs i) = Zmod.unsigned (N.v38120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38120 s i)) at 1.
  unfold R.v38120, N.v38120.
  rewrite ?node_5573.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38121 (s : N.State) (i : N.Inputs) :
  R.v38121 (state s) (inputs i) = Zmod.unsigned (N.v38121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38121 s i)) at 1.
  unfold R.v38121, N.v38121.
  unfold R.v6, N.v6.
  rewrite ?node_5569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38122 (s : N.State) (i : N.Inputs) :
  R.v38122 (state s) (inputs i) = Zmod.unsigned (N.v38122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38122 s i)) at 1.
  unfold R.v38122, N.v38122.
  unfold R.v6, N.v6.
  rewrite ?node_5566.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38123 (s : N.State) (i : N.Inputs) :
  R.v38123 (state s) (inputs i) = Zmod.unsigned (N.v38123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38123 s i)) at 1.
  unfold R.v38123, N.v38123.
  rewrite ?node_38121.
  rewrite ?node_38122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38124 (s : N.State) (i : N.Inputs) :
  R.v38124 (state s) (inputs i) = Zmod.unsigned (N.v38124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38124 s i)) at 1.
  unfold R.v38124, N.v38124.
  unfold R.v16484, N.v16484.
  rewrite ?node_38123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38125 (s : N.State) (i : N.Inputs) :
  R.v38125 (state s) (inputs i) = Zmod.unsigned (N.v38125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38125 s i)) at 1.
  unfold R.v38125, N.v38125.
  rewrite ?node_38120.
  rewrite ?node_38124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38126 (s : N.State) (i : N.Inputs) :
  R.v38126 (state s) (inputs i) = Zmod.unsigned (N.v38126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38126 s i)) at 1.
  unfold R.v38126, N.v38126.
  unfold R.v6, N.v6.
  rewrite ?node_38125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38127 (s : N.State) (i : N.Inputs) :
  R.v38127 (state s) (inputs i) = Zmod.unsigned (N.v38127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38127 s i)) at 1.
  unfold R.v38127, N.v38127.
  rewrite ?node_5574.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38128 (s : N.State) (i : N.Inputs) :
  R.v38128 (state s) (inputs i) = Zmod.unsigned (N.v38128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38128 s i)) at 1.
  unfold R.v38128, N.v38128.
  unfold R.v6, N.v6.
  rewrite ?node_5632.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38129 (s : N.State) (i : N.Inputs) :
  R.v38129 (state s) (inputs i) = Zmod.unsigned (N.v38129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38129 s i)) at 1.
  unfold R.v38129, N.v38129.
  rewrite ?node_38127.
  rewrite ?node_38128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38130 (s : N.State) (i : N.Inputs) :
  R.v38130 (state s) (inputs i) = Zmod.unsigned (N.v38130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38130 s i)) at 1.
  unfold R.v38130, N.v38130.
  rewrite ?node_38126.
  rewrite ?node_38129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38131 (s : N.State) (i : N.Inputs) :
  R.v38131 (state s) (inputs i) = Zmod.unsigned (N.v38131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38131 s i)) at 1.
  unfold R.v38131, N.v38131.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38132 (s : N.State) (i : N.Inputs) :
  R.v38132 (state s) (inputs i) = Zmod.unsigned (N.v38132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38132 s i)) at 1.
  unfold R.v38132, N.v38132.
  unfold R.v6, N.v6.
  rewrite ?node_5578.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38133 (s : N.State) (i : N.Inputs) :
  R.v38133 (state s) (inputs i) = Zmod.unsigned (N.v38133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38133 s i)) at 1.
  unfold R.v38133, N.v38133.
  unfold R.v6, N.v6.
  rewrite ?node_5577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38134 (s : N.State) (i : N.Inputs) :
  R.v38134 (state s) (inputs i) = Zmod.unsigned (N.v38134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38134 s i)) at 1.
  unfold R.v38134, N.v38134.
  rewrite ?node_38132.
  rewrite ?node_38133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38135 (s : N.State) (i : N.Inputs) :
  R.v38135 (state s) (inputs i) = Zmod.unsigned (N.v38135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38135 s i)) at 1.
  unfold R.v38135, N.v38135.
  unfold R.v16463, N.v16463.
  rewrite ?node_38134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38136 (s : N.State) (i : N.Inputs) :
  R.v38136 (state s) (inputs i) = Zmod.unsigned (N.v38136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38136 s i)) at 1.
  unfold R.v38136, N.v38136.
  rewrite ?node_5579.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38137 (s : N.State) (i : N.Inputs) :
  R.v38137 (state s) (inputs i) = Zmod.unsigned (N.v38137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38137 s i)) at 1.
  unfold R.v38137, N.v38137.
  unfold R.v6, N.v6.
  rewrite ?node_5634.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38138 (s : N.State) (i : N.Inputs) :
  R.v38138 (state s) (inputs i) = Zmod.unsigned (N.v38138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38138 s i)) at 1.
  unfold R.v38138, N.v38138.
  rewrite ?node_38136.
  rewrite ?node_38137.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38139 (s : N.State) (i : N.Inputs) :
  R.v38139 (state s) (inputs i) = Zmod.unsigned (N.v38139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38139 s i)) at 1.
  unfold R.v38139, N.v38139.
  rewrite ?node_38135.
  rewrite ?node_38138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38140 (s : N.State) (i : N.Inputs) :
  R.v38140 (state s) (inputs i) = Zmod.unsigned (N.v38140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38140 s i)) at 1.
  unfold R.v38140, N.v38140.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38141 (s : N.State) (i : N.Inputs) :
  R.v38141 (state s) (inputs i) = Zmod.unsigned (N.v38141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38141 s i)) at 1.
  unfold R.v38141, N.v38141.
  rewrite ?node_5620.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38142 (s : N.State) (i : N.Inputs) :
  R.v38142 (state s) (inputs i) = Zmod.unsigned (N.v38142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38142 s i)) at 1.
  unfold R.v38142, N.v38142.
  rewrite ?node_5616.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38143 (s : N.State) (i : N.Inputs) :
  R.v38143 (state s) (inputs i) = Zmod.unsigned (N.v38143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38143 s i)) at 1.
  unfold R.v38143, N.v38143.
  rewrite ?node_5612.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38144 (s : N.State) (i : N.Inputs) :
  R.v38144 (state s) (inputs i) = Zmod.unsigned (N.v38144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38144 s i)) at 1.
  unfold R.v38144, N.v38144.
  unfold R.v6, N.v6.
  rewrite ?node_5609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38145 (s : N.State) (i : N.Inputs) :
  R.v38145 (state s) (inputs i) = Zmod.unsigned (N.v38145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38145 s i)) at 1.
  unfold R.v38145, N.v38145.
  unfold R.v6, N.v6.
  rewrite ?node_5602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38146 (s : N.State) (i : N.Inputs) :
  R.v38146 (state s) (inputs i) = Zmod.unsigned (N.v38146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38146 s i)) at 1.
  unfold R.v38146, N.v38146.
  rewrite ?node_38144.
  rewrite ?node_38145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38147 (s : N.State) (i : N.Inputs) :
  R.v38147 (state s) (inputs i) = Zmod.unsigned (N.v38147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38147 s i)) at 1.
  unfold R.v38147, N.v38147.
  unfold R.v16484, N.v16484.
  rewrite ?node_38146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38148 (s : N.State) (i : N.Inputs) :
  R.v38148 (state s) (inputs i) = Zmod.unsigned (N.v38148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38148 s i)) at 1.
  unfold R.v38148, N.v38148.
  rewrite ?node_38141.
  rewrite ?node_38142.
  rewrite ?node_38143.
  rewrite ?node_38147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38149 (s : N.State) (i : N.Inputs) :
  R.v38149 (state s) (inputs i) = Zmod.unsigned (N.v38149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38149 s i)) at 1.
  unfold R.v38149, N.v38149.
  unfold R.v6, N.v6.
  rewrite ?node_38148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38150 (s : N.State) (i : N.Inputs) :
  R.v38150 (state s) (inputs i) = Zmod.unsigned (N.v38150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38150 s i)) at 1.
  unfold R.v38150, N.v38150.
  rewrite ?node_5621.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38151 (s : N.State) (i : N.Inputs) :
  R.v38151 (state s) (inputs i) = Zmod.unsigned (N.v38151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38151 s i)) at 1.
  unfold R.v38151, N.v38151.
  unfold R.v6, N.v6.
  rewrite ?node_5672.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38152 (s : N.State) (i : N.Inputs) :
  R.v38152 (state s) (inputs i) = Zmod.unsigned (N.v38152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38152 s i)) at 1.
  unfold R.v38152, N.v38152.
  unfold R.v6, N.v6.
  rewrite ?node_5684.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38153 (s : N.State) (i : N.Inputs) :
  R.v38153 (state s) (inputs i) = Zmod.unsigned (N.v38153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38153 s i)) at 1.
  unfold R.v38153, N.v38153.
  rewrite ?node_38150.
  rewrite ?node_38151.
  rewrite ?node_38152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38154 (s : N.State) (i : N.Inputs) :
  R.v38154 (state s) (inputs i) = Zmod.unsigned (N.v38154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38154 s i)) at 1.
  unfold R.v38154, N.v38154.
  rewrite ?node_38149.
  rewrite ?node_38153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38155 (s : N.State) (i : N.Inputs) :
  R.v38155 (state s) (inputs i) = Zmod.unsigned (N.v38155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38155 s i)) at 1.
  unfold R.v38155, N.v38155.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38156 (s : N.State) (i : N.Inputs) :
  R.v38156 (state s) (inputs i) = Zmod.unsigned (N.v38156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38156 s i)) at 1.
  unfold R.v38156, N.v38156.
  rewrite ?node_5612.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38157 (s : N.State) (i : N.Inputs) :
  R.v38157 (state s) (inputs i) = Zmod.unsigned (N.v38157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38157 s i)) at 1.
  unfold R.v38157, N.v38157.
  unfold R.v6, N.v6.
  rewrite ?node_5609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38158 (s : N.State) (i : N.Inputs) :
  R.v38158 (state s) (inputs i) = Zmod.unsigned (N.v38158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38158 s i)) at 1.
  unfold R.v38158, N.v38158.
  unfold R.v6, N.v6.
  rewrite ?node_5602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38159 (s : N.State) (i : N.Inputs) :
  R.v38159 (state s) (inputs i) = Zmod.unsigned (N.v38159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38159 s i)) at 1.
  unfold R.v38159, N.v38159.
  rewrite ?node_38157.
  rewrite ?node_38158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38160 (s : N.State) (i : N.Inputs) :
  R.v38160 (state s) (inputs i) = Zmod.unsigned (N.v38160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38160 s i)) at 1.
  unfold R.v38160, N.v38160.
  unfold R.v16484, N.v16484.
  rewrite ?node_38159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38161 (s : N.State) (i : N.Inputs) :
  R.v38161 (state s) (inputs i) = Zmod.unsigned (N.v38161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38161 s i)) at 1.
  unfold R.v38161, N.v38161.
  rewrite ?node_38156.
  rewrite ?node_38160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38162 (s : N.State) (i : N.Inputs) :
  R.v38162 (state s) (inputs i) = Zmod.unsigned (N.v38162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38162 s i)) at 1.
  unfold R.v38162, N.v38162.
  unfold R.v6, N.v6.
  rewrite ?node_38161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38163 (s : N.State) (i : N.Inputs) :
  R.v38163 (state s) (inputs i) = Zmod.unsigned (N.v38163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38163 s i)) at 1.
  unfold R.v38163, N.v38163.
  rewrite ?node_5613.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38164 (s : N.State) (i : N.Inputs) :
  R.v38164 (state s) (inputs i) = Zmod.unsigned (N.v38164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38164 s i)) at 1.
  unfold R.v38164, N.v38164.
  unfold R.v6, N.v6.
  rewrite ?node_5672.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38165 (s : N.State) (i : N.Inputs) :
  R.v38165 (state s) (inputs i) = Zmod.unsigned (N.v38165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38165 s i)) at 1.
  unfold R.v38165, N.v38165.
  rewrite ?node_38163.
  rewrite ?node_38164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38166 (s : N.State) (i : N.Inputs) :
  R.v38166 (state s) (inputs i) = Zmod.unsigned (N.v38166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38166 s i)) at 1.
  unfold R.v38166, N.v38166.
  rewrite ?node_38162.
  rewrite ?node_38165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38167 (s : N.State) (i : N.Inputs) :
  R.v38167 (state s) (inputs i) = Zmod.unsigned (N.v38167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38167 s i)) at 1.
  unfold R.v38167, N.v38167.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38168 (s : N.State) (i : N.Inputs) :
  R.v38168 (state s) (inputs i) = Zmod.unsigned (N.v38168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38168 s i)) at 1.
  unfold R.v38168, N.v38168.
  rewrite ?node_5620.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38169 (s : N.State) (i : N.Inputs) :
  R.v38169 (state s) (inputs i) = Zmod.unsigned (N.v38169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38169 s i)) at 1.
  unfold R.v38169, N.v38169.
  unfold R.v6, N.v6.
  rewrite ?node_5616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38170 (s : N.State) (i : N.Inputs) :
  R.v38170 (state s) (inputs i) = Zmod.unsigned (N.v38170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38170 s i)) at 1.
  unfold R.v38170, N.v38170.
  unfold R.v6, N.v6.
  rewrite ?node_5613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38171 (s : N.State) (i : N.Inputs) :
  R.v38171 (state s) (inputs i) = Zmod.unsigned (N.v38171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38171 s i)) at 1.
  unfold R.v38171, N.v38171.
  rewrite ?node_38169.
  rewrite ?node_38170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38172 (s : N.State) (i : N.Inputs) :
  R.v38172 (state s) (inputs i) = Zmod.unsigned (N.v38172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38172 s i)) at 1.
  unfold R.v38172, N.v38172.
  unfold R.v16484, N.v16484.
  rewrite ?node_38171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38173 (s : N.State) (i : N.Inputs) :
  R.v38173 (state s) (inputs i) = Zmod.unsigned (N.v38173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38173 s i)) at 1.
  unfold R.v38173, N.v38173.
  rewrite ?node_38168.
  rewrite ?node_38172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38174 (s : N.State) (i : N.Inputs) :
  R.v38174 (state s) (inputs i) = Zmod.unsigned (N.v38174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38174 s i)) at 1.
  unfold R.v38174, N.v38174.
  unfold R.v6, N.v6.
  rewrite ?node_38173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38175 (s : N.State) (i : N.Inputs) :
  R.v38175 (state s) (inputs i) = Zmod.unsigned (N.v38175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38175 s i)) at 1.
  unfold R.v38175, N.v38175.
  rewrite ?node_5621.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38176 (s : N.State) (i : N.Inputs) :
  R.v38176 (state s) (inputs i) = Zmod.unsigned (N.v38176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38176 s i)) at 1.
  unfold R.v38176, N.v38176.
  unfold R.v6, N.v6.
  rewrite ?node_5684.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38177 (s : N.State) (i : N.Inputs) :
  R.v38177 (state s) (inputs i) = Zmod.unsigned (N.v38177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38177 s i)) at 1.
  unfold R.v38177, N.v38177.
  rewrite ?node_38175.
  rewrite ?node_38176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38178 (s : N.State) (i : N.Inputs) :
  R.v38178 (state s) (inputs i) = Zmod.unsigned (N.v38178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38178 s i)) at 1.
  unfold R.v38178, N.v38178.
  rewrite ?node_38174.
  rewrite ?node_38177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38179 (s : N.State) (i : N.Inputs) :
  R.v38179 (state s) (inputs i) = Zmod.unsigned (N.v38179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38179 s i)) at 1.
  unfold R.v38179, N.v38179.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38180 (s : N.State) (i : N.Inputs) :
  R.v38180 (state s) (inputs i) = Zmod.unsigned (N.v38180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38180 s i)) at 1.
  unfold R.v38180, N.v38180.
  unfold R.v6, N.v6.
  rewrite ?node_5627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38181 (s : N.State) (i : N.Inputs) :
  R.v38181 (state s) (inputs i) = Zmod.unsigned (N.v38181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38181 s i)) at 1.
  unfold R.v38181, N.v38181.
  unfold R.v6, N.v6.
  rewrite ?node_5624.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38182 (s : N.State) (i : N.Inputs) :
  R.v38182 (state s) (inputs i) = Zmod.unsigned (N.v38182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38182 s i)) at 1.
  unfold R.v38182, N.v38182.
  rewrite ?node_38180.
  rewrite ?node_38181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38183 (s : N.State) (i : N.Inputs) :
  R.v38183 (state s) (inputs i) = Zmod.unsigned (N.v38183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38183 s i)) at 1.
  unfold R.v38183, N.v38183.
  unfold R.v16463, N.v16463.
  rewrite ?node_38182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38184 (s : N.State) (i : N.Inputs) :
  R.v38184 (state s) (inputs i) = Zmod.unsigned (N.v38184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38184 s i)) at 1.
  unfold R.v38184, N.v38184.
  rewrite ?node_5628.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38185 (s : N.State) (i : N.Inputs) :
  R.v38185 (state s) (inputs i) = Zmod.unsigned (N.v38185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38185 s i)) at 1.
  unfold R.v38185, N.v38185.
  unfold R.v6, N.v6.
  rewrite ?node_5686.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38186 (s : N.State) (i : N.Inputs) :
  R.v38186 (state s) (inputs i) = Zmod.unsigned (N.v38186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38186 s i)) at 1.
  unfold R.v38186, N.v38186.
  rewrite ?node_38184.
  rewrite ?node_38185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38187 (s : N.State) (i : N.Inputs) :
  R.v38187 (state s) (inputs i) = Zmod.unsigned (N.v38187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38187 s i)) at 1.
  unfold R.v38187, N.v38187.
  rewrite ?node_38183.
  rewrite ?node_38186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38188 (s : N.State) (i : N.Inputs) :
  R.v38188 (state s) (inputs i) = Zmod.unsigned (N.v38188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38188 s i)) at 1.
  unfold R.v38188, N.v38188.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38189 (s : N.State) (i : N.Inputs) :
  R.v38189 (state s) (inputs i) = Zmod.unsigned (N.v38189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38189 s i)) at 1.
  unfold R.v38189, N.v38189.
  rewrite ?node_5672.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38190 (s : N.State) (i : N.Inputs) :
  R.v38190 (state s) (inputs i) = Zmod.unsigned (N.v38190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38190 s i)) at 1.
  unfold R.v38190, N.v38190.
  rewrite ?node_5668.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38191 (s : N.State) (i : N.Inputs) :
  R.v38191 (state s) (inputs i) = Zmod.unsigned (N.v38191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38191 s i)) at 1.
  unfold R.v38191, N.v38191.
  rewrite ?node_5664.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38192 (s : N.State) (i : N.Inputs) :
  R.v38192 (state s) (inputs i) = Zmod.unsigned (N.v38192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38192 s i)) at 1.
  unfold R.v38192, N.v38192.
  unfold R.v6, N.v6.
  rewrite ?node_5660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38193 (s : N.State) (i : N.Inputs) :
  R.v38193 (state s) (inputs i) = Zmod.unsigned (N.v38193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38193 s i)) at 1.
  unfold R.v38193, N.v38193.
  unfold R.v6, N.v6.
  rewrite ?node_5653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38194 (s : N.State) (i : N.Inputs) :
  R.v38194 (state s) (inputs i) = Zmod.unsigned (N.v38194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38194 s i)) at 1.
  unfold R.v38194, N.v38194.
  rewrite ?node_38192.
  rewrite ?node_38193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38195 (s : N.State) (i : N.Inputs) :
  R.v38195 (state s) (inputs i) = Zmod.unsigned (N.v38195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38195 s i)) at 1.
  unfold R.v38195, N.v38195.
  unfold R.v16484, N.v16484.
  rewrite ?node_38194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38196 (s : N.State) (i : N.Inputs) :
  R.v38196 (state s) (inputs i) = Zmod.unsigned (N.v38196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38196 s i)) at 1.
  unfold R.v38196, N.v38196.
  rewrite ?node_38189.
  rewrite ?node_38190.
  rewrite ?node_38191.
  rewrite ?node_38195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38197 (s : N.State) (i : N.Inputs) :
  R.v38197 (state s) (inputs i) = Zmod.unsigned (N.v38197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38197 s i)) at 1.
  unfold R.v38197, N.v38197.
  unfold R.v6, N.v6.
  rewrite ?node_38196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38198 (s : N.State) (i : N.Inputs) :
  R.v38198 (state s) (inputs i) = Zmod.unsigned (N.v38198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38198 s i)) at 1.
  unfold R.v38198, N.v38198.
  rewrite ?node_5673.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38199 (s : N.State) (i : N.Inputs) :
  R.v38199 (state s) (inputs i) = Zmod.unsigned (N.v38199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38199 s i)) at 1.
  unfold R.v38199, N.v38199.
  unfold R.v6, N.v6.
  rewrite ?node_5730.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38200 (s : N.State) (i : N.Inputs) :
  R.v38200 (state s) (inputs i) = Zmod.unsigned (N.v38200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38200 s i)) at 1.
  unfold R.v38200, N.v38200.
  unfold R.v6, N.v6.
  rewrite ?node_5740.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38201 (s : N.State) (i : N.Inputs) :
  R.v38201 (state s) (inputs i) = Zmod.unsigned (N.v38201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38201 s i)) at 1.
  unfold R.v38201, N.v38201.
  rewrite ?node_38198.
  rewrite ?node_38199.
  rewrite ?node_38200.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38202 (s : N.State) (i : N.Inputs) :
  R.v38202 (state s) (inputs i) = Zmod.unsigned (N.v38202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38202 s i)) at 1.
  unfold R.v38202, N.v38202.
  rewrite ?node_38197.
  rewrite ?node_38201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38203 (s : N.State) (i : N.Inputs) :
  R.v38203 (state s) (inputs i) = Zmod.unsigned (N.v38203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38203 s i)) at 1.
  unfold R.v38203, N.v38203.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38204 (s : N.State) (i : N.Inputs) :
  R.v38204 (state s) (inputs i) = Zmod.unsigned (N.v38204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38204 s i)) at 1.
  unfold R.v38204, N.v38204.
  rewrite ?node_5664.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38205 (s : N.State) (i : N.Inputs) :
  R.v38205 (state s) (inputs i) = Zmod.unsigned (N.v38205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38205 s i)) at 1.
  unfold R.v38205, N.v38205.
  unfold R.v6, N.v6.
  rewrite ?node_5660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38206 (s : N.State) (i : N.Inputs) :
  R.v38206 (state s) (inputs i) = Zmod.unsigned (N.v38206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38206 s i)) at 1.
  unfold R.v38206, N.v38206.
  unfold R.v6, N.v6.
  rewrite ?node_5653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38207 (s : N.State) (i : N.Inputs) :
  R.v38207 (state s) (inputs i) = Zmod.unsigned (N.v38207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38207 s i)) at 1.
  unfold R.v38207, N.v38207.
  rewrite ?node_38205.
  rewrite ?node_38206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38208 (s : N.State) (i : N.Inputs) :
  R.v38208 (state s) (inputs i) = Zmod.unsigned (N.v38208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38208 s i)) at 1.
  unfold R.v38208, N.v38208.
  unfold R.v16484, N.v16484.
  rewrite ?node_38207.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38209 (s : N.State) (i : N.Inputs) :
  R.v38209 (state s) (inputs i) = Zmod.unsigned (N.v38209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38209 s i)) at 1.
  unfold R.v38209, N.v38209.
  rewrite ?node_38204.
  rewrite ?node_38208.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38210 (s : N.State) (i : N.Inputs) :
  R.v38210 (state s) (inputs i) = Zmod.unsigned (N.v38210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38210 s i)) at 1.
  unfold R.v38210, N.v38210.
  unfold R.v6, N.v6.
  rewrite ?node_38209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38211 (s : N.State) (i : N.Inputs) :
  R.v38211 (state s) (inputs i) = Zmod.unsigned (N.v38211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38211 s i)) at 1.
  unfold R.v38211, N.v38211.
  rewrite ?node_5665.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38212 (s : N.State) (i : N.Inputs) :
  R.v38212 (state s) (inputs i) = Zmod.unsigned (N.v38212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38212 s i)) at 1.
  unfold R.v38212, N.v38212.
  unfold R.v6, N.v6.
  rewrite ?node_5730.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38213 (s : N.State) (i : N.Inputs) :
  R.v38213 (state s) (inputs i) = Zmod.unsigned (N.v38213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38213 s i)) at 1.
  unfold R.v38213, N.v38213.
  rewrite ?node_38211.
  rewrite ?node_38212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38214 (s : N.State) (i : N.Inputs) :
  R.v38214 (state s) (inputs i) = Zmod.unsigned (N.v38214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38214 s i)) at 1.
  unfold R.v38214, N.v38214.
  rewrite ?node_38210.
  rewrite ?node_38213.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38215 (s : N.State) (i : N.Inputs) :
  R.v38215 (state s) (inputs i) = Zmod.unsigned (N.v38215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38215 s i)) at 1.
  unfold R.v38215, N.v38215.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38216 (s : N.State) (i : N.Inputs) :
  R.v38216 (state s) (inputs i) = Zmod.unsigned (N.v38216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38216 s i)) at 1.
  unfold R.v38216, N.v38216.
  rewrite ?node_5672.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38217 (s : N.State) (i : N.Inputs) :
  R.v38217 (state s) (inputs i) = Zmod.unsigned (N.v38217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38217 s i)) at 1.
  unfold R.v38217, N.v38217.
  unfold R.v6, N.v6.
  rewrite ?node_5668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38218 (s : N.State) (i : N.Inputs) :
  R.v38218 (state s) (inputs i) = Zmod.unsigned (N.v38218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38218 s i)) at 1.
  unfold R.v38218, N.v38218.
  unfold R.v6, N.v6.
  rewrite ?node_5665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38219 (s : N.State) (i : N.Inputs) :
  R.v38219 (state s) (inputs i) = Zmod.unsigned (N.v38219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38219 s i)) at 1.
  unfold R.v38219, N.v38219.
  rewrite ?node_38217.
  rewrite ?node_38218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38220 (s : N.State) (i : N.Inputs) :
  R.v38220 (state s) (inputs i) = Zmod.unsigned (N.v38220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38220 s i)) at 1.
  unfold R.v38220, N.v38220.
  unfold R.v16484, N.v16484.
  rewrite ?node_38219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38221 (s : N.State) (i : N.Inputs) :
  R.v38221 (state s) (inputs i) = Zmod.unsigned (N.v38221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38221 s i)) at 1.
  unfold R.v38221, N.v38221.
  rewrite ?node_38216.
  rewrite ?node_38220.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38222 (s : N.State) (i : N.Inputs) :
  R.v38222 (state s) (inputs i) = Zmod.unsigned (N.v38222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38222 s i)) at 1.
  unfold R.v38222, N.v38222.
  unfold R.v6, N.v6.
  rewrite ?node_38221.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38223 (s : N.State) (i : N.Inputs) :
  R.v38223 (state s) (inputs i) = Zmod.unsigned (N.v38223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38223 s i)) at 1.
  unfold R.v38223, N.v38223.
  rewrite ?node_5673.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38224 (s : N.State) (i : N.Inputs) :
  R.v38224 (state s) (inputs i) = Zmod.unsigned (N.v38224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38224 s i)) at 1.
  unfold R.v38224, N.v38224.
  unfold R.v6, N.v6.
  rewrite ?node_5740.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38225 (s : N.State) (i : N.Inputs) :
  R.v38225 (state s) (inputs i) = Zmod.unsigned (N.v38225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38225 s i)) at 1.
  unfold R.v38225, N.v38225.
  rewrite ?node_38223.
  rewrite ?node_38224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38226 (s : N.State) (i : N.Inputs) :
  R.v38226 (state s) (inputs i) = Zmod.unsigned (N.v38226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38226 s i)) at 1.
  unfold R.v38226, N.v38226.
  rewrite ?node_38222.
  rewrite ?node_38225.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38227 (s : N.State) (i : N.Inputs) :
  R.v38227 (state s) (inputs i) = Zmod.unsigned (N.v38227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38227 s i)) at 1.
  unfold R.v38227, N.v38227.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38228 (s : N.State) (i : N.Inputs) :
  R.v38228 (state s) (inputs i) = Zmod.unsigned (N.v38228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38228 s i)) at 1.
  unfold R.v38228, N.v38228.
  unfold R.v6, N.v6.
  rewrite ?node_5679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38229 (s : N.State) (i : N.Inputs) :
  R.v38229 (state s) (inputs i) = Zmod.unsigned (N.v38229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38229 s i)) at 1.
  unfold R.v38229, N.v38229.
  unfold R.v6, N.v6.
  rewrite ?node_5676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38230 (s : N.State) (i : N.Inputs) :
  R.v38230 (state s) (inputs i) = Zmod.unsigned (N.v38230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38230 s i)) at 1.
  unfold R.v38230, N.v38230.
  rewrite ?node_38228.
  rewrite ?node_38229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38231 (s : N.State) (i : N.Inputs) :
  R.v38231 (state s) (inputs i) = Zmod.unsigned (N.v38231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38231 s i)) at 1.
  unfold R.v38231, N.v38231.
  unfold R.v16463, N.v16463.
  rewrite ?node_38230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38232 (s : N.State) (i : N.Inputs) :
  R.v38232 (state s) (inputs i) = Zmod.unsigned (N.v38232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38232 s i)) at 1.
  unfold R.v38232, N.v38232.
  rewrite ?node_5680.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38233 (s : N.State) (i : N.Inputs) :
  R.v38233 (state s) (inputs i) = Zmod.unsigned (N.v38233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38233 s i)) at 1.
  unfold R.v38233, N.v38233.
  unfold R.v6, N.v6.
  rewrite ?node_5742.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38234 (s : N.State) (i : N.Inputs) :
  R.v38234 (state s) (inputs i) = Zmod.unsigned (N.v38234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38234 s i)) at 1.
  unfold R.v38234, N.v38234.
  rewrite ?node_38232.
  rewrite ?node_38233.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38235 (s : N.State) (i : N.Inputs) :
  R.v38235 (state s) (inputs i) = Zmod.unsigned (N.v38235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38235 s i)) at 1.
  unfold R.v38235, N.v38235.
  rewrite ?node_38231.
  rewrite ?node_38234.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38236 (s : N.State) (i : N.Inputs) :
  R.v38236 (state s) (inputs i) = Zmod.unsigned (N.v38236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38236 s i)) at 1.
  unfold R.v38236, N.v38236.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38237 (s : N.State) (i : N.Inputs) :
  R.v38237 (state s) (inputs i) = Zmod.unsigned (N.v38237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38237 s i)) at 1.
  unfold R.v38237, N.v38237.
  rewrite ?node_5730.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38238 (s : N.State) (i : N.Inputs) :
  R.v38238 (state s) (inputs i) = Zmod.unsigned (N.v38238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38238 s i)) at 1.
  unfold R.v38238, N.v38238.
  rewrite ?node_5726.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38239 (s : N.State) (i : N.Inputs) :
  R.v38239 (state s) (inputs i) = Zmod.unsigned (N.v38239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38239 s i)) at 1.
  unfold R.v38239, N.v38239.
  rewrite ?node_5722.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38240 (s : N.State) (i : N.Inputs) :
  R.v38240 (state s) (inputs i) = Zmod.unsigned (N.v38240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38240 s i)) at 1.
  unfold R.v38240, N.v38240.
  unfold R.v6, N.v6.
  rewrite ?node_5714.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38241 (s : N.State) (i : N.Inputs) :
  R.v38241 (state s) (inputs i) = Zmod.unsigned (N.v38241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38241 s i)) at 1.
  unfold R.v38241, N.v38241.
  unfold R.v6, N.v6.
  rewrite ?node_5707.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38242 (s : N.State) (i : N.Inputs) :
  R.v38242 (state s) (inputs i) = Zmod.unsigned (N.v38242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38242 s i)) at 1.
  unfold R.v38242, N.v38242.
  rewrite ?node_38240.
  rewrite ?node_38241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38243 (s : N.State) (i : N.Inputs) :
  R.v38243 (state s) (inputs i) = Zmod.unsigned (N.v38243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38243 s i)) at 1.
  unfold R.v38243, N.v38243.
  unfold R.v16484, N.v16484.
  rewrite ?node_38242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38244 (s : N.State) (i : N.Inputs) :
  R.v38244 (state s) (inputs i) = Zmod.unsigned (N.v38244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38244 s i)) at 1.
  unfold R.v38244, N.v38244.
  rewrite ?node_38237.
  rewrite ?node_38238.
  rewrite ?node_38239.
  rewrite ?node_38243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38245 (s : N.State) (i : N.Inputs) :
  R.v38245 (state s) (inputs i) = Zmod.unsigned (N.v38245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38245 s i)) at 1.
  unfold R.v38245, N.v38245.
  unfold R.v6, N.v6.
  rewrite ?node_38244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38246 (s : N.State) (i : N.Inputs) :
  R.v38246 (state s) (inputs i) = Zmod.unsigned (N.v38246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38246 s i)) at 1.
  unfold R.v38246, N.v38246.
  rewrite ?node_5731.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38247 (s : N.State) (i : N.Inputs) :
  R.v38247 (state s) (inputs i) = Zmod.unsigned (N.v38247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38247 s i)) at 1.
  unfold R.v38247, N.v38247.
  unfold R.v6, N.v6.
  rewrite ?node_5783.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38248 (s : N.State) (i : N.Inputs) :
  R.v38248 (state s) (inputs i) = Zmod.unsigned (N.v38248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38248 s i)) at 1.
  unfold R.v38248, N.v38248.
  unfold R.v6, N.v6.
  rewrite ?node_5799.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38249 (s : N.State) (i : N.Inputs) :
  R.v38249 (state s) (inputs i) = Zmod.unsigned (N.v38249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38249 s i)) at 1.
  unfold R.v38249, N.v38249.
  rewrite ?node_38246.
  rewrite ?node_38247.
  rewrite ?node_38248.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38250 (s : N.State) (i : N.Inputs) :
  R.v38250 (state s) (inputs i) = Zmod.unsigned (N.v38250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38250 s i)) at 1.
  unfold R.v38250, N.v38250.
  rewrite ?node_38245.
  rewrite ?node_38249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38251 (s : N.State) (i : N.Inputs) :
  R.v38251 (state s) (inputs i) = Zmod.unsigned (N.v38251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38251 s i)) at 1.
  unfold R.v38251, N.v38251.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38252 (s : N.State) (i : N.Inputs) :
  R.v38252 (state s) (inputs i) = Zmod.unsigned (N.v38252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38252 s i)) at 1.
  unfold R.v38252, N.v38252.
  rewrite ?node_5722.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38253 (s : N.State) (i : N.Inputs) :
  R.v38253 (state s) (inputs i) = Zmod.unsigned (N.v38253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38253 s i)) at 1.
  unfold R.v38253, N.v38253.
  unfold R.v6, N.v6.
  rewrite ?node_5714.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38254 (s : N.State) (i : N.Inputs) :
  R.v38254 (state s) (inputs i) = Zmod.unsigned (N.v38254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38254 s i)) at 1.
  unfold R.v38254, N.v38254.
  unfold R.v6, N.v6.
  rewrite ?node_5707.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38255 (s : N.State) (i : N.Inputs) :
  R.v38255 (state s) (inputs i) = Zmod.unsigned (N.v38255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38255 s i)) at 1.
  unfold R.v38255, N.v38255.
  rewrite ?node_38253.
  rewrite ?node_38254.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38256 (s : N.State) (i : N.Inputs) :
  R.v38256 (state s) (inputs i) = Zmod.unsigned (N.v38256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38256 s i)) at 1.
  unfold R.v38256, N.v38256.
  unfold R.v16484, N.v16484.
  rewrite ?node_38255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38257 (s : N.State) (i : N.Inputs) :
  R.v38257 (state s) (inputs i) = Zmod.unsigned (N.v38257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38257 s i)) at 1.
  unfold R.v38257, N.v38257.
  rewrite ?node_38252.
  rewrite ?node_38256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38258 (s : N.State) (i : N.Inputs) :
  R.v38258 (state s) (inputs i) = Zmod.unsigned (N.v38258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38258 s i)) at 1.
  unfold R.v38258, N.v38258.
  unfold R.v6, N.v6.
  rewrite ?node_38257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38259 (s : N.State) (i : N.Inputs) :
  R.v38259 (state s) (inputs i) = Zmod.unsigned (N.v38259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38259 s i)) at 1.
  unfold R.v38259, N.v38259.
  rewrite ?node_5723.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38260 (s : N.State) (i : N.Inputs) :
  R.v38260 (state s) (inputs i) = Zmod.unsigned (N.v38260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38260 s i)) at 1.
  unfold R.v38260, N.v38260.
  unfold R.v6, N.v6.
  rewrite ?node_5783.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38261 (s : N.State) (i : N.Inputs) :
  R.v38261 (state s) (inputs i) = Zmod.unsigned (N.v38261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38261 s i)) at 1.
  unfold R.v38261, N.v38261.
  rewrite ?node_38259.
  rewrite ?node_38260.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38262 (s : N.State) (i : N.Inputs) :
  R.v38262 (state s) (inputs i) = Zmod.unsigned (N.v38262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38262 s i)) at 1.
  unfold R.v38262, N.v38262.
  rewrite ?node_38258.
  rewrite ?node_38261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38263 (s : N.State) (i : N.Inputs) :
  R.v38263 (state s) (inputs i) = Zmod.unsigned (N.v38263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38263 s i)) at 1.
  unfold R.v38263, N.v38263.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38264 (s : N.State) (i : N.Inputs) :
  R.v38264 (state s) (inputs i) = Zmod.unsigned (N.v38264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38264 s i)) at 1.
  unfold R.v38264, N.v38264.
  rewrite ?node_5730.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38265 (s : N.State) (i : N.Inputs) :
  R.v38265 (state s) (inputs i) = Zmod.unsigned (N.v38265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38265 s i)) at 1.
  unfold R.v38265, N.v38265.
  unfold R.v6, N.v6.
  rewrite ?node_5726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38266 (s : N.State) (i : N.Inputs) :
  R.v38266 (state s) (inputs i) = Zmod.unsigned (N.v38266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38266 s i)) at 1.
  unfold R.v38266, N.v38266.
  unfold R.v6, N.v6.
  rewrite ?node_5723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38267 (s : N.State) (i : N.Inputs) :
  R.v38267 (state s) (inputs i) = Zmod.unsigned (N.v38267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38267 s i)) at 1.
  unfold R.v38267, N.v38267.
  rewrite ?node_38265.
  rewrite ?node_38266.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38268 (s : N.State) (i : N.Inputs) :
  R.v38268 (state s) (inputs i) = Zmod.unsigned (N.v38268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38268 s i)) at 1.
  unfold R.v38268, N.v38268.
  unfold R.v16484, N.v16484.
  rewrite ?node_38267.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38269 (s : N.State) (i : N.Inputs) :
  R.v38269 (state s) (inputs i) = Zmod.unsigned (N.v38269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38269 s i)) at 1.
  unfold R.v38269, N.v38269.
  rewrite ?node_38264.
  rewrite ?node_38268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38270 (s : N.State) (i : N.Inputs) :
  R.v38270 (state s) (inputs i) = Zmod.unsigned (N.v38270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38270 s i)) at 1.
  unfold R.v38270, N.v38270.
  unfold R.v6, N.v6.
  rewrite ?node_38269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38271 (s : N.State) (i : N.Inputs) :
  R.v38271 (state s) (inputs i) = Zmod.unsigned (N.v38271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38271 s i)) at 1.
  unfold R.v38271, N.v38271.
  rewrite ?node_5731.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38272 (s : N.State) (i : N.Inputs) :
  R.v38272 (state s) (inputs i) = Zmod.unsigned (N.v38272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38272 s i)) at 1.
  unfold R.v38272, N.v38272.
  unfold R.v6, N.v6.
  rewrite ?node_5799.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38273 (s : N.State) (i : N.Inputs) :
  R.v38273 (state s) (inputs i) = Zmod.unsigned (N.v38273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38273 s i)) at 1.
  unfold R.v38273, N.v38273.
  rewrite ?node_38271.
  rewrite ?node_38272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38274 (s : N.State) (i : N.Inputs) :
  R.v38274 (state s) (inputs i) = Zmod.unsigned (N.v38274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38274 s i)) at 1.
  unfold R.v38274, N.v38274.
  rewrite ?node_38270.
  rewrite ?node_38273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38275 (s : N.State) (i : N.Inputs) :
  R.v38275 (state s) (inputs i) = Zmod.unsigned (N.v38275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38275 s i)) at 1.
  unfold R.v38275, N.v38275.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38276 (s : N.State) (i : N.Inputs) :
  R.v38276 (state s) (inputs i) = Zmod.unsigned (N.v38276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38276 s i)) at 1.
  unfold R.v38276, N.v38276.
  unfold R.v6, N.v6.
  rewrite ?node_5735.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38277 (s : N.State) (i : N.Inputs) :
  R.v38277 (state s) (inputs i) = Zmod.unsigned (N.v38277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38277 s i)) at 1.
  unfold R.v38277, N.v38277.
  unfold R.v6, N.v6.
  rewrite ?node_5734.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38278 (s : N.State) (i : N.Inputs) :
  R.v38278 (state s) (inputs i) = Zmod.unsigned (N.v38278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38278 s i)) at 1.
  unfold R.v38278, N.v38278.
  rewrite ?node_38276.
  rewrite ?node_38277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38279 (s : N.State) (i : N.Inputs) :
  R.v38279 (state s) (inputs i) = Zmod.unsigned (N.v38279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38279 s i)) at 1.
  unfold R.v38279, N.v38279.
  unfold R.v16463, N.v16463.
  rewrite ?node_38278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38280 (s : N.State) (i : N.Inputs) :
  R.v38280 (state s) (inputs i) = Zmod.unsigned (N.v38280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38280 s i)) at 1.
  unfold R.v38280, N.v38280.
  rewrite ?node_5736.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38281 (s : N.State) (i : N.Inputs) :
  R.v38281 (state s) (inputs i) = Zmod.unsigned (N.v38281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38281 s i)) at 1.
  unfold R.v38281, N.v38281.
  unfold R.v6, N.v6.
  rewrite ?node_5801.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38282 (s : N.State) (i : N.Inputs) :
  R.v38282 (state s) (inputs i) = Zmod.unsigned (N.v38282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38282 s i)) at 1.
  unfold R.v38282, N.v38282.
  rewrite ?node_38280.
  rewrite ?node_38281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38283 (s : N.State) (i : N.Inputs) :
  R.v38283 (state s) (inputs i) = Zmod.unsigned (N.v38283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38283 s i)) at 1.
  unfold R.v38283, N.v38283.
  rewrite ?node_38279.
  rewrite ?node_38282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38284 (s : N.State) (i : N.Inputs) :
  R.v38284 (state s) (inputs i) = Zmod.unsigned (N.v38284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38284 s i)) at 1.
  unfold R.v38284, N.v38284.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38285 (s : N.State) (i : N.Inputs) :
  R.v38285 (state s) (inputs i) = Zmod.unsigned (N.v38285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38285 s i)) at 1.
  unfold R.v38285, N.v38285.
  rewrite ?node_5783.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38286 (s : N.State) (i : N.Inputs) :
  R.v38286 (state s) (inputs i) = Zmod.unsigned (N.v38286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38286 s i)) at 1.
  unfold R.v38286, N.v38286.
  unfold R.v16463, N.v16463.
  rewrite !state_r166_nr_5F166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r166_nr_5F166 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38287 (s : N.State) (i : N.Inputs) :
  R.v38287 (state s) (inputs i) = Zmod.unsigned (N.v38287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38287 s i)) at 1.
  unfold R.v38287, N.v38287.
  rewrite ?node_5778.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38288 (s : N.State) (i : N.Inputs) :
  R.v38288 (state s) (inputs i) = Zmod.unsigned (N.v38288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38288 s i)) at 1.
  unfold R.v38288, N.v38288.
  unfold R.v6, N.v6.
  rewrite ?node_5770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38289 (s : N.State) (i : N.Inputs) :
  R.v38289 (state s) (inputs i) = Zmod.unsigned (N.v38289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38289 s i)) at 1.
  unfold R.v38289, N.v38289.
  unfold R.v6, N.v6.
  rewrite ?node_5763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38290 (s : N.State) (i : N.Inputs) :
  R.v38290 (state s) (inputs i) = Zmod.unsigned (N.v38290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38290 s i)) at 1.
  unfold R.v38290, N.v38290.
  rewrite ?node_38288.
  rewrite ?node_38289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38291 (s : N.State) (i : N.Inputs) :
  R.v38291 (state s) (inputs i) = Zmod.unsigned (N.v38291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38291 s i)) at 1.
  unfold R.v38291, N.v38291.
  unfold R.v16484, N.v16484.
  rewrite ?node_38290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38292 (s : N.State) (i : N.Inputs) :
  R.v38292 (state s) (inputs i) = Zmod.unsigned (N.v38292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38292 s i)) at 1.
  unfold R.v38292, N.v38292.
  rewrite ?node_38285.
  rewrite ?node_38286.
  rewrite ?node_38287.
  rewrite ?node_38291.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38293 (s : N.State) (i : N.Inputs) :
  R.v38293 (state s) (inputs i) = Zmod.unsigned (N.v38293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38293 s i)) at 1.
  unfold R.v38293, N.v38293.
  unfold R.v6, N.v6.
  rewrite ?node_38292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38294 (s : N.State) (i : N.Inputs) :
  R.v38294 (state s) (inputs i) = Zmod.unsigned (N.v38294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38294 s i)) at 1.
  unfold R.v38294, N.v38294.
  rewrite ?node_5784.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38295 (s : N.State) (i : N.Inputs) :
  R.v38295 (state s) (inputs i) = Zmod.unsigned (N.v38295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38295 s i)) at 1.
  unfold R.v38295, N.v38295.
  unfold R.v6, N.v6.
  rewrite ?node_5842.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38296 (s : N.State) (i : N.Inputs) :
  R.v38296 (state s) (inputs i) = Zmod.unsigned (N.v38296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38296 s i)) at 1.
  unfold R.v38296, N.v38296.
  unfold R.v6, N.v6.
  rewrite ?node_5858.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38297 (s : N.State) (i : N.Inputs) :
  R.v38297 (state s) (inputs i) = Zmod.unsigned (N.v38297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38297 s i)) at 1.
  unfold R.v38297, N.v38297.
  rewrite ?node_38294.
  rewrite ?node_38295.
  rewrite ?node_38296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38298 (s : N.State) (i : N.Inputs) :
  R.v38298 (state s) (inputs i) = Zmod.unsigned (N.v38298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38298 s i)) at 1.
  unfold R.v38298, N.v38298.
  rewrite ?node_38293.
  rewrite ?node_38297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38299 (s : N.State) (i : N.Inputs) :
  R.v38299 (state s) (inputs i) = Zmod.unsigned (N.v38299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38299 s i)) at 1.
  unfold R.v38299, N.v38299.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38300 (s : N.State) (i : N.Inputs) :
  R.v38300 (state s) (inputs i) = Zmod.unsigned (N.v38300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38300 s i)) at 1.
  unfold R.v38300, N.v38300.
  rewrite ?node_5778.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38301 (s : N.State) (i : N.Inputs) :
  R.v38301 (state s) (inputs i) = Zmod.unsigned (N.v38301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38301 s i)) at 1.
  unfold R.v38301, N.v38301.
  unfold R.v6, N.v6.
  rewrite ?node_5770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38302 (s : N.State) (i : N.Inputs) :
  R.v38302 (state s) (inputs i) = Zmod.unsigned (N.v38302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38302 s i)) at 1.
  unfold R.v38302, N.v38302.
  unfold R.v6, N.v6.
  rewrite ?node_5763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38303 (s : N.State) (i : N.Inputs) :
  R.v38303 (state s) (inputs i) = Zmod.unsigned (N.v38303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38303 s i)) at 1.
  unfold R.v38303, N.v38303.
  rewrite ?node_38301.
  rewrite ?node_38302.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38304 (s : N.State) (i : N.Inputs) :
  R.v38304 (state s) (inputs i) = Zmod.unsigned (N.v38304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38304 s i)) at 1.
  unfold R.v38304, N.v38304.
  unfold R.v16484, N.v16484.
  rewrite ?node_38303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38305 (s : N.State) (i : N.Inputs) :
  R.v38305 (state s) (inputs i) = Zmod.unsigned (N.v38305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38305 s i)) at 1.
  unfold R.v38305, N.v38305.
  rewrite ?node_38300.
  rewrite ?node_38304.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38306 (s : N.State) (i : N.Inputs) :
  R.v38306 (state s) (inputs i) = Zmod.unsigned (N.v38306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38306 s i)) at 1.
  unfold R.v38306, N.v38306.
  unfold R.v6, N.v6.
  rewrite ?node_38305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38307 (s : N.State) (i : N.Inputs) :
  R.v38307 (state s) (inputs i) = Zmod.unsigned (N.v38307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38307 s i)) at 1.
  unfold R.v38307, N.v38307.
  rewrite ?node_5779.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38308 (s : N.State) (i : N.Inputs) :
  R.v38308 (state s) (inputs i) = Zmod.unsigned (N.v38308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38308 s i)) at 1.
  unfold R.v38308, N.v38308.
  unfold R.v6, N.v6.
  rewrite ?node_5842.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38309 (s : N.State) (i : N.Inputs) :
  R.v38309 (state s) (inputs i) = Zmod.unsigned (N.v38309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38309 s i)) at 1.
  unfold R.v38309, N.v38309.
  rewrite ?node_38307.
  rewrite ?node_38308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38310 (s : N.State) (i : N.Inputs) :
  R.v38310 (state s) (inputs i) = Zmod.unsigned (N.v38310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38310 s i)) at 1.
  unfold R.v38310, N.v38310.
  rewrite ?node_38306.
  rewrite ?node_38309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38311 (s : N.State) (i : N.Inputs) :
  R.v38311 (state s) (inputs i) = Zmod.unsigned (N.v38311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38311 s i)) at 1.
  unfold R.v38311, N.v38311.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38312 (s : N.State) (i : N.Inputs) :
  R.v38312 (state s) (inputs i) = Zmod.unsigned (N.v38312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38312 s i)) at 1.
  unfold R.v38312, N.v38312.
  rewrite ?node_5783.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38313 (s : N.State) (i : N.Inputs) :
  R.v38313 (state s) (inputs i) = Zmod.unsigned (N.v38313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38313 s i)) at 1.
  unfold R.v38313, N.v38313.
  unfold R.v6, N.v6.
  rewrite !state_r166_nr_5F166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r166_nr_5F166 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38314 (s : N.State) (i : N.Inputs) :
  R.v38314 (state s) (inputs i) = Zmod.unsigned (N.v38314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38314 s i)) at 1.
  unfold R.v38314, N.v38314.
  unfold R.v6, N.v6.
  rewrite ?node_5779.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38315 (s : N.State) (i : N.Inputs) :
  R.v38315 (state s) (inputs i) = Zmod.unsigned (N.v38315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38315 s i)) at 1.
  unfold R.v38315, N.v38315.
  rewrite ?node_38313.
  rewrite ?node_38314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38316 (s : N.State) (i : N.Inputs) :
  R.v38316 (state s) (inputs i) = Zmod.unsigned (N.v38316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38316 s i)) at 1.
  unfold R.v38316, N.v38316.
  unfold R.v16484, N.v16484.
  rewrite ?node_38315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38317 (s : N.State) (i : N.Inputs) :
  R.v38317 (state s) (inputs i) = Zmod.unsigned (N.v38317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38317 s i)) at 1.
  unfold R.v38317, N.v38317.
  rewrite ?node_38312.
  rewrite ?node_38316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38318 (s : N.State) (i : N.Inputs) :
  R.v38318 (state s) (inputs i) = Zmod.unsigned (N.v38318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38318 s i)) at 1.
  unfold R.v38318, N.v38318.
  unfold R.v6, N.v6.
  rewrite ?node_38317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38319 (s : N.State) (i : N.Inputs) :
  R.v38319 (state s) (inputs i) = Zmod.unsigned (N.v38319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38319 s i)) at 1.
  unfold R.v38319, N.v38319.
  rewrite ?node_5784.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38320 (s : N.State) (i : N.Inputs) :
  R.v38320 (state s) (inputs i) = Zmod.unsigned (N.v38320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38320 s i)) at 1.
  unfold R.v38320, N.v38320.
  unfold R.v6, N.v6.
  rewrite ?node_5858.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38321 (s : N.State) (i : N.Inputs) :
  R.v38321 (state s) (inputs i) = Zmod.unsigned (N.v38321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38321 s i)) at 1.
  unfold R.v38321, N.v38321.
  rewrite ?node_38319.
  rewrite ?node_38320.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38322 (s : N.State) (i : N.Inputs) :
  R.v38322 (state s) (inputs i) = Zmod.unsigned (N.v38322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38322 s i)) at 1.
  unfold R.v38322, N.v38322.
  rewrite ?node_38318.
  rewrite ?node_38321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38323 (s : N.State) (i : N.Inputs) :
  R.v38323 (state s) (inputs i) = Zmod.unsigned (N.v38323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38323 s i)) at 1.
  unfold R.v38323, N.v38323.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38324 (s : N.State) (i : N.Inputs) :
  R.v38324 (state s) (inputs i) = Zmod.unsigned (N.v38324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38324 s i)) at 1.
  unfold R.v38324, N.v38324.
  rewrite ?node_5794.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38325 (s : N.State) (i : N.Inputs) :
  R.v38325 (state s) (inputs i) = Zmod.unsigned (N.v38325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38325 s i)) at 1.
  unfold R.v38325, N.v38325.
  unfold R.v6, N.v6.
  rewrite ?node_5790.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38326 (s : N.State) (i : N.Inputs) :
  R.v38326 (state s) (inputs i) = Zmod.unsigned (N.v38326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38326 s i)) at 1.
  unfold R.v38326, N.v38326.
  unfold R.v6, N.v6.
  rewrite ?node_5787.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38327 (s : N.State) (i : N.Inputs) :
  R.v38327 (state s) (inputs i) = Zmod.unsigned (N.v38327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38327 s i)) at 1.
  unfold R.v38327, N.v38327.
  rewrite ?node_38325.
  rewrite ?node_38326.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38328 (s : N.State) (i : N.Inputs) :
  R.v38328 (state s) (inputs i) = Zmod.unsigned (N.v38328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38328 s i)) at 1.
  unfold R.v38328, N.v38328.
  unfold R.v16484, N.v16484.
  rewrite ?node_38327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38329 (s : N.State) (i : N.Inputs) :
  R.v38329 (state s) (inputs i) = Zmod.unsigned (N.v38329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38329 s i)) at 1.
  unfold R.v38329, N.v38329.
  rewrite ?node_38324.
  rewrite ?node_38328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38330 (s : N.State) (i : N.Inputs) :
  R.v38330 (state s) (inputs i) = Zmod.unsigned (N.v38330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38330 s i)) at 1.
  unfold R.v38330, N.v38330.
  unfold R.v6, N.v6.
  rewrite ?node_38329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38331 (s : N.State) (i : N.Inputs) :
  R.v38331 (state s) (inputs i) = Zmod.unsigned (N.v38331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38331 s i)) at 1.
  unfold R.v38331, N.v38331.
  rewrite ?node_5795.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38332 (s : N.State) (i : N.Inputs) :
  R.v38332 (state s) (inputs i) = Zmod.unsigned (N.v38332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38332 s i)) at 1.
  unfold R.v38332, N.v38332.
  unfold R.v6, N.v6.
  rewrite ?node_5862.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38333 (s : N.State) (i : N.Inputs) :
  R.v38333 (state s) (inputs i) = Zmod.unsigned (N.v38333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38333 s i)) at 1.
  unfold R.v38333, N.v38333.
  rewrite ?node_38331.
  rewrite ?node_38332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38334 (s : N.State) (i : N.Inputs) :
  R.v38334 (state s) (inputs i) = Zmod.unsigned (N.v38334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38334 s i)) at 1.
  unfold R.v38334, N.v38334.
  rewrite ?node_38330.
  rewrite ?node_38333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38335 (s : N.State) (i : N.Inputs) :
  R.v38335 (state s) (inputs i) = Zmod.unsigned (N.v38335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38335 s i)) at 1.
  unfold R.v38335, N.v38335.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38336 (s : N.State) (i : N.Inputs) :
  R.v38336 (state s) (inputs i) = Zmod.unsigned (N.v38336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38336 s i)) at 1.
  unfold R.v38336, N.v38336.
  rewrite ?node_5842.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38337 (s : N.State) (i : N.Inputs) :
  R.v38337 (state s) (inputs i) = Zmod.unsigned (N.v38337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38337 s i)) at 1.
  unfold R.v38337, N.v38337.
  unfold R.v16463, N.v16463.
  rewrite !state_r179_nr_5F179.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r179_nr_5F179 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38338 (s : N.State) (i : N.Inputs) :
  R.v38338 (state s) (inputs i) = Zmod.unsigned (N.v38338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38338 s i)) at 1.
  unfold R.v38338, N.v38338.
  rewrite ?node_5837.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38339 (s : N.State) (i : N.Inputs) :
  R.v38339 (state s) (inputs i) = Zmod.unsigned (N.v38339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38339 s i)) at 1.
  unfold R.v38339, N.v38339.
  unfold R.v6, N.v6.
  rewrite ?node_5829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38340 (s : N.State) (i : N.Inputs) :
  R.v38340 (state s) (inputs i) = Zmod.unsigned (N.v38340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38340 s i)) at 1.
  unfold R.v38340, N.v38340.
  unfold R.v6, N.v6.
  rewrite ?node_5822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38341 (s : N.State) (i : N.Inputs) :
  R.v38341 (state s) (inputs i) = Zmod.unsigned (N.v38341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38341 s i)) at 1.
  unfold R.v38341, N.v38341.
  rewrite ?node_38339.
  rewrite ?node_38340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38342 (s : N.State) (i : N.Inputs) :
  R.v38342 (state s) (inputs i) = Zmod.unsigned (N.v38342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38342 s i)) at 1.
  unfold R.v38342, N.v38342.
  unfold R.v16484, N.v16484.
  rewrite ?node_38341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38343 (s : N.State) (i : N.Inputs) :
  R.v38343 (state s) (inputs i) = Zmod.unsigned (N.v38343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38343 s i)) at 1.
  unfold R.v38343, N.v38343.
  rewrite ?node_38336.
  rewrite ?node_38337.
  rewrite ?node_38338.
  rewrite ?node_38342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38344 (s : N.State) (i : N.Inputs) :
  R.v38344 (state s) (inputs i) = Zmod.unsigned (N.v38344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38344 s i)) at 1.
  unfold R.v38344, N.v38344.
  unfold R.v6, N.v6.
  rewrite ?node_38343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38345 (s : N.State) (i : N.Inputs) :
  R.v38345 (state s) (inputs i) = Zmod.unsigned (N.v38345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38345 s i)) at 1.
  unfold R.v38345, N.v38345.
  rewrite ?node_5843.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38346 (s : N.State) (i : N.Inputs) :
  R.v38346 (state s) (inputs i) = Zmod.unsigned (N.v38346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38346 s i)) at 1.
  unfold R.v38346, N.v38346.
  unfold R.v6, N.v6.
  rewrite ?node_5904.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38347 (s : N.State) (i : N.Inputs) :
  R.v38347 (state s) (inputs i) = Zmod.unsigned (N.v38347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38347 s i)) at 1.
  unfold R.v38347, N.v38347.
  unfold R.v6, N.v6.
  rewrite ?node_5920.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38348 (s : N.State) (i : N.Inputs) :
  R.v38348 (state s) (inputs i) = Zmod.unsigned (N.v38348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38348 s i)) at 1.
  unfold R.v38348, N.v38348.
  rewrite ?node_38345.
  rewrite ?node_38346.
  rewrite ?node_38347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38349 (s : N.State) (i : N.Inputs) :
  R.v38349 (state s) (inputs i) = Zmod.unsigned (N.v38349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38349 s i)) at 1.
  unfold R.v38349, N.v38349.
  rewrite ?node_38344.
  rewrite ?node_38348.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38350 (s : N.State) (i : N.Inputs) :
  R.v38350 (state s) (inputs i) = Zmod.unsigned (N.v38350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38350 s i)) at 1.
  unfold R.v38350, N.v38350.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38351 (s : N.State) (i : N.Inputs) :
  R.v38351 (state s) (inputs i) = Zmod.unsigned (N.v38351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38351 s i)) at 1.
  unfold R.v38351, N.v38351.
  rewrite ?node_5837.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38352 (s : N.State) (i : N.Inputs) :
  R.v38352 (state s) (inputs i) = Zmod.unsigned (N.v38352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38352 s i)) at 1.
  unfold R.v38352, N.v38352.
  unfold R.v6, N.v6.
  rewrite ?node_5829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38353 (s : N.State) (i : N.Inputs) :
  R.v38353 (state s) (inputs i) = Zmod.unsigned (N.v38353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38353 s i)) at 1.
  unfold R.v38353, N.v38353.
  unfold R.v6, N.v6.
  rewrite ?node_5822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38354 (s : N.State) (i : N.Inputs) :
  R.v38354 (state s) (inputs i) = Zmod.unsigned (N.v38354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38354 s i)) at 1.
  unfold R.v38354, N.v38354.
  rewrite ?node_38352.
  rewrite ?node_38353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38355 (s : N.State) (i : N.Inputs) :
  R.v38355 (state s) (inputs i) = Zmod.unsigned (N.v38355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38355 s i)) at 1.
  unfold R.v38355, N.v38355.
  unfold R.v16484, N.v16484.
  rewrite ?node_38354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38356 (s : N.State) (i : N.Inputs) :
  R.v38356 (state s) (inputs i) = Zmod.unsigned (N.v38356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38356 s i)) at 1.
  unfold R.v38356, N.v38356.
  rewrite ?node_38351.
  rewrite ?node_38355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38357 (s : N.State) (i : N.Inputs) :
  R.v38357 (state s) (inputs i) = Zmod.unsigned (N.v38357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38357 s i)) at 1.
  unfold R.v38357, N.v38357.
  unfold R.v6, N.v6.
  rewrite ?node_38356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38358 (s : N.State) (i : N.Inputs) :
  R.v38358 (state s) (inputs i) = Zmod.unsigned (N.v38358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38358 s i)) at 1.
  unfold R.v38358, N.v38358.
  rewrite ?node_5838.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38359 (s : N.State) (i : N.Inputs) :
  R.v38359 (state s) (inputs i) = Zmod.unsigned (N.v38359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38359 s i)) at 1.
  unfold R.v38359, N.v38359.
  unfold R.v6, N.v6.
  rewrite ?node_5904.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38360 (s : N.State) (i : N.Inputs) :
  R.v38360 (state s) (inputs i) = Zmod.unsigned (N.v38360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38360 s i)) at 1.
  unfold R.v38360, N.v38360.
  rewrite ?node_38358.
  rewrite ?node_38359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38361 (s : N.State) (i : N.Inputs) :
  R.v38361 (state s) (inputs i) = Zmod.unsigned (N.v38361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38361 s i)) at 1.
  unfold R.v38361, N.v38361.
  rewrite ?node_38357.
  rewrite ?node_38360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38362 (s : N.State) (i : N.Inputs) :
  R.v38362 (state s) (inputs i) = Zmod.unsigned (N.v38362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38362 s i)) at 1.
  unfold R.v38362, N.v38362.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38363 (s : N.State) (i : N.Inputs) :
  R.v38363 (state s) (inputs i) = Zmod.unsigned (N.v38363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38363 s i)) at 1.
  unfold R.v38363, N.v38363.
  rewrite ?node_5842.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38364 (s : N.State) (i : N.Inputs) :
  R.v38364 (state s) (inputs i) = Zmod.unsigned (N.v38364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38364 s i)) at 1.
  unfold R.v38364, N.v38364.
  unfold R.v6, N.v6.
  rewrite !state_r179_nr_5F179.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r179_nr_5F179 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38365 (s : N.State) (i : N.Inputs) :
  R.v38365 (state s) (inputs i) = Zmod.unsigned (N.v38365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38365 s i)) at 1.
  unfold R.v38365, N.v38365.
  unfold R.v6, N.v6.
  rewrite ?node_5838.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38366 (s : N.State) (i : N.Inputs) :
  R.v38366 (state s) (inputs i) = Zmod.unsigned (N.v38366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38366 s i)) at 1.
  unfold R.v38366, N.v38366.
  rewrite ?node_38364.
  rewrite ?node_38365.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38367 (s : N.State) (i : N.Inputs) :
  R.v38367 (state s) (inputs i) = Zmod.unsigned (N.v38367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38367 s i)) at 1.
  unfold R.v38367, N.v38367.
  unfold R.v16484, N.v16484.
  rewrite ?node_38366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38368 (s : N.State) (i : N.Inputs) :
  R.v38368 (state s) (inputs i) = Zmod.unsigned (N.v38368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38368 s i)) at 1.
  unfold R.v38368, N.v38368.
  rewrite ?node_38363.
  rewrite ?node_38367.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38369 (s : N.State) (i : N.Inputs) :
  R.v38369 (state s) (inputs i) = Zmod.unsigned (N.v38369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38369 s i)) at 1.
  unfold R.v38369, N.v38369.
  unfold R.v6, N.v6.
  rewrite ?node_38368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38370 (s : N.State) (i : N.Inputs) :
  R.v38370 (state s) (inputs i) = Zmod.unsigned (N.v38370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38370 s i)) at 1.
  unfold R.v38370, N.v38370.
  rewrite ?node_5843.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38371 (s : N.State) (i : N.Inputs) :
  R.v38371 (state s) (inputs i) = Zmod.unsigned (N.v38371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38371 s i)) at 1.
  unfold R.v38371, N.v38371.
  unfold R.v6, N.v6.
  rewrite ?node_5920.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38372 (s : N.State) (i : N.Inputs) :
  R.v38372 (state s) (inputs i) = Zmod.unsigned (N.v38372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38372 s i)) at 1.
  unfold R.v38372, N.v38372.
  rewrite ?node_38370.
  rewrite ?node_38371.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38373 (s : N.State) (i : N.Inputs) :
  R.v38373 (state s) (inputs i) = Zmod.unsigned (N.v38373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38373 s i)) at 1.
  unfold R.v38373, N.v38373.
  rewrite ?node_38369.
  rewrite ?node_38372.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38374 (s : N.State) (i : N.Inputs) :
  R.v38374 (state s) (inputs i) = Zmod.unsigned (N.v38374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38374 s i)) at 1.
  unfold R.v38374, N.v38374.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38375 (s : N.State) (i : N.Inputs) :
  R.v38375 (state s) (inputs i) = Zmod.unsigned (N.v38375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38375 s i)) at 1.
  unfold R.v38375, N.v38375.
  rewrite ?node_5853.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38376 (s : N.State) (i : N.Inputs) :
  R.v38376 (state s) (inputs i) = Zmod.unsigned (N.v38376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38376 s i)) at 1.
  unfold R.v38376, N.v38376.
  unfold R.v6, N.v6.
  rewrite ?node_5849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38377 (s : N.State) (i : N.Inputs) :
  R.v38377 (state s) (inputs i) = Zmod.unsigned (N.v38377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38377 s i)) at 1.
  unfold R.v38377, N.v38377.
  unfold R.v6, N.v6.
  rewrite ?node_5846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38378 (s : N.State) (i : N.Inputs) :
  R.v38378 (state s) (inputs i) = Zmod.unsigned (N.v38378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38378 s i)) at 1.
  unfold R.v38378, N.v38378.
  rewrite ?node_38376.
  rewrite ?node_38377.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38379 (s : N.State) (i : N.Inputs) :
  R.v38379 (state s) (inputs i) = Zmod.unsigned (N.v38379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38379 s i)) at 1.
  unfold R.v38379, N.v38379.
  unfold R.v16484, N.v16484.
  rewrite ?node_38378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38380 (s : N.State) (i : N.Inputs) :
  R.v38380 (state s) (inputs i) = Zmod.unsigned (N.v38380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38380 s i)) at 1.
  unfold R.v38380, N.v38380.
  rewrite ?node_38375.
  rewrite ?node_38379.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38381 (s : N.State) (i : N.Inputs) :
  R.v38381 (state s) (inputs i) = Zmod.unsigned (N.v38381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38381 s i)) at 1.
  unfold R.v38381, N.v38381.
  unfold R.v6, N.v6.
  rewrite ?node_38380.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38382 (s : N.State) (i : N.Inputs) :
  R.v38382 (state s) (inputs i) = Zmod.unsigned (N.v38382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38382 s i)) at 1.
  unfold R.v38382, N.v38382.
  rewrite ?node_5854.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38383 (s : N.State) (i : N.Inputs) :
  R.v38383 (state s) (inputs i) = Zmod.unsigned (N.v38383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38383 s i)) at 1.
  unfold R.v38383, N.v38383.
  unfold R.v6, N.v6.
  rewrite ?node_5924.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38384 (s : N.State) (i : N.Inputs) :
  R.v38384 (state s) (inputs i) = Zmod.unsigned (N.v38384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38384 s i)) at 1.
  unfold R.v38384, N.v38384.
  rewrite ?node_38382.
  rewrite ?node_38383.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38385 (s : N.State) (i : N.Inputs) :
  R.v38385 (state s) (inputs i) = Zmod.unsigned (N.v38385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38385 s i)) at 1.
  unfold R.v38385, N.v38385.
  rewrite ?node_38381.
  rewrite ?node_38384.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38386 (s : N.State) (i : N.Inputs) :
  R.v38386 (state s) (inputs i) = Zmod.unsigned (N.v38386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38386 s i)) at 1.
  unfold R.v38386, N.v38386.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38387 (s : N.State) (i : N.Inputs) :
  R.v38387 (state s) (inputs i) = Zmod.unsigned (N.v38387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38387 s i)) at 1.
  unfold R.v38387, N.v38387.
  rewrite ?node_5904.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38388 (s : N.State) (i : N.Inputs) :
  R.v38388 (state s) (inputs i) = Zmod.unsigned (N.v38388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38388 s i)) at 1.
  unfold R.v38388, N.v38388.
  rewrite ?node_5900.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38389 (s : N.State) (i : N.Inputs) :
  R.v38389 (state s) (inputs i) = Zmod.unsigned (N.v38389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38389 s i)) at 1.
  unfold R.v38389, N.v38389.
  rewrite ?node_5898.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38390 (s : N.State) (i : N.Inputs) :
  R.v38390 (state s) (inputs i) = Zmod.unsigned (N.v38390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38390 s i)) at 1.
  unfold R.v38390, N.v38390.
  unfold R.v6, N.v6.
  rewrite ?node_5890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38391 (s : N.State) (i : N.Inputs) :
  R.v38391 (state s) (inputs i) = Zmod.unsigned (N.v38391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38391 s i)) at 1.
  unfold R.v38391, N.v38391.
  unfold R.v6, N.v6.
  rewrite ?node_5883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38392 (s : N.State) (i : N.Inputs) :
  R.v38392 (state s) (inputs i) = Zmod.unsigned (N.v38392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38392 s i)) at 1.
  unfold R.v38392, N.v38392.
  rewrite ?node_38390.
  rewrite ?node_38391.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38393 (s : N.State) (i : N.Inputs) :
  R.v38393 (state s) (inputs i) = Zmod.unsigned (N.v38393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38393 s i)) at 1.
  unfold R.v38393, N.v38393.
  unfold R.v16484, N.v16484.
  rewrite ?node_38392.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38394 (s : N.State) (i : N.Inputs) :
  R.v38394 (state s) (inputs i) = Zmod.unsigned (N.v38394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38394 s i)) at 1.
  unfold R.v38394, N.v38394.
  rewrite ?node_38387.
  rewrite ?node_38388.
  rewrite ?node_38389.
  rewrite ?node_38393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38395 (s : N.State) (i : N.Inputs) :
  R.v38395 (state s) (inputs i) = Zmod.unsigned (N.v38395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38395 s i)) at 1.
  unfold R.v38395, N.v38395.
  unfold R.v6, N.v6.
  rewrite ?node_38394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38396 (s : N.State) (i : N.Inputs) :
  R.v38396 (state s) (inputs i) = Zmod.unsigned (N.v38396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38396 s i)) at 1.
  unfold R.v38396, N.v38396.
  rewrite ?node_5905.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38397 (s : N.State) (i : N.Inputs) :
  R.v38397 (state s) (inputs i) = Zmod.unsigned (N.v38397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38397 s i)) at 1.
  unfold R.v38397, N.v38397.
  unfold R.v6, N.v6.
  rewrite ?node_5966.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38398 (s : N.State) (i : N.Inputs) :
  R.v38398 (state s) (inputs i) = Zmod.unsigned (N.v38398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38398 s i)) at 1.
  unfold R.v38398, N.v38398.
  unfold R.v6, N.v6.
  rewrite ?node_5984.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38399 (s : N.State) (i : N.Inputs) :
  R.v38399 (state s) (inputs i) = Zmod.unsigned (N.v38399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38399 s i)) at 1.
  unfold R.v38399, N.v38399.
  rewrite ?node_38396.
  rewrite ?node_38397.
  rewrite ?node_38398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38400 (s : N.State) (i : N.Inputs) :
  R.v38400 (state s) (inputs i) = Zmod.unsigned (N.v38400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38400 s i)) at 1.
  unfold R.v38400, N.v38400.
  rewrite ?node_38395.
  rewrite ?node_38399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38401 (s : N.State) (i : N.Inputs) :
  R.v38401 (state s) (inputs i) = Zmod.unsigned (N.v38401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38401 s i)) at 1.
  unfold R.v38401, N.v38401.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38402 (s : N.State) (i : N.Inputs) :
  R.v38402 (state s) (inputs i) = Zmod.unsigned (N.v38402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38402 s i)) at 1.
  unfold R.v38402, N.v38402.
  rewrite ?node_5898.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38403 (s : N.State) (i : N.Inputs) :
  R.v38403 (state s) (inputs i) = Zmod.unsigned (N.v38403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38403 s i)) at 1.
  unfold R.v38403, N.v38403.
  unfold R.v6, N.v6.
  rewrite ?node_5890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38404 (s : N.State) (i : N.Inputs) :
  R.v38404 (state s) (inputs i) = Zmod.unsigned (N.v38404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38404 s i)) at 1.
  unfold R.v38404, N.v38404.
  unfold R.v6, N.v6.
  rewrite ?node_5883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38405 (s : N.State) (i : N.Inputs) :
  R.v38405 (state s) (inputs i) = Zmod.unsigned (N.v38405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38405 s i)) at 1.
  unfold R.v38405, N.v38405.
  rewrite ?node_38403.
  rewrite ?node_38404.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38406 (s : N.State) (i : N.Inputs) :
  R.v38406 (state s) (inputs i) = Zmod.unsigned (N.v38406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38406 s i)) at 1.
  unfold R.v38406, N.v38406.
  unfold R.v16484, N.v16484.
  rewrite ?node_38405.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38407 (s : N.State) (i : N.Inputs) :
  R.v38407 (state s) (inputs i) = Zmod.unsigned (N.v38407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38407 s i)) at 1.
  unfold R.v38407, N.v38407.
  rewrite ?node_38402.
  rewrite ?node_38406.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38408 (s : N.State) (i : N.Inputs) :
  R.v38408 (state s) (inputs i) = Zmod.unsigned (N.v38408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38408 s i)) at 1.
  unfold R.v38408, N.v38408.
  unfold R.v6, N.v6.
  rewrite ?node_38407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38409 (s : N.State) (i : N.Inputs) :
  R.v38409 (state s) (inputs i) = Zmod.unsigned (N.v38409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38409 s i)) at 1.
  unfold R.v38409, N.v38409.
  rewrite ?node_5899.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38410 (s : N.State) (i : N.Inputs) :
  R.v38410 (state s) (inputs i) = Zmod.unsigned (N.v38410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38410 s i)) at 1.
  unfold R.v38410, N.v38410.
  unfold R.v6, N.v6.
  rewrite ?node_5966.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38411 (s : N.State) (i : N.Inputs) :
  R.v38411 (state s) (inputs i) = Zmod.unsigned (N.v38411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38411 s i)) at 1.
  unfold R.v38411, N.v38411.
  rewrite ?node_38409.
  rewrite ?node_38410.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38412 (s : N.State) (i : N.Inputs) :
  R.v38412 (state s) (inputs i) = Zmod.unsigned (N.v38412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38412 s i)) at 1.
  unfold R.v38412, N.v38412.
  rewrite ?node_38408.
  rewrite ?node_38411.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38413 (s : N.State) (i : N.Inputs) :
  R.v38413 (state s) (inputs i) = Zmod.unsigned (N.v38413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38413 s i)) at 1.
  unfold R.v38413, N.v38413.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38414 (s : N.State) (i : N.Inputs) :
  R.v38414 (state s) (inputs i) = Zmod.unsigned (N.v38414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38414 s i)) at 1.
  unfold R.v38414, N.v38414.
  rewrite ?node_5904.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38415 (s : N.State) (i : N.Inputs) :
  R.v38415 (state s) (inputs i) = Zmod.unsigned (N.v38415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38415 s i)) at 1.
  unfold R.v38415, N.v38415.
  unfold R.v6, N.v6.
  rewrite ?node_5900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38416 (s : N.State) (i : N.Inputs) :
  R.v38416 (state s) (inputs i) = Zmod.unsigned (N.v38416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38416 s i)) at 1.
  unfold R.v38416, N.v38416.
  unfold R.v6, N.v6.
  rewrite ?node_5899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38417 (s : N.State) (i : N.Inputs) :
  R.v38417 (state s) (inputs i) = Zmod.unsigned (N.v38417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38417 s i)) at 1.
  unfold R.v38417, N.v38417.
  rewrite ?node_38415.
  rewrite ?node_38416.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38418 (s : N.State) (i : N.Inputs) :
  R.v38418 (state s) (inputs i) = Zmod.unsigned (N.v38418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38418 s i)) at 1.
  unfold R.v38418, N.v38418.
  unfold R.v16484, N.v16484.
  rewrite ?node_38417.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38419 (s : N.State) (i : N.Inputs) :
  R.v38419 (state s) (inputs i) = Zmod.unsigned (N.v38419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38419 s i)) at 1.
  unfold R.v38419, N.v38419.
  rewrite ?node_38414.
  rewrite ?node_38418.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38420 (s : N.State) (i : N.Inputs) :
  R.v38420 (state s) (inputs i) = Zmod.unsigned (N.v38420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38420 s i)) at 1.
  unfold R.v38420, N.v38420.
  unfold R.v6, N.v6.
  rewrite ?node_38419.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38421 (s : N.State) (i : N.Inputs) :
  R.v38421 (state s) (inputs i) = Zmod.unsigned (N.v38421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38421 s i)) at 1.
  unfold R.v38421, N.v38421.
  rewrite ?node_5905.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38422 (s : N.State) (i : N.Inputs) :
  R.v38422 (state s) (inputs i) = Zmod.unsigned (N.v38422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38422 s i)) at 1.
  unfold R.v38422, N.v38422.
  unfold R.v6, N.v6.
  rewrite ?node_5984.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38423 (s : N.State) (i : N.Inputs) :
  R.v38423 (state s) (inputs i) = Zmod.unsigned (N.v38423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38423 s i)) at 1.
  unfold R.v38423, N.v38423.
  rewrite ?node_38421.
  rewrite ?node_38422.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38424 (s : N.State) (i : N.Inputs) :
  R.v38424 (state s) (inputs i) = Zmod.unsigned (N.v38424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38424 s i)) at 1.
  unfold R.v38424, N.v38424.
  rewrite ?node_38420.
  rewrite ?node_38423.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38425 (s : N.State) (i : N.Inputs) :
  R.v38425 (state s) (inputs i) = Zmod.unsigned (N.v38425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38425 s i)) at 1.
  unfold R.v38425, N.v38425.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38426 (s : N.State) (i : N.Inputs) :
  R.v38426 (state s) (inputs i) = Zmod.unsigned (N.v38426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38426 s i)) at 1.
  unfold R.v38426, N.v38426.
  rewrite ?node_5915.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38427 (s : N.State) (i : N.Inputs) :
  R.v38427 (state s) (inputs i) = Zmod.unsigned (N.v38427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38427 s i)) at 1.
  unfold R.v38427, N.v38427.
  unfold R.v6, N.v6.
  rewrite ?node_5911.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38428 (s : N.State) (i : N.Inputs) :
  R.v38428 (state s) (inputs i) = Zmod.unsigned (N.v38428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38428 s i)) at 1.
  unfold R.v38428, N.v38428.
  unfold R.v6, N.v6.
  rewrite ?node_5908.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38429 (s : N.State) (i : N.Inputs) :
  R.v38429 (state s) (inputs i) = Zmod.unsigned (N.v38429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38429 s i)) at 1.
  unfold R.v38429, N.v38429.
  rewrite ?node_38427.
  rewrite ?node_38428.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38430 (s : N.State) (i : N.Inputs) :
  R.v38430 (state s) (inputs i) = Zmod.unsigned (N.v38430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38430 s i)) at 1.
  unfold R.v38430, N.v38430.
  unfold R.v16484, N.v16484.
  rewrite ?node_38429.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38431 (s : N.State) (i : N.Inputs) :
  R.v38431 (state s) (inputs i) = Zmod.unsigned (N.v38431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38431 s i)) at 1.
  unfold R.v38431, N.v38431.
  rewrite ?node_38426.
  rewrite ?node_38430.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38432 (s : N.State) (i : N.Inputs) :
  R.v38432 (state s) (inputs i) = Zmod.unsigned (N.v38432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38432 s i)) at 1.
  unfold R.v38432, N.v38432.
  unfold R.v6, N.v6.
  rewrite ?node_38431.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38433 (s : N.State) (i : N.Inputs) :
  R.v38433 (state s) (inputs i) = Zmod.unsigned (N.v38433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38433 s i)) at 1.
  unfold R.v38433, N.v38433.
  rewrite ?node_5916.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38434 (s : N.State) (i : N.Inputs) :
  R.v38434 (state s) (inputs i) = Zmod.unsigned (N.v38434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38434 s i)) at 1.
  unfold R.v38434, N.v38434.
  unfold R.v6, N.v6.
  rewrite ?node_5988.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38435 (s : N.State) (i : N.Inputs) :
  R.v38435 (state s) (inputs i) = Zmod.unsigned (N.v38435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38435 s i)) at 1.
  unfold R.v38435, N.v38435.
  rewrite ?node_38433.
  rewrite ?node_38434.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38436 (s : N.State) (i : N.Inputs) :
  R.v38436 (state s) (inputs i) = Zmod.unsigned (N.v38436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38436 s i)) at 1.
  unfold R.v38436, N.v38436.
  rewrite ?node_38432.
  rewrite ?node_38435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38437 (s : N.State) (i : N.Inputs) :
  R.v38437 (state s) (inputs i) = Zmod.unsigned (N.v38437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38437 s i)) at 1.
  unfold R.v38437, N.v38437.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38438 (s : N.State) (i : N.Inputs) :
  R.v38438 (state s) (inputs i) = Zmod.unsigned (N.v38438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38438 s i)) at 1.
  unfold R.v38438, N.v38438.
  rewrite ?node_5966.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38439 (s : N.State) (i : N.Inputs) :
  R.v38439 (state s) (inputs i) = Zmod.unsigned (N.v38439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38439 s i)) at 1.
  unfold R.v38439, N.v38439.
  rewrite ?node_5962.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38440 (s : N.State) (i : N.Inputs) :
  R.v38440 (state s) (inputs i) = Zmod.unsigned (N.v38440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38440 s i)) at 1.
  unfold R.v38440, N.v38440.
  rewrite ?node_5960.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38441 (s : N.State) (i : N.Inputs) :
  R.v38441 (state s) (inputs i) = Zmod.unsigned (N.v38441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38441 s i)) at 1.
  unfold R.v38441, N.v38441.
  unfold R.v6, N.v6.
  rewrite ?node_5952.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38442 (s : N.State) (i : N.Inputs) :
  R.v38442 (state s) (inputs i) = Zmod.unsigned (N.v38442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38442 s i)) at 1.
  unfold R.v38442, N.v38442.
  unfold R.v6, N.v6.
  rewrite ?node_5945.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38443 (s : N.State) (i : N.Inputs) :
  R.v38443 (state s) (inputs i) = Zmod.unsigned (N.v38443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38443 s i)) at 1.
  unfold R.v38443, N.v38443.
  rewrite ?node_38441.
  rewrite ?node_38442.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38444 (s : N.State) (i : N.Inputs) :
  R.v38444 (state s) (inputs i) = Zmod.unsigned (N.v38444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38444 s i)) at 1.
  unfold R.v38444, N.v38444.
  unfold R.v16484, N.v16484.
  rewrite ?node_38443.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38445 (s : N.State) (i : N.Inputs) :
  R.v38445 (state s) (inputs i) = Zmod.unsigned (N.v38445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38445 s i)) at 1.
  unfold R.v38445, N.v38445.
  rewrite ?node_38438.
  rewrite ?node_38439.
  rewrite ?node_38440.
  rewrite ?node_38444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38446 (s : N.State) (i : N.Inputs) :
  R.v38446 (state s) (inputs i) = Zmod.unsigned (N.v38446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38446 s i)) at 1.
  unfold R.v38446, N.v38446.
  unfold R.v6, N.v6.
  rewrite ?node_38445.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38447 (s : N.State) (i : N.Inputs) :
  R.v38447 (state s) (inputs i) = Zmod.unsigned (N.v38447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38447 s i)) at 1.
  unfold R.v38447, N.v38447.
  rewrite ?node_5967.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38448 (s : N.State) (i : N.Inputs) :
  R.v38448 (state s) (inputs i) = Zmod.unsigned (N.v38448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38448 s i)) at 1.
  unfold R.v38448, N.v38448.
  unfold R.v6, N.v6.
  rewrite ?node_6031.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38449 (s : N.State) (i : N.Inputs) :
  R.v38449 (state s) (inputs i) = Zmod.unsigned (N.v38449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38449 s i)) at 1.
  unfold R.v38449, N.v38449.
  unfold R.v6, N.v6.
  rewrite ?node_6053.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38450 (s : N.State) (i : N.Inputs) :
  R.v38450 (state s) (inputs i) = Zmod.unsigned (N.v38450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38450 s i)) at 1.
  unfold R.v38450, N.v38450.
  rewrite ?node_38447.
  rewrite ?node_38448.
  rewrite ?node_38449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38451 (s : N.State) (i : N.Inputs) :
  R.v38451 (state s) (inputs i) = Zmod.unsigned (N.v38451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38451 s i)) at 1.
  unfold R.v38451, N.v38451.
  rewrite ?node_38446.
  rewrite ?node_38450.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38452 (s : N.State) (i : N.Inputs) :
  R.v38452 (state s) (inputs i) = Zmod.unsigned (N.v38452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38452 s i)) at 1.
  unfold R.v38452, N.v38452.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38453 (s : N.State) (i : N.Inputs) :
  R.v38453 (state s) (inputs i) = Zmod.unsigned (N.v38453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38453 s i)) at 1.
  unfold R.v38453, N.v38453.
  rewrite ?node_5960.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38454 (s : N.State) (i : N.Inputs) :
  R.v38454 (state s) (inputs i) = Zmod.unsigned (N.v38454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38454 s i)) at 1.
  unfold R.v38454, N.v38454.
  unfold R.v6, N.v6.
  rewrite ?node_5952.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38455 (s : N.State) (i : N.Inputs) :
  R.v38455 (state s) (inputs i) = Zmod.unsigned (N.v38455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38455 s i)) at 1.
  unfold R.v38455, N.v38455.
  unfold R.v6, N.v6.
  rewrite ?node_5945.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38456 (s : N.State) (i : N.Inputs) :
  R.v38456 (state s) (inputs i) = Zmod.unsigned (N.v38456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38456 s i)) at 1.
  unfold R.v38456, N.v38456.
  rewrite ?node_38454.
  rewrite ?node_38455.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38457 (s : N.State) (i : N.Inputs) :
  R.v38457 (state s) (inputs i) = Zmod.unsigned (N.v38457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38457 s i)) at 1.
  unfold R.v38457, N.v38457.
  unfold R.v16484, N.v16484.
  rewrite ?node_38456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38458 (s : N.State) (i : N.Inputs) :
  R.v38458 (state s) (inputs i) = Zmod.unsigned (N.v38458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38458 s i)) at 1.
  unfold R.v38458, N.v38458.
  rewrite ?node_38453.
  rewrite ?node_38457.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38459 (s : N.State) (i : N.Inputs) :
  R.v38459 (state s) (inputs i) = Zmod.unsigned (N.v38459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38459 s i)) at 1.
  unfold R.v38459, N.v38459.
  unfold R.v6, N.v6.
  rewrite ?node_38458.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38460 (s : N.State) (i : N.Inputs) :
  R.v38460 (state s) (inputs i) = Zmod.unsigned (N.v38460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38460 s i)) at 1.
  unfold R.v38460, N.v38460.
  rewrite ?node_5961.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38461 (s : N.State) (i : N.Inputs) :
  R.v38461 (state s) (inputs i) = Zmod.unsigned (N.v38461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38461 s i)) at 1.
  unfold R.v38461, N.v38461.
  unfold R.v6, N.v6.
  rewrite ?node_6031.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38462 (s : N.State) (i : N.Inputs) :
  R.v38462 (state s) (inputs i) = Zmod.unsigned (N.v38462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38462 s i)) at 1.
  unfold R.v38462, N.v38462.
  rewrite ?node_38460.
  rewrite ?node_38461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38463 (s : N.State) (i : N.Inputs) :
  R.v38463 (state s) (inputs i) = Zmod.unsigned (N.v38463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38463 s i)) at 1.
  unfold R.v38463, N.v38463.
  rewrite ?node_38459.
  rewrite ?node_38462.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38464 (s : N.State) (i : N.Inputs) :
  R.v38464 (state s) (inputs i) = Zmod.unsigned (N.v38464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38464 s i)) at 1.
  unfold R.v38464, N.v38464.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38465 (s : N.State) (i : N.Inputs) :
  R.v38465 (state s) (inputs i) = Zmod.unsigned (N.v38465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38465 s i)) at 1.
  unfold R.v38465, N.v38465.
  rewrite ?node_5966.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38466 (s : N.State) (i : N.Inputs) :
  R.v38466 (state s) (inputs i) = Zmod.unsigned (N.v38466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38466 s i)) at 1.
  unfold R.v38466, N.v38466.
  unfold R.v6, N.v6.
  rewrite ?node_5962.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38467 (s : N.State) (i : N.Inputs) :
  R.v38467 (state s) (inputs i) = Zmod.unsigned (N.v38467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38467 s i)) at 1.
  unfold R.v38467, N.v38467.
  unfold R.v6, N.v6.
  rewrite ?node_5961.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38468 (s : N.State) (i : N.Inputs) :
  R.v38468 (state s) (inputs i) = Zmod.unsigned (N.v38468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38468 s i)) at 1.
  unfold R.v38468, N.v38468.
  rewrite ?node_38466.
  rewrite ?node_38467.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38469 (s : N.State) (i : N.Inputs) :
  R.v38469 (state s) (inputs i) = Zmod.unsigned (N.v38469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38469 s i)) at 1.
  unfold R.v38469, N.v38469.
  unfold R.v16484, N.v16484.
  rewrite ?node_38468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38470 (s : N.State) (i : N.Inputs) :
  R.v38470 (state s) (inputs i) = Zmod.unsigned (N.v38470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38470 s i)) at 1.
  unfold R.v38470, N.v38470.
  rewrite ?node_38465.
  rewrite ?node_38469.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38471 (s : N.State) (i : N.Inputs) :
  R.v38471 (state s) (inputs i) = Zmod.unsigned (N.v38471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38471 s i)) at 1.
  unfold R.v38471, N.v38471.
  unfold R.v6, N.v6.
  rewrite ?node_38470.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38472 (s : N.State) (i : N.Inputs) :
  R.v38472 (state s) (inputs i) = Zmod.unsigned (N.v38472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38472 s i)) at 1.
  unfold R.v38472, N.v38472.
  rewrite ?node_5967.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38473 (s : N.State) (i : N.Inputs) :
  R.v38473 (state s) (inputs i) = Zmod.unsigned (N.v38473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38473 s i)) at 1.
  unfold R.v38473, N.v38473.
  unfold R.v6, N.v6.
  rewrite ?node_6053.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38474 (s : N.State) (i : N.Inputs) :
  R.v38474 (state s) (inputs i) = Zmod.unsigned (N.v38474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38474 s i)) at 1.
  unfold R.v38474, N.v38474.
  rewrite ?node_38472.
  rewrite ?node_38473.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38475 (s : N.State) (i : N.Inputs) :
  R.v38475 (state s) (inputs i) = Zmod.unsigned (N.v38475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38475 s i)) at 1.
  unfold R.v38475, N.v38475.
  rewrite ?node_38471.
  rewrite ?node_38474.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38476 (s : N.State) (i : N.Inputs) :
  R.v38476 (state s) (inputs i) = Zmod.unsigned (N.v38476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38476 s i)) at 1.
  unfold R.v38476, N.v38476.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38477 (s : N.State) (i : N.Inputs) :
  R.v38477 (state s) (inputs i) = Zmod.unsigned (N.v38477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38477 s i)) at 1.
  unfold R.v38477, N.v38477.
  rewrite ?node_5979.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38478 (s : N.State) (i : N.Inputs) :
  R.v38478 (state s) (inputs i) = Zmod.unsigned (N.v38478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38478 s i)) at 1.
  unfold R.v38478, N.v38478.
  rewrite ?node_5977.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38479 (s : N.State) (i : N.Inputs) :
  R.v38479 (state s) (inputs i) = Zmod.unsigned (N.v38479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38479 s i)) at 1.
  unfold R.v38479, N.v38479.
  unfold R.v6, N.v6.
  rewrite ?node_5973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38480 (s : N.State) (i : N.Inputs) :
  R.v38480 (state s) (inputs i) = Zmod.unsigned (N.v38480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38480 s i)) at 1.
  unfold R.v38480, N.v38480.
  unfold R.v6, N.v6.
  rewrite ?node_5970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38481 (s : N.State) (i : N.Inputs) :
  R.v38481 (state s) (inputs i) = Zmod.unsigned (N.v38481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38481 s i)) at 1.
  unfold R.v38481, N.v38481.
  rewrite ?node_38479.
  rewrite ?node_38480.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38482 (s : N.State) (i : N.Inputs) :
  R.v38482 (state s) (inputs i) = Zmod.unsigned (N.v38482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38482 s i)) at 1.
  unfold R.v38482, N.v38482.
  unfold R.v16484, N.v16484.
  rewrite ?node_38481.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38483 (s : N.State) (i : N.Inputs) :
  R.v38483 (state s) (inputs i) = Zmod.unsigned (N.v38483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38483 s i)) at 1.
  unfold R.v38483, N.v38483.
  rewrite ?node_38477.
  rewrite ?node_38478.
  rewrite ?node_38482.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38484 (s : N.State) (i : N.Inputs) :
  R.v38484 (state s) (inputs i) = Zmod.unsigned (N.v38484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38484 s i)) at 1.
  unfold R.v38484, N.v38484.
  unfold R.v6, N.v6.
  rewrite ?node_38483.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38485 (s : N.State) (i : N.Inputs) :
  R.v38485 (state s) (inputs i) = Zmod.unsigned (N.v38485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38485 s i)) at 1.
  unfold R.v38485, N.v38485.
  rewrite ?node_5980.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38486 (s : N.State) (i : N.Inputs) :
  R.v38486 (state s) (inputs i) = Zmod.unsigned (N.v38486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38486 s i)) at 1.
  unfold R.v38486, N.v38486.
  unfold R.v6, N.v6.
  rewrite ?node_6048.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38487 (s : N.State) (i : N.Inputs) :
  R.v38487 (state s) (inputs i) = Zmod.unsigned (N.v38487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38487 s i)) at 1.
  unfold R.v38487, N.v38487.
  unfold R.v6, N.v6.
  rewrite ?node_6055.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38488 (s : N.State) (i : N.Inputs) :
  R.v38488 (state s) (inputs i) = Zmod.unsigned (N.v38488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38488 s i)) at 1.
  unfold R.v38488, N.v38488.
  rewrite ?node_38485.
  rewrite ?node_38486.
  rewrite ?node_38487.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38489 (s : N.State) (i : N.Inputs) :
  R.v38489 (state s) (inputs i) = Zmod.unsigned (N.v38489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38489 s i)) at 1.
  unfold R.v38489, N.v38489.
  rewrite ?node_38484.
  rewrite ?node_38488.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38490 (s : N.State) (i : N.Inputs) :
  R.v38490 (state s) (inputs i) = Zmod.unsigned (N.v38490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38490 s i)) at 1.
  unfold R.v38490, N.v38490.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38491 (s : N.State) (i : N.Inputs) :
  R.v38491 (state s) (inputs i) = Zmod.unsigned (N.v38491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38491 s i)) at 1.
  unfold R.v38491, N.v38491.
  rewrite ?node_5977.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38492 (s : N.State) (i : N.Inputs) :
  R.v38492 (state s) (inputs i) = Zmod.unsigned (N.v38492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38492 s i)) at 1.
  unfold R.v38492, N.v38492.
  unfold R.v6, N.v6.
  rewrite ?node_5973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38493 (s : N.State) (i : N.Inputs) :
  R.v38493 (state s) (inputs i) = Zmod.unsigned (N.v38493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38493 s i)) at 1.
  unfold R.v38493, N.v38493.
  unfold R.v6, N.v6.
  rewrite ?node_5970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38494 (s : N.State) (i : N.Inputs) :
  R.v38494 (state s) (inputs i) = Zmod.unsigned (N.v38494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38494 s i)) at 1.
  unfold R.v38494, N.v38494.
  rewrite ?node_38492.
  rewrite ?node_38493.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38495 (s : N.State) (i : N.Inputs) :
  R.v38495 (state s) (inputs i) = Zmod.unsigned (N.v38495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38495 s i)) at 1.
  unfold R.v38495, N.v38495.
  unfold R.v16484, N.v16484.
  rewrite ?node_38494.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38496 (s : N.State) (i : N.Inputs) :
  R.v38496 (state s) (inputs i) = Zmod.unsigned (N.v38496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38496 s i)) at 1.
  unfold R.v38496, N.v38496.
  rewrite ?node_38491.
  rewrite ?node_38495.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38497 (s : N.State) (i : N.Inputs) :
  R.v38497 (state s) (inputs i) = Zmod.unsigned (N.v38497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38497 s i)) at 1.
  unfold R.v38497, N.v38497.
  unfold R.v6, N.v6.
  rewrite ?node_38496.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38498 (s : N.State) (i : N.Inputs) :
  R.v38498 (state s) (inputs i) = Zmod.unsigned (N.v38498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38498 s i)) at 1.
  unfold R.v38498, N.v38498.
  rewrite ?node_5978.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38499 (s : N.State) (i : N.Inputs) :
  R.v38499 (state s) (inputs i) = Zmod.unsigned (N.v38499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38499 s i)) at 1.
  unfold R.v38499, N.v38499.
  unfold R.v6, N.v6.
  rewrite ?node_6048.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38500 (s : N.State) (i : N.Inputs) :
  R.v38500 (state s) (inputs i) = Zmod.unsigned (N.v38500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38500 s i)) at 1.
  unfold R.v38500, N.v38500.
  rewrite ?node_38498.
  rewrite ?node_38499.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38501 (s : N.State) (i : N.Inputs) :
  R.v38501 (state s) (inputs i) = Zmod.unsigned (N.v38501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38501 s i)) at 1.
  unfold R.v38501, N.v38501.
  rewrite ?node_38497.
  rewrite ?node_38500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38502 (s : N.State) (i : N.Inputs) :
  R.v38502 (state s) (inputs i) = Zmod.unsigned (N.v38502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38502 s i)) at 1.
  unfold R.v38502, N.v38502.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38503 (s : N.State) (i : N.Inputs) :
  R.v38503 (state s) (inputs i) = Zmod.unsigned (N.v38503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38503 s i)) at 1.
  unfold R.v38503, N.v38503.
  unfold R.v6, N.v6.
  rewrite ?node_5979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38504 (s : N.State) (i : N.Inputs) :
  R.v38504 (state s) (inputs i) = Zmod.unsigned (N.v38504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38504 s i)) at 1.
  unfold R.v38504, N.v38504.
  unfold R.v6, N.v6.
  rewrite ?node_5978.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38505 (s : N.State) (i : N.Inputs) :
  R.v38505 (state s) (inputs i) = Zmod.unsigned (N.v38505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38505 s i)) at 1.
  unfold R.v38505, N.v38505.
  rewrite ?node_38503.
  rewrite ?node_38504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38506 (s : N.State) (i : N.Inputs) :
  R.v38506 (state s) (inputs i) = Zmod.unsigned (N.v38506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38506 s i)) at 1.
  unfold R.v38506, N.v38506.
  unfold R.v16463, N.v16463.
  rewrite ?node_38505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38507 (s : N.State) (i : N.Inputs) :
  R.v38507 (state s) (inputs i) = Zmod.unsigned (N.v38507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38507 s i)) at 1.
  unfold R.v38507, N.v38507.
  rewrite ?node_5980.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38508 (s : N.State) (i : N.Inputs) :
  R.v38508 (state s) (inputs i) = Zmod.unsigned (N.v38508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38508 s i)) at 1.
  unfold R.v38508, N.v38508.
  unfold R.v6, N.v6.
  rewrite ?node_6055.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38509 (s : N.State) (i : N.Inputs) :
  R.v38509 (state s) (inputs i) = Zmod.unsigned (N.v38509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38509 s i)) at 1.
  unfold R.v38509, N.v38509.
  rewrite ?node_38507.
  rewrite ?node_38508.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38510 (s : N.State) (i : N.Inputs) :
  R.v38510 (state s) (inputs i) = Zmod.unsigned (N.v38510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38510 s i)) at 1.
  unfold R.v38510, N.v38510.
  rewrite ?node_38506.
  rewrite ?node_38509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38511 (s : N.State) (i : N.Inputs) :
  R.v38511 (state s) (inputs i) = Zmod.unsigned (N.v38511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38511 s i)) at 1.
  unfold R.v38511, N.v38511.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38512 (s : N.State) (i : N.Inputs) :
  R.v38512 (state s) (inputs i) = Zmod.unsigned (N.v38512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38512 s i)) at 1.
  unfold R.v38512, N.v38512.
  rewrite ?node_6031.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38513 (s : N.State) (i : N.Inputs) :
  R.v38513 (state s) (inputs i) = Zmod.unsigned (N.v38513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38513 s i)) at 1.
  unfold R.v38513, N.v38513.
  rewrite ?node_6027.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38514 (s : N.State) (i : N.Inputs) :
  R.v38514 (state s) (inputs i) = Zmod.unsigned (N.v38514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38514 s i)) at 1.
  unfold R.v38514, N.v38514.
  rewrite ?node_6024.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38515 (s : N.State) (i : N.Inputs) :
  R.v38515 (state s) (inputs i) = Zmod.unsigned (N.v38515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38515 s i)) at 1.
  unfold R.v38515, N.v38515.
  unfold R.v6, N.v6.
  rewrite ?node_6016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38516 (s : N.State) (i : N.Inputs) :
  R.v38516 (state s) (inputs i) = Zmod.unsigned (N.v38516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38516 s i)) at 1.
  unfold R.v38516, N.v38516.
  unfold R.v6, N.v6.
  rewrite ?node_6009.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38517 (s : N.State) (i : N.Inputs) :
  R.v38517 (state s) (inputs i) = Zmod.unsigned (N.v38517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38517 s i)) at 1.
  unfold R.v38517, N.v38517.
  rewrite ?node_38515.
  rewrite ?node_38516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38518 (s : N.State) (i : N.Inputs) :
  R.v38518 (state s) (inputs i) = Zmod.unsigned (N.v38518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38518 s i)) at 1.
  unfold R.v38518, N.v38518.
  unfold R.v16484, N.v16484.
  rewrite ?node_38517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38519 (s : N.State) (i : N.Inputs) :
  R.v38519 (state s) (inputs i) = Zmod.unsigned (N.v38519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38519 s i)) at 1.
  unfold R.v38519, N.v38519.
  rewrite ?node_38512.
  rewrite ?node_38513.
  rewrite ?node_38514.
  rewrite ?node_38518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38520 (s : N.State) (i : N.Inputs) :
  R.v38520 (state s) (inputs i) = Zmod.unsigned (N.v38520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38520 s i)) at 1.
  unfold R.v38520, N.v38520.
  unfold R.v6, N.v6.
  rewrite ?node_38519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38521 (s : N.State) (i : N.Inputs) :
  R.v38521 (state s) (inputs i) = Zmod.unsigned (N.v38521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38521 s i)) at 1.
  unfold R.v38521, N.v38521.
  rewrite ?node_6032.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38522 (s : N.State) (i : N.Inputs) :
  R.v38522 (state s) (inputs i) = Zmod.unsigned (N.v38522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38522 s i)) at 1.
  unfold R.v38522, N.v38522.
  unfold R.v6, N.v6.
  rewrite ?node_6098.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38523 (s : N.State) (i : N.Inputs) :
  R.v38523 (state s) (inputs i) = Zmod.unsigned (N.v38523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38523 s i)) at 1.
  unfold R.v38523, N.v38523.
  unfold R.v6, N.v6.
  rewrite ?node_6122.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38524 (s : N.State) (i : N.Inputs) :
  R.v38524 (state s) (inputs i) = Zmod.unsigned (N.v38524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38524 s i)) at 1.
  unfold R.v38524, N.v38524.
  rewrite ?node_38521.
  rewrite ?node_38522.
  rewrite ?node_38523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38525 (s : N.State) (i : N.Inputs) :
  R.v38525 (state s) (inputs i) = Zmod.unsigned (N.v38525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38525 s i)) at 1.
  unfold R.v38525, N.v38525.
  rewrite ?node_38520.
  rewrite ?node_38524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38526 (s : N.State) (i : N.Inputs) :
  R.v38526 (state s) (inputs i) = Zmod.unsigned (N.v38526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38526 s i)) at 1.
  unfold R.v38526, N.v38526.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38527 (s : N.State) (i : N.Inputs) :
  R.v38527 (state s) (inputs i) = Zmod.unsigned (N.v38527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38527 s i)) at 1.
  unfold R.v38527, N.v38527.
  rewrite ?node_6024.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38528 (s : N.State) (i : N.Inputs) :
  R.v38528 (state s) (inputs i) = Zmod.unsigned (N.v38528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38528 s i)) at 1.
  unfold R.v38528, N.v38528.
  unfold R.v6, N.v6.
  rewrite ?node_6016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38529 (s : N.State) (i : N.Inputs) :
  R.v38529 (state s) (inputs i) = Zmod.unsigned (N.v38529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38529 s i)) at 1.
  unfold R.v38529, N.v38529.
  unfold R.v6, N.v6.
  rewrite ?node_6009.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38530 (s : N.State) (i : N.Inputs) :
  R.v38530 (state s) (inputs i) = Zmod.unsigned (N.v38530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38530 s i)) at 1.
  unfold R.v38530, N.v38530.
  rewrite ?node_38528.
  rewrite ?node_38529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38531 (s : N.State) (i : N.Inputs) :
  R.v38531 (state s) (inputs i) = Zmod.unsigned (N.v38531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38531 s i)) at 1.
  unfold R.v38531, N.v38531.
  unfold R.v16484, N.v16484.
  rewrite ?node_38530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38532 (s : N.State) (i : N.Inputs) :
  R.v38532 (state s) (inputs i) = Zmod.unsigned (N.v38532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38532 s i)) at 1.
  unfold R.v38532, N.v38532.
  rewrite ?node_38527.
  rewrite ?node_38531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38533 (s : N.State) (i : N.Inputs) :
  R.v38533 (state s) (inputs i) = Zmod.unsigned (N.v38533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38533 s i)) at 1.
  unfold R.v38533, N.v38533.
  unfold R.v6, N.v6.
  rewrite ?node_38532.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38534 (s : N.State) (i : N.Inputs) :
  R.v38534 (state s) (inputs i) = Zmod.unsigned (N.v38534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38534 s i)) at 1.
  unfold R.v38534, N.v38534.
  rewrite ?node_6025.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38535 (s : N.State) (i : N.Inputs) :
  R.v38535 (state s) (inputs i) = Zmod.unsigned (N.v38535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38535 s i)) at 1.
  unfold R.v38535, N.v38535.
  unfold R.v6, N.v6.
  rewrite ?node_6098.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38536 (s : N.State) (i : N.Inputs) :
  R.v38536 (state s) (inputs i) = Zmod.unsigned (N.v38536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38536 s i)) at 1.
  unfold R.v38536, N.v38536.
  rewrite ?node_38534.
  rewrite ?node_38535.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38537 (s : N.State) (i : N.Inputs) :
  R.v38537 (state s) (inputs i) = Zmod.unsigned (N.v38537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38537 s i)) at 1.
  unfold R.v38537, N.v38537.
  rewrite ?node_38533.
  rewrite ?node_38536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38538 (s : N.State) (i : N.Inputs) :
  R.v38538 (state s) (inputs i) = Zmod.unsigned (N.v38538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38538 s i)) at 1.
  unfold R.v38538, N.v38538.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38539 (s : N.State) (i : N.Inputs) :
  R.v38539 (state s) (inputs i) = Zmod.unsigned (N.v38539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38539 s i)) at 1.
  unfold R.v38539, N.v38539.
  rewrite ?node_6031.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38540 (s : N.State) (i : N.Inputs) :
  R.v38540 (state s) (inputs i) = Zmod.unsigned (N.v38540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38540 s i)) at 1.
  unfold R.v38540, N.v38540.
  unfold R.v6, N.v6.
  rewrite ?node_6027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38541 (s : N.State) (i : N.Inputs) :
  R.v38541 (state s) (inputs i) = Zmod.unsigned (N.v38541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38541 s i)) at 1.
  unfold R.v38541, N.v38541.
  unfold R.v6, N.v6.
  rewrite ?node_6025.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38542 (s : N.State) (i : N.Inputs) :
  R.v38542 (state s) (inputs i) = Zmod.unsigned (N.v38542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38542 s i)) at 1.
  unfold R.v38542, N.v38542.
  rewrite ?node_38540.
  rewrite ?node_38541.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38543 (s : N.State) (i : N.Inputs) :
  R.v38543 (state s) (inputs i) = Zmod.unsigned (N.v38543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38543 s i)) at 1.
  unfold R.v38543, N.v38543.
  unfold R.v16484, N.v16484.
  rewrite ?node_38542.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38544 (s : N.State) (i : N.Inputs) :
  R.v38544 (state s) (inputs i) = Zmod.unsigned (N.v38544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38544 s i)) at 1.
  unfold R.v38544, N.v38544.
  rewrite ?node_38539.
  rewrite ?node_38543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38545 (s : N.State) (i : N.Inputs) :
  R.v38545 (state s) (inputs i) = Zmod.unsigned (N.v38545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38545 s i)) at 1.
  unfold R.v38545, N.v38545.
  unfold R.v6, N.v6.
  rewrite ?node_38544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38546 (s : N.State) (i : N.Inputs) :
  R.v38546 (state s) (inputs i) = Zmod.unsigned (N.v38546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38546 s i)) at 1.
  unfold R.v38546, N.v38546.
  rewrite ?node_6032.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38547 (s : N.State) (i : N.Inputs) :
  R.v38547 (state s) (inputs i) = Zmod.unsigned (N.v38547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38547 s i)) at 1.
  unfold R.v38547, N.v38547.
  unfold R.v6, N.v6.
  rewrite ?node_6122.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38548 (s : N.State) (i : N.Inputs) :
  R.v38548 (state s) (inputs i) = Zmod.unsigned (N.v38548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38548 s i)) at 1.
  unfold R.v38548, N.v38548.
  rewrite ?node_38546.
  rewrite ?node_38547.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38549 (s : N.State) (i : N.Inputs) :
  R.v38549 (state s) (inputs i) = Zmod.unsigned (N.v38549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38549 s i)) at 1.
  unfold R.v38549, N.v38549.
  rewrite ?node_38545.
  rewrite ?node_38548.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38550 (s : N.State) (i : N.Inputs) :
  R.v38550 (state s) (inputs i) = Zmod.unsigned (N.v38550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38550 s i)) at 1.
  unfold R.v38550, N.v38550.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38551 (s : N.State) (i : N.Inputs) :
  R.v38551 (state s) (inputs i) = Zmod.unsigned (N.v38551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38551 s i)) at 1.
  unfold R.v38551, N.v38551.
  rewrite ?node_6048.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38552 (s : N.State) (i : N.Inputs) :
  R.v38552 (state s) (inputs i) = Zmod.unsigned (N.v38552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38552 s i)) at 1.
  unfold R.v38552, N.v38552.
  rewrite ?node_6044.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38553 (s : N.State) (i : N.Inputs) :
  R.v38553 (state s) (inputs i) = Zmod.unsigned (N.v38553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38553 s i)) at 1.
  unfold R.v38553, N.v38553.
  rewrite ?node_6042.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38554 (s : N.State) (i : N.Inputs) :
  R.v38554 (state s) (inputs i) = Zmod.unsigned (N.v38554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38554 s i)) at 1.
  unfold R.v38554, N.v38554.
  unfold R.v6, N.v6.
  rewrite ?node_6038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38555 (s : N.State) (i : N.Inputs) :
  R.v38555 (state s) (inputs i) = Zmod.unsigned (N.v38555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38555 s i)) at 1.
  unfold R.v38555, N.v38555.
  unfold R.v6, N.v6.
  rewrite ?node_6035.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38556 (s : N.State) (i : N.Inputs) :
  R.v38556 (state s) (inputs i) = Zmod.unsigned (N.v38556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38556 s i)) at 1.
  unfold R.v38556, N.v38556.
  rewrite ?node_38554.
  rewrite ?node_38555.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38557 (s : N.State) (i : N.Inputs) :
  R.v38557 (state s) (inputs i) = Zmod.unsigned (N.v38557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38557 s i)) at 1.
  unfold R.v38557, N.v38557.
  unfold R.v16484, N.v16484.
  rewrite ?node_38556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38558 (s : N.State) (i : N.Inputs) :
  R.v38558 (state s) (inputs i) = Zmod.unsigned (N.v38558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38558 s i)) at 1.
  unfold R.v38558, N.v38558.
  rewrite ?node_38551.
  rewrite ?node_38552.
  rewrite ?node_38553.
  rewrite ?node_38557.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38559 (s : N.State) (i : N.Inputs) :
  R.v38559 (state s) (inputs i) = Zmod.unsigned (N.v38559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38559 s i)) at 1.
  unfold R.v38559, N.v38559.
  unfold R.v6, N.v6.
  rewrite ?node_38558.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38560 (s : N.State) (i : N.Inputs) :
  R.v38560 (state s) (inputs i) = Zmod.unsigned (N.v38560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38560 s i)) at 1.
  unfold R.v38560, N.v38560.
  rewrite ?node_6049.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38561 (s : N.State) (i : N.Inputs) :
  R.v38561 (state s) (inputs i) = Zmod.unsigned (N.v38561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38561 s i)) at 1.
  unfold R.v38561, N.v38561.
  unfold R.v6, N.v6.
  rewrite ?node_6117.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38562 (s : N.State) (i : N.Inputs) :
  R.v38562 (state s) (inputs i) = Zmod.unsigned (N.v38562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38562 s i)) at 1.
  unfold R.v38562, N.v38562.
  unfold R.v6, N.v6.
  rewrite ?node_6126.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38563 (s : N.State) (i : N.Inputs) :
  R.v38563 (state s) (inputs i) = Zmod.unsigned (N.v38563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38563 s i)) at 1.
  unfold R.v38563, N.v38563.
  rewrite ?node_38560.
  rewrite ?node_38561.
  rewrite ?node_38562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38564 (s : N.State) (i : N.Inputs) :
  R.v38564 (state s) (inputs i) = Zmod.unsigned (N.v38564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38564 s i)) at 1.
  unfold R.v38564, N.v38564.
  rewrite ?node_38559.
  rewrite ?node_38563.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38565 (s : N.State) (i : N.Inputs) :
  R.v38565 (state s) (inputs i) = Zmod.unsigned (N.v38565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38565 s i)) at 1.
  unfold R.v38565, N.v38565.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38566 (s : N.State) (i : N.Inputs) :
  R.v38566 (state s) (inputs i) = Zmod.unsigned (N.v38566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38566 s i)) at 1.
  unfold R.v38566, N.v38566.
  rewrite ?node_6042.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38567 (s : N.State) (i : N.Inputs) :
  R.v38567 (state s) (inputs i) = Zmod.unsigned (N.v38567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38567 s i)) at 1.
  unfold R.v38567, N.v38567.
  unfold R.v6, N.v6.
  rewrite ?node_6038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38568 (s : N.State) (i : N.Inputs) :
  R.v38568 (state s) (inputs i) = Zmod.unsigned (N.v38568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38568 s i)) at 1.
  unfold R.v38568, N.v38568.
  unfold R.v6, N.v6.
  rewrite ?node_6035.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38569 (s : N.State) (i : N.Inputs) :
  R.v38569 (state s) (inputs i) = Zmod.unsigned (N.v38569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38569 s i)) at 1.
  unfold R.v38569, N.v38569.
  rewrite ?node_38567.
  rewrite ?node_38568.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38570 (s : N.State) (i : N.Inputs) :
  R.v38570 (state s) (inputs i) = Zmod.unsigned (N.v38570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38570 s i)) at 1.
  unfold R.v38570, N.v38570.
  unfold R.v16484, N.v16484.
  rewrite ?node_38569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38571 (s : N.State) (i : N.Inputs) :
  R.v38571 (state s) (inputs i) = Zmod.unsigned (N.v38571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38571 s i)) at 1.
  unfold R.v38571, N.v38571.
  rewrite ?node_38566.
  rewrite ?node_38570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38572 (s : N.State) (i : N.Inputs) :
  R.v38572 (state s) (inputs i) = Zmod.unsigned (N.v38572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38572 s i)) at 1.
  unfold R.v38572, N.v38572.
  unfold R.v6, N.v6.
  rewrite ?node_38571.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38573 (s : N.State) (i : N.Inputs) :
  R.v38573 (state s) (inputs i) = Zmod.unsigned (N.v38573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38573 s i)) at 1.
  unfold R.v38573, N.v38573.
  rewrite ?node_6043.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38574 (s : N.State) (i : N.Inputs) :
  R.v38574 (state s) (inputs i) = Zmod.unsigned (N.v38574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38574 s i)) at 1.
  unfold R.v38574, N.v38574.
  unfold R.v6, N.v6.
  rewrite ?node_6117.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38575 (s : N.State) (i : N.Inputs) :
  R.v38575 (state s) (inputs i) = Zmod.unsigned (N.v38575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38575 s i)) at 1.
  unfold R.v38575, N.v38575.
  rewrite ?node_38573.
  rewrite ?node_38574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38576 (s : N.State) (i : N.Inputs) :
  R.v38576 (state s) (inputs i) = Zmod.unsigned (N.v38576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38576 s i)) at 1.
  unfold R.v38576, N.v38576.
  rewrite ?node_38572.
  rewrite ?node_38575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38577 (s : N.State) (i : N.Inputs) :
  R.v38577 (state s) (inputs i) = Zmod.unsigned (N.v38577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38577 s i)) at 1.
  unfold R.v38577, N.v38577.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38578 (s : N.State) (i : N.Inputs) :
  R.v38578 (state s) (inputs i) = Zmod.unsigned (N.v38578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38578 s i)) at 1.
  unfold R.v38578, N.v38578.
  rewrite ?node_6048.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38579 (s : N.State) (i : N.Inputs) :
  R.v38579 (state s) (inputs i) = Zmod.unsigned (N.v38579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38579 s i)) at 1.
  unfold R.v38579, N.v38579.
  unfold R.v6, N.v6.
  rewrite ?node_6044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38580 (s : N.State) (i : N.Inputs) :
  R.v38580 (state s) (inputs i) = Zmod.unsigned (N.v38580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38580 s i)) at 1.
  unfold R.v38580, N.v38580.
  unfold R.v6, N.v6.
  rewrite ?node_6043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38581 (s : N.State) (i : N.Inputs) :
  R.v38581 (state s) (inputs i) = Zmod.unsigned (N.v38581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38581 s i)) at 1.
  unfold R.v38581, N.v38581.
  rewrite ?node_38579.
  rewrite ?node_38580.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38582 (s : N.State) (i : N.Inputs) :
  R.v38582 (state s) (inputs i) = Zmod.unsigned (N.v38582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38582 s i)) at 1.
  unfold R.v38582, N.v38582.
  unfold R.v16484, N.v16484.
  rewrite ?node_38581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38583 (s : N.State) (i : N.Inputs) :
  R.v38583 (state s) (inputs i) = Zmod.unsigned (N.v38583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38583 s i)) at 1.
  unfold R.v38583, N.v38583.
  rewrite ?node_38578.
  rewrite ?node_38582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38584 (s : N.State) (i : N.Inputs) :
  R.v38584 (state s) (inputs i) = Zmod.unsigned (N.v38584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38584 s i)) at 1.
  unfold R.v38584, N.v38584.
  unfold R.v6, N.v6.
  rewrite ?node_38583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38585 (s : N.State) (i : N.Inputs) :
  R.v38585 (state s) (inputs i) = Zmod.unsigned (N.v38585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38585 s i)) at 1.
  unfold R.v38585, N.v38585.
  rewrite ?node_6049.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38586 (s : N.State) (i : N.Inputs) :
  R.v38586 (state s) (inputs i) = Zmod.unsigned (N.v38586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38586 s i)) at 1.
  unfold R.v38586, N.v38586.
  unfold R.v6, N.v6.
  rewrite ?node_6126.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38587 (s : N.State) (i : N.Inputs) :
  R.v38587 (state s) (inputs i) = Zmod.unsigned (N.v38587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38587 s i)) at 1.
  unfold R.v38587, N.v38587.
  rewrite ?node_38585.
  rewrite ?node_38586.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38588 (s : N.State) (i : N.Inputs) :
  R.v38588 (state s) (inputs i) = Zmod.unsigned (N.v38588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38588 s i)) at 1.
  unfold R.v38588, N.v38588.
  rewrite ?node_38584.
  rewrite ?node_38587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38589 (s : N.State) (i : N.Inputs) :
  R.v38589 (state s) (inputs i) = Zmod.unsigned (N.v38589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38589 s i)) at 1.
  unfold R.v38589, N.v38589.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38590 (s : N.State) (i : N.Inputs) :
  R.v38590 (state s) (inputs i) = Zmod.unsigned (N.v38590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38590 s i)) at 1.
  unfold R.v38590, N.v38590.
  rewrite ?node_6098.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38591 (s : N.State) (i : N.Inputs) :
  R.v38591 (state s) (inputs i) = Zmod.unsigned (N.v38591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38591 s i)) at 1.
  unfold R.v38591, N.v38591.
  rewrite ?node_6094.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38592 (s : N.State) (i : N.Inputs) :
  R.v38592 (state s) (inputs i) = Zmod.unsigned (N.v38592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38592 s i)) at 1.
  unfold R.v38592, N.v38592.
  rewrite ?node_6091.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38593 (s : N.State) (i : N.Inputs) :
  R.v38593 (state s) (inputs i) = Zmod.unsigned (N.v38593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38593 s i)) at 1.
  unfold R.v38593, N.v38593.
  unfold R.v6, N.v6.
  rewrite ?node_6083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38594 (s : N.State) (i : N.Inputs) :
  R.v38594 (state s) (inputs i) = Zmod.unsigned (N.v38594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38594 s i)) at 1.
  unfold R.v38594, N.v38594.
  unfold R.v6, N.v6.
  rewrite ?node_6076.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38595 (s : N.State) (i : N.Inputs) :
  R.v38595 (state s) (inputs i) = Zmod.unsigned (N.v38595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38595 s i)) at 1.
  unfold R.v38595, N.v38595.
  rewrite ?node_38593.
  rewrite ?node_38594.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38596 (s : N.State) (i : N.Inputs) :
  R.v38596 (state s) (inputs i) = Zmod.unsigned (N.v38596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38596 s i)) at 1.
  unfold R.v38596, N.v38596.
  unfold R.v16484, N.v16484.
  rewrite ?node_38595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38597 (s : N.State) (i : N.Inputs) :
  R.v38597 (state s) (inputs i) = Zmod.unsigned (N.v38597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38597 s i)) at 1.
  unfold R.v38597, N.v38597.
  rewrite ?node_38590.
  rewrite ?node_38591.
  rewrite ?node_38592.
  rewrite ?node_38596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38598 (s : N.State) (i : N.Inputs) :
  R.v38598 (state s) (inputs i) = Zmod.unsigned (N.v38598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38598 s i)) at 1.
  unfold R.v38598, N.v38598.
  unfold R.v6, N.v6.
  rewrite ?node_38597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38599 (s : N.State) (i : N.Inputs) :
  R.v38599 (state s) (inputs i) = Zmod.unsigned (N.v38599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38599 s i)) at 1.
  unfold R.v38599, N.v38599.
  rewrite ?node_6099.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38600 (s : N.State) (i : N.Inputs) :
  R.v38600 (state s) (inputs i) = Zmod.unsigned (N.v38600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38600 s i)) at 1.
  unfold R.v38600, N.v38600.
  unfold R.v6, N.v6.
  rewrite ?node_6170.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38601 (s : N.State) (i : N.Inputs) :
  R.v38601 (state s) (inputs i) = Zmod.unsigned (N.v38601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38601 s i)) at 1.
  unfold R.v38601, N.v38601.
  unfold R.v6, N.v6.
  rewrite ?node_6194.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38602 (s : N.State) (i : N.Inputs) :
  R.v38602 (state s) (inputs i) = Zmod.unsigned (N.v38602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38602 s i)) at 1.
  unfold R.v38602, N.v38602.
  rewrite ?node_38599.
  rewrite ?node_38600.
  rewrite ?node_38601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38603 (s : N.State) (i : N.Inputs) :
  R.v38603 (state s) (inputs i) = Zmod.unsigned (N.v38603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38603 s i)) at 1.
  unfold R.v38603, N.v38603.
  rewrite ?node_38598.
  rewrite ?node_38602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38604 (s : N.State) (i : N.Inputs) :
  R.v38604 (state s) (inputs i) = Zmod.unsigned (N.v38604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38604 s i)) at 1.
  unfold R.v38604, N.v38604.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38605 (s : N.State) (i : N.Inputs) :
  R.v38605 (state s) (inputs i) = Zmod.unsigned (N.v38605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38605 s i)) at 1.
  unfold R.v38605, N.v38605.
  rewrite ?node_6091.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38606 (s : N.State) (i : N.Inputs) :
  R.v38606 (state s) (inputs i) = Zmod.unsigned (N.v38606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38606 s i)) at 1.
  unfold R.v38606, N.v38606.
  unfold R.v6, N.v6.
  rewrite ?node_6083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38607 (s : N.State) (i : N.Inputs) :
  R.v38607 (state s) (inputs i) = Zmod.unsigned (N.v38607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38607 s i)) at 1.
  unfold R.v38607, N.v38607.
  unfold R.v6, N.v6.
  rewrite ?node_6076.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38608 (s : N.State) (i : N.Inputs) :
  R.v38608 (state s) (inputs i) = Zmod.unsigned (N.v38608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38608 s i)) at 1.
  unfold R.v38608, N.v38608.
  rewrite ?node_38606.
  rewrite ?node_38607.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38609 (s : N.State) (i : N.Inputs) :
  R.v38609 (state s) (inputs i) = Zmod.unsigned (N.v38609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38609 s i)) at 1.
  unfold R.v38609, N.v38609.
  unfold R.v16484, N.v16484.
  rewrite ?node_38608.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38610 (s : N.State) (i : N.Inputs) :
  R.v38610 (state s) (inputs i) = Zmod.unsigned (N.v38610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38610 s i)) at 1.
  unfold R.v38610, N.v38610.
  rewrite ?node_38605.
  rewrite ?node_38609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38611 (s : N.State) (i : N.Inputs) :
  R.v38611 (state s) (inputs i) = Zmod.unsigned (N.v38611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38611 s i)) at 1.
  unfold R.v38611, N.v38611.
  unfold R.v6, N.v6.
  rewrite ?node_38610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38612 (s : N.State) (i : N.Inputs) :
  R.v38612 (state s) (inputs i) = Zmod.unsigned (N.v38612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38612 s i)) at 1.
  unfold R.v38612, N.v38612.
  rewrite ?node_6092.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38613 (s : N.State) (i : N.Inputs) :
  R.v38613 (state s) (inputs i) = Zmod.unsigned (N.v38613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38613 s i)) at 1.
  unfold R.v38613, N.v38613.
  unfold R.v6, N.v6.
  rewrite ?node_6170.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38614 (s : N.State) (i : N.Inputs) :
  R.v38614 (state s) (inputs i) = Zmod.unsigned (N.v38614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38614 s i)) at 1.
  unfold R.v38614, N.v38614.
  rewrite ?node_38612.
  rewrite ?node_38613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38615 (s : N.State) (i : N.Inputs) :
  R.v38615 (state s) (inputs i) = Zmod.unsigned (N.v38615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38615 s i)) at 1.
  unfold R.v38615, N.v38615.
  rewrite ?node_38611.
  rewrite ?node_38614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38616 (s : N.State) (i : N.Inputs) :
  R.v38616 (state s) (inputs i) = Zmod.unsigned (N.v38616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38616 s i)) at 1.
  unfold R.v38616, N.v38616.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38617 (s : N.State) (i : N.Inputs) :
  R.v38617 (state s) (inputs i) = Zmod.unsigned (N.v38617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38617 s i)) at 1.
  unfold R.v38617, N.v38617.
  rewrite ?node_6098.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38618 (s : N.State) (i : N.Inputs) :
  R.v38618 (state s) (inputs i) = Zmod.unsigned (N.v38618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38618 s i)) at 1.
  unfold R.v38618, N.v38618.
  unfold R.v6, N.v6.
  rewrite ?node_6094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38619 (s : N.State) (i : N.Inputs) :
  R.v38619 (state s) (inputs i) = Zmod.unsigned (N.v38619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38619 s i)) at 1.
  unfold R.v38619, N.v38619.
  unfold R.v6, N.v6.
  rewrite ?node_6092.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38620 (s : N.State) (i : N.Inputs) :
  R.v38620 (state s) (inputs i) = Zmod.unsigned (N.v38620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38620 s i)) at 1.
  unfold R.v38620, N.v38620.
  rewrite ?node_38618.
  rewrite ?node_38619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38621 (s : N.State) (i : N.Inputs) :
  R.v38621 (state s) (inputs i) = Zmod.unsigned (N.v38621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38621 s i)) at 1.
  unfold R.v38621, N.v38621.
  unfold R.v16484, N.v16484.
  rewrite ?node_38620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38622 (s : N.State) (i : N.Inputs) :
  R.v38622 (state s) (inputs i) = Zmod.unsigned (N.v38622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38622 s i)) at 1.
  unfold R.v38622, N.v38622.
  rewrite ?node_38617.
  rewrite ?node_38621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38623 (s : N.State) (i : N.Inputs) :
  R.v38623 (state s) (inputs i) = Zmod.unsigned (N.v38623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38623 s i)) at 1.
  unfold R.v38623, N.v38623.
  unfold R.v6, N.v6.
  rewrite ?node_38622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38624 (s : N.State) (i : N.Inputs) :
  R.v38624 (state s) (inputs i) = Zmod.unsigned (N.v38624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38624 s i)) at 1.
  unfold R.v38624, N.v38624.
  rewrite ?node_6099.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38625 (s : N.State) (i : N.Inputs) :
  R.v38625 (state s) (inputs i) = Zmod.unsigned (N.v38625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38625 s i)) at 1.
  unfold R.v38625, N.v38625.
  unfold R.v6, N.v6.
  rewrite ?node_6194.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38626 (s : N.State) (i : N.Inputs) :
  R.v38626 (state s) (inputs i) = Zmod.unsigned (N.v38626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38626 s i)) at 1.
  unfold R.v38626, N.v38626.
  rewrite ?node_38624.
  rewrite ?node_38625.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38627 (s : N.State) (i : N.Inputs) :
  R.v38627 (state s) (inputs i) = Zmod.unsigned (N.v38627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38627 s i)) at 1.
  unfold R.v38627, N.v38627.
  rewrite ?node_38623.
  rewrite ?node_38626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38628 (s : N.State) (i : N.Inputs) :
  R.v38628 (state s) (inputs i) = Zmod.unsigned (N.v38628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38628 s i)) at 1.
  unfold R.v38628, N.v38628.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38629 (s : N.State) (i : N.Inputs) :
  R.v38629 (state s) (inputs i) = Zmod.unsigned (N.v38629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38629 s i)) at 1.
  unfold R.v38629, N.v38629.
  rewrite ?node_6117.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38630 (s : N.State) (i : N.Inputs) :
  R.v38630 (state s) (inputs i) = Zmod.unsigned (N.v38630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38630 s i)) at 1.
  unfold R.v38630, N.v38630.
  rewrite ?node_6113.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38631 (s : N.State) (i : N.Inputs) :
  R.v38631 (state s) (inputs i) = Zmod.unsigned (N.v38631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38631 s i)) at 1.
  unfold R.v38631, N.v38631.
  rewrite ?node_6109.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38632 (s : N.State) (i : N.Inputs) :
  R.v38632 (state s) (inputs i) = Zmod.unsigned (N.v38632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38632 s i)) at 1.
  unfold R.v38632, N.v38632.
  unfold R.v6, N.v6.
  rewrite ?node_6105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38633 (s : N.State) (i : N.Inputs) :
  R.v38633 (state s) (inputs i) = Zmod.unsigned (N.v38633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38633 s i)) at 1.
  unfold R.v38633, N.v38633.
  unfold R.v6, N.v6.
  rewrite ?node_6102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38634 (s : N.State) (i : N.Inputs) :
  R.v38634 (state s) (inputs i) = Zmod.unsigned (N.v38634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38634 s i)) at 1.
  unfold R.v38634, N.v38634.
  rewrite ?node_38632.
  rewrite ?node_38633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38635 (s : N.State) (i : N.Inputs) :
  R.v38635 (state s) (inputs i) = Zmod.unsigned (N.v38635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38635 s i)) at 1.
  unfold R.v38635, N.v38635.
  unfold R.v16484, N.v16484.
  rewrite ?node_38634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38636 (s : N.State) (i : N.Inputs) :
  R.v38636 (state s) (inputs i) = Zmod.unsigned (N.v38636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38636 s i)) at 1.
  unfold R.v38636, N.v38636.
  rewrite ?node_38629.
  rewrite ?node_38630.
  rewrite ?node_38631.
  rewrite ?node_38635.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38637 (s : N.State) (i : N.Inputs) :
  R.v38637 (state s) (inputs i) = Zmod.unsigned (N.v38637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38637 s i)) at 1.
  unfold R.v38637, N.v38637.
  unfold R.v6, N.v6.
  rewrite ?node_38636.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38638 (s : N.State) (i : N.Inputs) :
  R.v38638 (state s) (inputs i) = Zmod.unsigned (N.v38638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38638 s i)) at 1.
  unfold R.v38638, N.v38638.
  rewrite ?node_6118.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38639 (s : N.State) (i : N.Inputs) :
  R.v38639 (state s) (inputs i) = Zmod.unsigned (N.v38639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38639 s i)) at 1.
  unfold R.v38639, N.v38639.
  unfold R.v6, N.v6.
  rewrite ?node_6189.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38640 (s : N.State) (i : N.Inputs) :
  R.v38640 (state s) (inputs i) = Zmod.unsigned (N.v38640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38640 s i)) at 1.
  unfold R.v38640, N.v38640.
  unfold R.v6, N.v6.
  rewrite ?node_6198.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38641 (s : N.State) (i : N.Inputs) :
  R.v38641 (state s) (inputs i) = Zmod.unsigned (N.v38641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38641 s i)) at 1.
  unfold R.v38641, N.v38641.
  rewrite ?node_38638.
  rewrite ?node_38639.
  rewrite ?node_38640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38642 (s : N.State) (i : N.Inputs) :
  R.v38642 (state s) (inputs i) = Zmod.unsigned (N.v38642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38642 s i)) at 1.
  unfold R.v38642, N.v38642.
  rewrite ?node_38637.
  rewrite ?node_38641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38643 (s : N.State) (i : N.Inputs) :
  R.v38643 (state s) (inputs i) = Zmod.unsigned (N.v38643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38643 s i)) at 1.
  unfold R.v38643, N.v38643.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38644 (s : N.State) (i : N.Inputs) :
  R.v38644 (state s) (inputs i) = Zmod.unsigned (N.v38644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38644 s i)) at 1.
  unfold R.v38644, N.v38644.
  rewrite ?node_6109.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38645 (s : N.State) (i : N.Inputs) :
  R.v38645 (state s) (inputs i) = Zmod.unsigned (N.v38645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38645 s i)) at 1.
  unfold R.v38645, N.v38645.
  unfold R.v6, N.v6.
  rewrite ?node_6105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38646 (s : N.State) (i : N.Inputs) :
  R.v38646 (state s) (inputs i) = Zmod.unsigned (N.v38646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38646 s i)) at 1.
  unfold R.v38646, N.v38646.
  unfold R.v6, N.v6.
  rewrite ?node_6102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38647 (s : N.State) (i : N.Inputs) :
  R.v38647 (state s) (inputs i) = Zmod.unsigned (N.v38647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38647 s i)) at 1.
  unfold R.v38647, N.v38647.
  rewrite ?node_38645.
  rewrite ?node_38646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38648 (s : N.State) (i : N.Inputs) :
  R.v38648 (state s) (inputs i) = Zmod.unsigned (N.v38648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38648 s i)) at 1.
  unfold R.v38648, N.v38648.
  unfold R.v16484, N.v16484.
  rewrite ?node_38647.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38649 (s : N.State) (i : N.Inputs) :
  R.v38649 (state s) (inputs i) = Zmod.unsigned (N.v38649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38649 s i)) at 1.
  unfold R.v38649, N.v38649.
  rewrite ?node_38644.
  rewrite ?node_38648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38650 (s : N.State) (i : N.Inputs) :
  R.v38650 (state s) (inputs i) = Zmod.unsigned (N.v38650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38650 s i)) at 1.
  unfold R.v38650, N.v38650.
  unfold R.v6, N.v6.
  rewrite ?node_38649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38651 (s : N.State) (i : N.Inputs) :
  R.v38651 (state s) (inputs i) = Zmod.unsigned (N.v38651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38651 s i)) at 1.
  unfold R.v38651, N.v38651.
  rewrite ?node_6110.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38652 (s : N.State) (i : N.Inputs) :
  R.v38652 (state s) (inputs i) = Zmod.unsigned (N.v38652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38652 s i)) at 1.
  unfold R.v38652, N.v38652.
  unfold R.v6, N.v6.
  rewrite ?node_6189.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38653 (s : N.State) (i : N.Inputs) :
  R.v38653 (state s) (inputs i) = Zmod.unsigned (N.v38653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38653 s i)) at 1.
  unfold R.v38653, N.v38653.
  rewrite ?node_38651.
  rewrite ?node_38652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38654 (s : N.State) (i : N.Inputs) :
  R.v38654 (state s) (inputs i) = Zmod.unsigned (N.v38654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38654 s i)) at 1.
  unfold R.v38654, N.v38654.
  rewrite ?node_38650.
  rewrite ?node_38653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38655 (s : N.State) (i : N.Inputs) :
  R.v38655 (state s) (inputs i) = Zmod.unsigned (N.v38655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38655 s i)) at 1.
  unfold R.v38655, N.v38655.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38656 (s : N.State) (i : N.Inputs) :
  R.v38656 (state s) (inputs i) = Zmod.unsigned (N.v38656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38656 s i)) at 1.
  unfold R.v38656, N.v38656.
  rewrite ?node_6117.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38657 (s : N.State) (i : N.Inputs) :
  R.v38657 (state s) (inputs i) = Zmod.unsigned (N.v38657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38657 s i)) at 1.
  unfold R.v38657, N.v38657.
  unfold R.v6, N.v6.
  rewrite ?node_6113.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38658 (s : N.State) (i : N.Inputs) :
  R.v38658 (state s) (inputs i) = Zmod.unsigned (N.v38658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38658 s i)) at 1.
  unfold R.v38658, N.v38658.
  unfold R.v6, N.v6.
  rewrite ?node_6110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38659 (s : N.State) (i : N.Inputs) :
  R.v38659 (state s) (inputs i) = Zmod.unsigned (N.v38659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38659 s i)) at 1.
  unfold R.v38659, N.v38659.
  rewrite ?node_38657.
  rewrite ?node_38658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38660 (s : N.State) (i : N.Inputs) :
  R.v38660 (state s) (inputs i) = Zmod.unsigned (N.v38660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38660 s i)) at 1.
  unfold R.v38660, N.v38660.
  unfold R.v16484, N.v16484.
  rewrite ?node_38659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38661 (s : N.State) (i : N.Inputs) :
  R.v38661 (state s) (inputs i) = Zmod.unsigned (N.v38661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38661 s i)) at 1.
  unfold R.v38661, N.v38661.
  rewrite ?node_38656.
  rewrite ?node_38660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38662 (s : N.State) (i : N.Inputs) :
  R.v38662 (state s) (inputs i) = Zmod.unsigned (N.v38662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38662 s i)) at 1.
  unfold R.v38662, N.v38662.
  unfold R.v6, N.v6.
  rewrite ?node_38661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38663 (s : N.State) (i : N.Inputs) :
  R.v38663 (state s) (inputs i) = Zmod.unsigned (N.v38663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38663 s i)) at 1.
  unfold R.v38663, N.v38663.
  rewrite ?node_6118.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38664 (s : N.State) (i : N.Inputs) :
  R.v38664 (state s) (inputs i) = Zmod.unsigned (N.v38664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38664 s i)) at 1.
  unfold R.v38664, N.v38664.
  unfold R.v6, N.v6.
  rewrite ?node_6198.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38665 (s : N.State) (i : N.Inputs) :
  R.v38665 (state s) (inputs i) = Zmod.unsigned (N.v38665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38665 s i)) at 1.
  unfold R.v38665, N.v38665.
  rewrite ?node_38663.
  rewrite ?node_38664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38666 (s : N.State) (i : N.Inputs) :
  R.v38666 (state s) (inputs i) = Zmod.unsigned (N.v38666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38666 s i)) at 1.
  unfold R.v38666, N.v38666.
  rewrite ?node_38662.
  rewrite ?node_38665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38667 (s : N.State) (i : N.Inputs) :
  R.v38667 (state s) (inputs i) = Zmod.unsigned (N.v38667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38667 s i)) at 1.
  unfold R.v38667, N.v38667.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38668 (s : N.State) (i : N.Inputs) :
  R.v38668 (state s) (inputs i) = Zmod.unsigned (N.v38668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38668 s i)) at 1.
  unfold R.v38668, N.v38668.
  rewrite ?node_6170.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38669 (s : N.State) (i : N.Inputs) :
  R.v38669 (state s) (inputs i) = Zmod.unsigned (N.v38669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38669 s i)) at 1.
  unfold R.v38669, N.v38669.
  rewrite ?node_6166.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38670 (s : N.State) (i : N.Inputs) :
  R.v38670 (state s) (inputs i) = Zmod.unsigned (N.v38670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38670 s i)) at 1.
  unfold R.v38670, N.v38670.
  rewrite ?node_6162.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38671 (s : N.State) (i : N.Inputs) :
  R.v38671 (state s) (inputs i) = Zmod.unsigned (N.v38671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38671 s i)) at 1.
  unfold R.v38671, N.v38671.
  unfold R.v6, N.v6.
  rewrite ?node_6154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38672 (s : N.State) (i : N.Inputs) :
  R.v38672 (state s) (inputs i) = Zmod.unsigned (N.v38672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38672 s i)) at 1.
  unfold R.v38672, N.v38672.
  unfold R.v6, N.v6.
  rewrite ?node_6147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38673 (s : N.State) (i : N.Inputs) :
  R.v38673 (state s) (inputs i) = Zmod.unsigned (N.v38673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38673 s i)) at 1.
  unfold R.v38673, N.v38673.
  rewrite ?node_38671.
  rewrite ?node_38672.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38674 (s : N.State) (i : N.Inputs) :
  R.v38674 (state s) (inputs i) = Zmod.unsigned (N.v38674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38674 s i)) at 1.
  unfold R.v38674, N.v38674.
  unfold R.v16484, N.v16484.
  rewrite ?node_38673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38675 (s : N.State) (i : N.Inputs) :
  R.v38675 (state s) (inputs i) = Zmod.unsigned (N.v38675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38675 s i)) at 1.
  unfold R.v38675, N.v38675.
  rewrite ?node_38668.
  rewrite ?node_38669.
  rewrite ?node_38670.
  rewrite ?node_38674.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38676 (s : N.State) (i : N.Inputs) :
  R.v38676 (state s) (inputs i) = Zmod.unsigned (N.v38676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38676 s i)) at 1.
  unfold R.v38676, N.v38676.
  unfold R.v6, N.v6.
  rewrite ?node_38675.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38677 (s : N.State) (i : N.Inputs) :
  R.v38677 (state s) (inputs i) = Zmod.unsigned (N.v38677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38677 s i)) at 1.
  unfold R.v38677, N.v38677.
  rewrite ?node_6171.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38678 (s : N.State) (i : N.Inputs) :
  R.v38678 (state s) (inputs i) = Zmod.unsigned (N.v38678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38678 s i)) at 1.
  unfold R.v38678, N.v38678.
  unfold R.v6, N.v6.
  rewrite ?node_6246.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38679 (s : N.State) (i : N.Inputs) :
  R.v38679 (state s) (inputs i) = Zmod.unsigned (N.v38679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38679 s i)) at 1.
  unfold R.v38679, N.v38679.
  unfold R.v6, N.v6.
  rewrite ?node_6268.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38680 (s : N.State) (i : N.Inputs) :
  R.v38680 (state s) (inputs i) = Zmod.unsigned (N.v38680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38680 s i)) at 1.
  unfold R.v38680, N.v38680.
  rewrite ?node_38677.
  rewrite ?node_38678.
  rewrite ?node_38679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38681 (s : N.State) (i : N.Inputs) :
  R.v38681 (state s) (inputs i) = Zmod.unsigned (N.v38681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38681 s i)) at 1.
  unfold R.v38681, N.v38681.
  rewrite ?node_38676.
  rewrite ?node_38680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38682 (s : N.State) (i : N.Inputs) :
  R.v38682 (state s) (inputs i) = Zmod.unsigned (N.v38682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38682 s i)) at 1.
  unfold R.v38682, N.v38682.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38683 (s : N.State) (i : N.Inputs) :
  R.v38683 (state s) (inputs i) = Zmod.unsigned (N.v38683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38683 s i)) at 1.
  unfold R.v38683, N.v38683.
  rewrite ?node_6162.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38684 (s : N.State) (i : N.Inputs) :
  R.v38684 (state s) (inputs i) = Zmod.unsigned (N.v38684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38684 s i)) at 1.
  unfold R.v38684, N.v38684.
  unfold R.v6, N.v6.
  rewrite ?node_6154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38685 (s : N.State) (i : N.Inputs) :
  R.v38685 (state s) (inputs i) = Zmod.unsigned (N.v38685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38685 s i)) at 1.
  unfold R.v38685, N.v38685.
  unfold R.v6, N.v6.
  rewrite ?node_6147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38686 (s : N.State) (i : N.Inputs) :
  R.v38686 (state s) (inputs i) = Zmod.unsigned (N.v38686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38686 s i)) at 1.
  unfold R.v38686, N.v38686.
  rewrite ?node_38684.
  rewrite ?node_38685.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38687 (s : N.State) (i : N.Inputs) :
  R.v38687 (state s) (inputs i) = Zmod.unsigned (N.v38687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38687 s i)) at 1.
  unfold R.v38687, N.v38687.
  unfold R.v16484, N.v16484.
  rewrite ?node_38686.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38688 (s : N.State) (i : N.Inputs) :
  R.v38688 (state s) (inputs i) = Zmod.unsigned (N.v38688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38688 s i)) at 1.
  unfold R.v38688, N.v38688.
  rewrite ?node_38683.
  rewrite ?node_38687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38689 (s : N.State) (i : N.Inputs) :
  R.v38689 (state s) (inputs i) = Zmod.unsigned (N.v38689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38689 s i)) at 1.
  unfold R.v38689, N.v38689.
  unfold R.v6, N.v6.
  rewrite ?node_38688.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38690 (s : N.State) (i : N.Inputs) :
  R.v38690 (state s) (inputs i) = Zmod.unsigned (N.v38690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38690 s i)) at 1.
  unfold R.v38690, N.v38690.
  rewrite ?node_6163.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38691 (s : N.State) (i : N.Inputs) :
  R.v38691 (state s) (inputs i) = Zmod.unsigned (N.v38691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38691 s i)) at 1.
  unfold R.v38691, N.v38691.
  unfold R.v6, N.v6.
  rewrite ?node_6246.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38692 (s : N.State) (i : N.Inputs) :
  R.v38692 (state s) (inputs i) = Zmod.unsigned (N.v38692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38692 s i)) at 1.
  unfold R.v38692, N.v38692.
  rewrite ?node_38690.
  rewrite ?node_38691.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38693 (s : N.State) (i : N.Inputs) :
  R.v38693 (state s) (inputs i) = Zmod.unsigned (N.v38693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38693 s i)) at 1.
  unfold R.v38693, N.v38693.
  rewrite ?node_38689.
  rewrite ?node_38692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38694 (s : N.State) (i : N.Inputs) :
  R.v38694 (state s) (inputs i) = Zmod.unsigned (N.v38694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38694 s i)) at 1.
  unfold R.v38694, N.v38694.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38695 (s : N.State) (i : N.Inputs) :
  R.v38695 (state s) (inputs i) = Zmod.unsigned (N.v38695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38695 s i)) at 1.
  unfold R.v38695, N.v38695.
  rewrite ?node_6170.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38696 (s : N.State) (i : N.Inputs) :
  R.v38696 (state s) (inputs i) = Zmod.unsigned (N.v38696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38696 s i)) at 1.
  unfold R.v38696, N.v38696.
  unfold R.v6, N.v6.
  rewrite ?node_6166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38697 (s : N.State) (i : N.Inputs) :
  R.v38697 (state s) (inputs i) = Zmod.unsigned (N.v38697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38697 s i)) at 1.
  unfold R.v38697, N.v38697.
  unfold R.v6, N.v6.
  rewrite ?node_6163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38698 (s : N.State) (i : N.Inputs) :
  R.v38698 (state s) (inputs i) = Zmod.unsigned (N.v38698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38698 s i)) at 1.
  unfold R.v38698, N.v38698.
  rewrite ?node_38696.
  rewrite ?node_38697.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38699 (s : N.State) (i : N.Inputs) :
  R.v38699 (state s) (inputs i) = Zmod.unsigned (N.v38699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38699 s i)) at 1.
  unfold R.v38699, N.v38699.
  unfold R.v16484, N.v16484.
  rewrite ?node_38698.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38700 (s : N.State) (i : N.Inputs) :
  R.v38700 (state s) (inputs i) = Zmod.unsigned (N.v38700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38700 s i)) at 1.
  unfold R.v38700, N.v38700.
  rewrite ?node_38695.
  rewrite ?node_38699.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38701 (s : N.State) (i : N.Inputs) :
  R.v38701 (state s) (inputs i) = Zmod.unsigned (N.v38701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38701 s i)) at 1.
  unfold R.v38701, N.v38701.
  unfold R.v6, N.v6.
  rewrite ?node_38700.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38702 (s : N.State) (i : N.Inputs) :
  R.v38702 (state s) (inputs i) = Zmod.unsigned (N.v38702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38702 s i)) at 1.
  unfold R.v38702, N.v38702.
  rewrite ?node_6171.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38703 (s : N.State) (i : N.Inputs) :
  R.v38703 (state s) (inputs i) = Zmod.unsigned (N.v38703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38703 s i)) at 1.
  unfold R.v38703, N.v38703.
  unfold R.v6, N.v6.
  rewrite ?node_6268.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38704 (s : N.State) (i : N.Inputs) :
  R.v38704 (state s) (inputs i) = Zmod.unsigned (N.v38704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38704 s i)) at 1.
  unfold R.v38704, N.v38704.
  rewrite ?node_38702.
  rewrite ?node_38703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38705 (s : N.State) (i : N.Inputs) :
  R.v38705 (state s) (inputs i) = Zmod.unsigned (N.v38705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38705 s i)) at 1.
  unfold R.v38705, N.v38705.
  rewrite ?node_38701.
  rewrite ?node_38704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38706 (s : N.State) (i : N.Inputs) :
  R.v38706 (state s) (inputs i) = Zmod.unsigned (N.v38706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38706 s i)) at 1.
  unfold R.v38706, N.v38706.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38707 (s : N.State) (i : N.Inputs) :
  R.v38707 (state s) (inputs i) = Zmod.unsigned (N.v38707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38707 s i)) at 1.
  unfold R.v38707, N.v38707.
  rewrite ?node_6189.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38708 (s : N.State) (i : N.Inputs) :
  R.v38708 (state s) (inputs i) = Zmod.unsigned (N.v38708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38708 s i)) at 1.
  unfold R.v38708, N.v38708.
  rewrite ?node_6185.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38709 (s : N.State) (i : N.Inputs) :
  R.v38709 (state s) (inputs i) = Zmod.unsigned (N.v38709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38709 s i)) at 1.
  unfold R.v38709, N.v38709.
  rewrite ?node_6181.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38710 (s : N.State) (i : N.Inputs) :
  R.v38710 (state s) (inputs i) = Zmod.unsigned (N.v38710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38710 s i)) at 1.
  unfold R.v38710, N.v38710.
  unfold R.v6, N.v6.
  rewrite ?node_6177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38711 (s : N.State) (i : N.Inputs) :
  R.v38711 (state s) (inputs i) = Zmod.unsigned (N.v38711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38711 s i)) at 1.
  unfold R.v38711, N.v38711.
  unfold R.v6, N.v6.
  rewrite ?node_6174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38712 (s : N.State) (i : N.Inputs) :
  R.v38712 (state s) (inputs i) = Zmod.unsigned (N.v38712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38712 s i)) at 1.
  unfold R.v38712, N.v38712.
  rewrite ?node_38710.
  rewrite ?node_38711.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38713 (s : N.State) (i : N.Inputs) :
  R.v38713 (state s) (inputs i) = Zmod.unsigned (N.v38713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38713 s i)) at 1.
  unfold R.v38713, N.v38713.
  unfold R.v16484, N.v16484.
  rewrite ?node_38712.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38714 (s : N.State) (i : N.Inputs) :
  R.v38714 (state s) (inputs i) = Zmod.unsigned (N.v38714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38714 s i)) at 1.
  unfold R.v38714, N.v38714.
  rewrite ?node_38707.
  rewrite ?node_38708.
  rewrite ?node_38709.
  rewrite ?node_38713.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38715 (s : N.State) (i : N.Inputs) :
  R.v38715 (state s) (inputs i) = Zmod.unsigned (N.v38715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38715 s i)) at 1.
  unfold R.v38715, N.v38715.
  unfold R.v6, N.v6.
  rewrite ?node_38714.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38716 (s : N.State) (i : N.Inputs) :
  R.v38716 (state s) (inputs i) = Zmod.unsigned (N.v38716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38716 s i)) at 1.
  unfold R.v38716, N.v38716.
  rewrite ?node_6190.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38717 (s : N.State) (i : N.Inputs) :
  R.v38717 (state s) (inputs i) = Zmod.unsigned (N.v38717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38717 s i)) at 1.
  unfold R.v38717, N.v38717.
  unfold R.v6, N.v6.
  rewrite ?node_6263.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38718 (s : N.State) (i : N.Inputs) :
  R.v38718 (state s) (inputs i) = Zmod.unsigned (N.v38718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38718 s i)) at 1.
  unfold R.v38718, N.v38718.
  unfold R.v6, N.v6.
  rewrite ?node_6272.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38719 (s : N.State) (i : N.Inputs) :
  R.v38719 (state s) (inputs i) = Zmod.unsigned (N.v38719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38719 s i)) at 1.
  unfold R.v38719, N.v38719.
  rewrite ?node_38716.
  rewrite ?node_38717.
  rewrite ?node_38718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38720 (s : N.State) (i : N.Inputs) :
  R.v38720 (state s) (inputs i) = Zmod.unsigned (N.v38720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38720 s i)) at 1.
  unfold R.v38720, N.v38720.
  rewrite ?node_38715.
  rewrite ?node_38719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38721 (s : N.State) (i : N.Inputs) :
  R.v38721 (state s) (inputs i) = Zmod.unsigned (N.v38721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38721 s i)) at 1.
  unfold R.v38721, N.v38721.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38722 (s : N.State) (i : N.Inputs) :
  R.v38722 (state s) (inputs i) = Zmod.unsigned (N.v38722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38722 s i)) at 1.
  unfold R.v38722, N.v38722.
  rewrite ?node_6181.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38723 (s : N.State) (i : N.Inputs) :
  R.v38723 (state s) (inputs i) = Zmod.unsigned (N.v38723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38723 s i)) at 1.
  unfold R.v38723, N.v38723.
  unfold R.v6, N.v6.
  rewrite ?node_6177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38724 (s : N.State) (i : N.Inputs) :
  R.v38724 (state s) (inputs i) = Zmod.unsigned (N.v38724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38724 s i)) at 1.
  unfold R.v38724, N.v38724.
  unfold R.v6, N.v6.
  rewrite ?node_6174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38725 (s : N.State) (i : N.Inputs) :
  R.v38725 (state s) (inputs i) = Zmod.unsigned (N.v38725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38725 s i)) at 1.
  unfold R.v38725, N.v38725.
  rewrite ?node_38723.
  rewrite ?node_38724.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38726 (s : N.State) (i : N.Inputs) :
  R.v38726 (state s) (inputs i) = Zmod.unsigned (N.v38726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38726 s i)) at 1.
  unfold R.v38726, N.v38726.
  unfold R.v16484, N.v16484.
  rewrite ?node_38725.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38727 (s : N.State) (i : N.Inputs) :
  R.v38727 (state s) (inputs i) = Zmod.unsigned (N.v38727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38727 s i)) at 1.
  unfold R.v38727, N.v38727.
  rewrite ?node_38722.
  rewrite ?node_38726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38728 (s : N.State) (i : N.Inputs) :
  R.v38728 (state s) (inputs i) = Zmod.unsigned (N.v38728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38728 s i)) at 1.
  unfold R.v38728, N.v38728.
  unfold R.v6, N.v6.
  rewrite ?node_38727.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38729 (s : N.State) (i : N.Inputs) :
  R.v38729 (state s) (inputs i) = Zmod.unsigned (N.v38729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38729 s i)) at 1.
  unfold R.v38729, N.v38729.
  rewrite ?node_6182.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38730 (s : N.State) (i : N.Inputs) :
  R.v38730 (state s) (inputs i) = Zmod.unsigned (N.v38730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38730 s i)) at 1.
  unfold R.v38730, N.v38730.
  unfold R.v6, N.v6.
  rewrite ?node_6263.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38731 (s : N.State) (i : N.Inputs) :
  R.v38731 (state s) (inputs i) = Zmod.unsigned (N.v38731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38731 s i)) at 1.
  unfold R.v38731, N.v38731.
  rewrite ?node_38729.
  rewrite ?node_38730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38732 (s : N.State) (i : N.Inputs) :
  R.v38732 (state s) (inputs i) = Zmod.unsigned (N.v38732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38732 s i)) at 1.
  unfold R.v38732, N.v38732.
  rewrite ?node_38728.
  rewrite ?node_38731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38733 (s : N.State) (i : N.Inputs) :
  R.v38733 (state s) (inputs i) = Zmod.unsigned (N.v38733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38733 s i)) at 1.
  unfold R.v38733, N.v38733.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38734 (s : N.State) (i : N.Inputs) :
  R.v38734 (state s) (inputs i) = Zmod.unsigned (N.v38734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38734 s i)) at 1.
  unfold R.v38734, N.v38734.
  rewrite ?node_6189.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38735 (s : N.State) (i : N.Inputs) :
  R.v38735 (state s) (inputs i) = Zmod.unsigned (N.v38735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38735 s i)) at 1.
  unfold R.v38735, N.v38735.
  unfold R.v6, N.v6.
  rewrite ?node_6185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38736 (s : N.State) (i : N.Inputs) :
  R.v38736 (state s) (inputs i) = Zmod.unsigned (N.v38736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38736 s i)) at 1.
  unfold R.v38736, N.v38736.
  unfold R.v6, N.v6.
  rewrite ?node_6182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38737 (s : N.State) (i : N.Inputs) :
  R.v38737 (state s) (inputs i) = Zmod.unsigned (N.v38737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38737 s i)) at 1.
  unfold R.v38737, N.v38737.
  rewrite ?node_38735.
  rewrite ?node_38736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38738 (s : N.State) (i : N.Inputs) :
  R.v38738 (state s) (inputs i) = Zmod.unsigned (N.v38738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38738 s i)) at 1.
  unfold R.v38738, N.v38738.
  unfold R.v16484, N.v16484.
  rewrite ?node_38737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38739 (s : N.State) (i : N.Inputs) :
  R.v38739 (state s) (inputs i) = Zmod.unsigned (N.v38739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38739 s i)) at 1.
  unfold R.v38739, N.v38739.
  rewrite ?node_38734.
  rewrite ?node_38738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38740 (s : N.State) (i : N.Inputs) :
  R.v38740 (state s) (inputs i) = Zmod.unsigned (N.v38740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38740 s i)) at 1.
  unfold R.v38740, N.v38740.
  unfold R.v6, N.v6.
  rewrite ?node_38739.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38741 (s : N.State) (i : N.Inputs) :
  R.v38741 (state s) (inputs i) = Zmod.unsigned (N.v38741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38741 s i)) at 1.
  unfold R.v38741, N.v38741.
  rewrite ?node_6190.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38742 (s : N.State) (i : N.Inputs) :
  R.v38742 (state s) (inputs i) = Zmod.unsigned (N.v38742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38742 s i)) at 1.
  unfold R.v38742, N.v38742.
  unfold R.v6, N.v6.
  rewrite ?node_6272.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38743 (s : N.State) (i : N.Inputs) :
  R.v38743 (state s) (inputs i) = Zmod.unsigned (N.v38743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38743 s i)) at 1.
  unfold R.v38743, N.v38743.
  rewrite ?node_38741.
  rewrite ?node_38742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38744 (s : N.State) (i : N.Inputs) :
  R.v38744 (state s) (inputs i) = Zmod.unsigned (N.v38744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38744 s i)) at 1.
  unfold R.v38744, N.v38744.
  rewrite ?node_38740.
  rewrite ?node_38743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38745 (s : N.State) (i : N.Inputs) :
  R.v38745 (state s) (inputs i) = Zmod.unsigned (N.v38745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38745 s i)) at 1.
  unfold R.v38745, N.v38745.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38746 (s : N.State) (i : N.Inputs) :
  R.v38746 (state s) (inputs i) = Zmod.unsigned (N.v38746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38746 s i)) at 1.
  unfold R.v38746, N.v38746.
  rewrite ?node_6246.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38747 (s : N.State) (i : N.Inputs) :
  R.v38747 (state s) (inputs i) = Zmod.unsigned (N.v38747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38747 s i)) at 1.
  unfold R.v38747, N.v38747.
  rewrite ?node_6242.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38748 (s : N.State) (i : N.Inputs) :
  R.v38748 (state s) (inputs i) = Zmod.unsigned (N.v38748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38748 s i)) at 1.
  unfold R.v38748, N.v38748.
  rewrite ?node_6234.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38749 (s : N.State) (i : N.Inputs) :
  R.v38749 (state s) (inputs i) = Zmod.unsigned (N.v38749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38749 s i)) at 1.
  unfold R.v38749, N.v38749.
  unfold R.v6, N.v6.
  rewrite ?node_6226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38750 (s : N.State) (i : N.Inputs) :
  R.v38750 (state s) (inputs i) = Zmod.unsigned (N.v38750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38750 s i)) at 1.
  unfold R.v38750, N.v38750.
  unfold R.v6, N.v6.
  rewrite ?node_6219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38751 (s : N.State) (i : N.Inputs) :
  R.v38751 (state s) (inputs i) = Zmod.unsigned (N.v38751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38751 s i)) at 1.
  unfold R.v38751, N.v38751.
  rewrite ?node_38749.
  rewrite ?node_38750.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38752 (s : N.State) (i : N.Inputs) :
  R.v38752 (state s) (inputs i) = Zmod.unsigned (N.v38752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38752 s i)) at 1.
  unfold R.v38752, N.v38752.
  unfold R.v16484, N.v16484.
  rewrite ?node_38751.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38753 (s : N.State) (i : N.Inputs) :
  R.v38753 (state s) (inputs i) = Zmod.unsigned (N.v38753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38753 s i)) at 1.
  unfold R.v38753, N.v38753.
  rewrite ?node_38746.
  rewrite ?node_38747.
  rewrite ?node_38748.
  rewrite ?node_38752.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38754 (s : N.State) (i : N.Inputs) :
  R.v38754 (state s) (inputs i) = Zmod.unsigned (N.v38754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38754 s i)) at 1.
  unfold R.v38754, N.v38754.
  unfold R.v6, N.v6.
  rewrite ?node_38753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38755 (s : N.State) (i : N.Inputs) :
  R.v38755 (state s) (inputs i) = Zmod.unsigned (N.v38755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38755 s i)) at 1.
  unfold R.v38755, N.v38755.
  rewrite ?node_6247.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38756 (s : N.State) (i : N.Inputs) :
  R.v38756 (state s) (inputs i) = Zmod.unsigned (N.v38756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38756 s i)) at 1.
  unfold R.v38756, N.v38756.
  unfold R.v6, N.v6.
  rewrite ?node_6320.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38757 (s : N.State) (i : N.Inputs) :
  R.v38757 (state s) (inputs i) = Zmod.unsigned (N.v38757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38757 s i)) at 1.
  unfold R.v38757, N.v38757.
  unfold R.v6, N.v6.
  rewrite ?node_6345.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38758 (s : N.State) (i : N.Inputs) :
  R.v38758 (state s) (inputs i) = Zmod.unsigned (N.v38758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38758 s i)) at 1.
  unfold R.v38758, N.v38758.
  rewrite ?node_38755.
  rewrite ?node_38756.
  rewrite ?node_38757.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38759 (s : N.State) (i : N.Inputs) :
  R.v38759 (state s) (inputs i) = Zmod.unsigned (N.v38759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38759 s i)) at 1.
  unfold R.v38759, N.v38759.
  rewrite ?node_38754.
  rewrite ?node_38758.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38760 (s : N.State) (i : N.Inputs) :
  R.v38760 (state s) (inputs i) = Zmod.unsigned (N.v38760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38760 s i)) at 1.
  unfold R.v38760, N.v38760.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38761 (s : N.State) (i : N.Inputs) :
  R.v38761 (state s) (inputs i) = Zmod.unsigned (N.v38761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38761 s i)) at 1.
  unfold R.v38761, N.v38761.
  rewrite ?node_6234.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38762 (s : N.State) (i : N.Inputs) :
  R.v38762 (state s) (inputs i) = Zmod.unsigned (N.v38762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38762 s i)) at 1.
  unfold R.v38762, N.v38762.
  unfold R.v6, N.v6.
  rewrite ?node_6226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38763 (s : N.State) (i : N.Inputs) :
  R.v38763 (state s) (inputs i) = Zmod.unsigned (N.v38763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38763 s i)) at 1.
  unfold R.v38763, N.v38763.
  unfold R.v6, N.v6.
  rewrite ?node_6219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38764 (s : N.State) (i : N.Inputs) :
  R.v38764 (state s) (inputs i) = Zmod.unsigned (N.v38764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38764 s i)) at 1.
  unfold R.v38764, N.v38764.
  rewrite ?node_38762.
  rewrite ?node_38763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38765 (s : N.State) (i : N.Inputs) :
  R.v38765 (state s) (inputs i) = Zmod.unsigned (N.v38765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38765 s i)) at 1.
  unfold R.v38765, N.v38765.
  unfold R.v16484, N.v16484.
  rewrite ?node_38764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38766 (s : N.State) (i : N.Inputs) :
  R.v38766 (state s) (inputs i) = Zmod.unsigned (N.v38766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38766 s i)) at 1.
  unfold R.v38766, N.v38766.
  rewrite ?node_38761.
  rewrite ?node_38765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38767 (s : N.State) (i : N.Inputs) :
  R.v38767 (state s) (inputs i) = Zmod.unsigned (N.v38767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38767 s i)) at 1.
  unfold R.v38767, N.v38767.
  unfold R.v6, N.v6.
  rewrite ?node_38766.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38768 (s : N.State) (i : N.Inputs) :
  R.v38768 (state s) (inputs i) = Zmod.unsigned (N.v38768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38768 s i)) at 1.
  unfold R.v38768, N.v38768.
  rewrite ?node_6235.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38769 (s : N.State) (i : N.Inputs) :
  R.v38769 (state s) (inputs i) = Zmod.unsigned (N.v38769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38769 s i)) at 1.
  unfold R.v38769, N.v38769.
  unfold R.v6, N.v6.
  rewrite ?node_6320.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38770 (s : N.State) (i : N.Inputs) :
  R.v38770 (state s) (inputs i) = Zmod.unsigned (N.v38770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38770 s i)) at 1.
  unfold R.v38770, N.v38770.
  rewrite ?node_38768.
  rewrite ?node_38769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38771 (s : N.State) (i : N.Inputs) :
  R.v38771 (state s) (inputs i) = Zmod.unsigned (N.v38771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38771 s i)) at 1.
  unfold R.v38771, N.v38771.
  rewrite ?node_38767.
  rewrite ?node_38770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38772 (s : N.State) (i : N.Inputs) :
  R.v38772 (state s) (inputs i) = Zmod.unsigned (N.v38772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38772 s i)) at 1.
  unfold R.v38772, N.v38772.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38773 (s : N.State) (i : N.Inputs) :
  R.v38773 (state s) (inputs i) = Zmod.unsigned (N.v38773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38773 s i)) at 1.
  unfold R.v38773, N.v38773.
  rewrite ?node_6246.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38774 (s : N.State) (i : N.Inputs) :
  R.v38774 (state s) (inputs i) = Zmod.unsigned (N.v38774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38774 s i)) at 1.
  unfold R.v38774, N.v38774.
  unfold R.v6, N.v6.
  rewrite ?node_6242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38775 (s : N.State) (i : N.Inputs) :
  R.v38775 (state s) (inputs i) = Zmod.unsigned (N.v38775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38775 s i)) at 1.
  unfold R.v38775, N.v38775.
  unfold R.v6, N.v6.
  rewrite ?node_6235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38776 (s : N.State) (i : N.Inputs) :
  R.v38776 (state s) (inputs i) = Zmod.unsigned (N.v38776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38776 s i)) at 1.
  unfold R.v38776, N.v38776.
  rewrite ?node_38774.
  rewrite ?node_38775.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38777 (s : N.State) (i : N.Inputs) :
  R.v38777 (state s) (inputs i) = Zmod.unsigned (N.v38777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38777 s i)) at 1.
  unfold R.v38777, N.v38777.
  unfold R.v16484, N.v16484.
  rewrite ?node_38776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38778 (s : N.State) (i : N.Inputs) :
  R.v38778 (state s) (inputs i) = Zmod.unsigned (N.v38778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38778 s i)) at 1.
  unfold R.v38778, N.v38778.
  rewrite ?node_38773.
  rewrite ?node_38777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38779 (s : N.State) (i : N.Inputs) :
  R.v38779 (state s) (inputs i) = Zmod.unsigned (N.v38779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38779 s i)) at 1.
  unfold R.v38779, N.v38779.
  unfold R.v6, N.v6.
  rewrite ?node_38778.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38780 (s : N.State) (i : N.Inputs) :
  R.v38780 (state s) (inputs i) = Zmod.unsigned (N.v38780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38780 s i)) at 1.
  unfold R.v38780, N.v38780.
  rewrite ?node_6247.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38781 (s : N.State) (i : N.Inputs) :
  R.v38781 (state s) (inputs i) = Zmod.unsigned (N.v38781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38781 s i)) at 1.
  unfold R.v38781, N.v38781.
  unfold R.v6, N.v6.
  rewrite ?node_6345.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38782 (s : N.State) (i : N.Inputs) :
  R.v38782 (state s) (inputs i) = Zmod.unsigned (N.v38782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38782 s i)) at 1.
  unfold R.v38782, N.v38782.
  rewrite ?node_38780.
  rewrite ?node_38781.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38783 (s : N.State) (i : N.Inputs) :
  R.v38783 (state s) (inputs i) = Zmod.unsigned (N.v38783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38783 s i)) at 1.
  unfold R.v38783, N.v38783.
  rewrite ?node_38779.
  rewrite ?node_38782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38784 (s : N.State) (i : N.Inputs) :
  R.v38784 (state s) (inputs i) = Zmod.unsigned (N.v38784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38784 s i)) at 1.
  unfold R.v38784, N.v38784.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38785 (s : N.State) (i : N.Inputs) :
  R.v38785 (state s) (inputs i) = Zmod.unsigned (N.v38785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38785 s i)) at 1.
  unfold R.v38785, N.v38785.
  rewrite ?node_6263.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38786 (s : N.State) (i : N.Inputs) :
  R.v38786 (state s) (inputs i) = Zmod.unsigned (N.v38786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38786 s i)) at 1.
  unfold R.v38786, N.v38786.
  rewrite ?node_6259.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38787 (s : N.State) (i : N.Inputs) :
  R.v38787 (state s) (inputs i) = Zmod.unsigned (N.v38787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38787 s i)) at 1.
  unfold R.v38787, N.v38787.
  rewrite ?node_6257.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38788 (s : N.State) (i : N.Inputs) :
  R.v38788 (state s) (inputs i) = Zmod.unsigned (N.v38788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38788 s i)) at 1.
  unfold R.v38788, N.v38788.
  unfold R.v6, N.v6.
  rewrite ?node_6253.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38789 (s : N.State) (i : N.Inputs) :
  R.v38789 (state s) (inputs i) = Zmod.unsigned (N.v38789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38789 s i)) at 1.
  unfold R.v38789, N.v38789.
  unfold R.v6, N.v6.
  rewrite ?node_6250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38790 (s : N.State) (i : N.Inputs) :
  R.v38790 (state s) (inputs i) = Zmod.unsigned (N.v38790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38790 s i)) at 1.
  unfold R.v38790, N.v38790.
  rewrite ?node_38788.
  rewrite ?node_38789.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38791 (s : N.State) (i : N.Inputs) :
  R.v38791 (state s) (inputs i) = Zmod.unsigned (N.v38791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38791 s i)) at 1.
  unfold R.v38791, N.v38791.
  unfold R.v16484, N.v16484.
  rewrite ?node_38790.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38792 (s : N.State) (i : N.Inputs) :
  R.v38792 (state s) (inputs i) = Zmod.unsigned (N.v38792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38792 s i)) at 1.
  unfold R.v38792, N.v38792.
  rewrite ?node_38785.
  rewrite ?node_38786.
  rewrite ?node_38787.
  rewrite ?node_38791.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38793 (s : N.State) (i : N.Inputs) :
  R.v38793 (state s) (inputs i) = Zmod.unsigned (N.v38793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38793 s i)) at 1.
  unfold R.v38793, N.v38793.
  unfold R.v6, N.v6.
  rewrite ?node_38792.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38794 (s : N.State) (i : N.Inputs) :
  R.v38794 (state s) (inputs i) = Zmod.unsigned (N.v38794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38794 s i)) at 1.
  unfold R.v38794, N.v38794.
  rewrite ?node_6264.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38795 (s : N.State) (i : N.Inputs) :
  R.v38795 (state s) (inputs i) = Zmod.unsigned (N.v38795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38795 s i)) at 1.
  unfold R.v38795, N.v38795.
  unfold R.v6, N.v6.
  rewrite ?node_6336.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38796 (s : N.State) (i : N.Inputs) :
  R.v38796 (state s) (inputs i) = Zmod.unsigned (N.v38796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38796 s i)) at 1.
  unfold R.v38796, N.v38796.
  unfold R.v6, N.v6.
  rewrite ?node_6353.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38797 (s : N.State) (i : N.Inputs) :
  R.v38797 (state s) (inputs i) = Zmod.unsigned (N.v38797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38797 s i)) at 1.
  unfold R.v38797, N.v38797.
  rewrite ?node_38794.
  rewrite ?node_38795.
  rewrite ?node_38796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38798 (s : N.State) (i : N.Inputs) :
  R.v38798 (state s) (inputs i) = Zmod.unsigned (N.v38798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38798 s i)) at 1.
  unfold R.v38798, N.v38798.
  rewrite ?node_38793.
  rewrite ?node_38797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38799 (s : N.State) (i : N.Inputs) :
  R.v38799 (state s) (inputs i) = Zmod.unsigned (N.v38799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38799 s i)) at 1.
  unfold R.v38799, N.v38799.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38800 (s : N.State) (i : N.Inputs) :
  R.v38800 (state s) (inputs i) = Zmod.unsigned (N.v38800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38800 s i)) at 1.
  unfold R.v38800, N.v38800.
  rewrite ?node_6257.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38801 (s : N.State) (i : N.Inputs) :
  R.v38801 (state s) (inputs i) = Zmod.unsigned (N.v38801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38801 s i)) at 1.
  unfold R.v38801, N.v38801.
  unfold R.v6, N.v6.
  rewrite ?node_6253.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38802 (s : N.State) (i : N.Inputs) :
  R.v38802 (state s) (inputs i) = Zmod.unsigned (N.v38802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38802 s i)) at 1.
  unfold R.v38802, N.v38802.
  unfold R.v6, N.v6.
  rewrite ?node_6250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38803 (s : N.State) (i : N.Inputs) :
  R.v38803 (state s) (inputs i) = Zmod.unsigned (N.v38803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38803 s i)) at 1.
  unfold R.v38803, N.v38803.
  rewrite ?node_38801.
  rewrite ?node_38802.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38804 (s : N.State) (i : N.Inputs) :
  R.v38804 (state s) (inputs i) = Zmod.unsigned (N.v38804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38804 s i)) at 1.
  unfold R.v38804, N.v38804.
  unfold R.v16484, N.v16484.
  rewrite ?node_38803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38805 (s : N.State) (i : N.Inputs) :
  R.v38805 (state s) (inputs i) = Zmod.unsigned (N.v38805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38805 s i)) at 1.
  unfold R.v38805, N.v38805.
  rewrite ?node_38800.
  rewrite ?node_38804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38806 (s : N.State) (i : N.Inputs) :
  R.v38806 (state s) (inputs i) = Zmod.unsigned (N.v38806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38806 s i)) at 1.
  unfold R.v38806, N.v38806.
  unfold R.v6, N.v6.
  rewrite ?node_38805.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38807 (s : N.State) (i : N.Inputs) :
  R.v38807 (state s) (inputs i) = Zmod.unsigned (N.v38807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38807 s i)) at 1.
  unfold R.v38807, N.v38807.
  rewrite ?node_6258.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38808 (s : N.State) (i : N.Inputs) :
  R.v38808 (state s) (inputs i) = Zmod.unsigned (N.v38808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38808 s i)) at 1.
  unfold R.v38808, N.v38808.
  unfold R.v6, N.v6.
  rewrite ?node_6336.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38809 (s : N.State) (i : N.Inputs) :
  R.v38809 (state s) (inputs i) = Zmod.unsigned (N.v38809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38809 s i)) at 1.
  unfold R.v38809, N.v38809.
  rewrite ?node_38807.
  rewrite ?node_38808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38810 (s : N.State) (i : N.Inputs) :
  R.v38810 (state s) (inputs i) = Zmod.unsigned (N.v38810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38810 s i)) at 1.
  unfold R.v38810, N.v38810.
  rewrite ?node_38806.
  rewrite ?node_38809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38811 (s : N.State) (i : N.Inputs) :
  R.v38811 (state s) (inputs i) = Zmod.unsigned (N.v38811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38811 s i)) at 1.
  unfold R.v38811, N.v38811.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38812 (s : N.State) (i : N.Inputs) :
  R.v38812 (state s) (inputs i) = Zmod.unsigned (N.v38812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38812 s i)) at 1.
  unfold R.v38812, N.v38812.
  rewrite ?node_6263.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38813 (s : N.State) (i : N.Inputs) :
  R.v38813 (state s) (inputs i) = Zmod.unsigned (N.v38813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38813 s i)) at 1.
  unfold R.v38813, N.v38813.
  unfold R.v6, N.v6.
  rewrite ?node_6259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38814 (s : N.State) (i : N.Inputs) :
  R.v38814 (state s) (inputs i) = Zmod.unsigned (N.v38814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38814 s i)) at 1.
  unfold R.v38814, N.v38814.
  unfold R.v6, N.v6.
  rewrite ?node_6258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38815 (s : N.State) (i : N.Inputs) :
  R.v38815 (state s) (inputs i) = Zmod.unsigned (N.v38815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38815 s i)) at 1.
  unfold R.v38815, N.v38815.
  rewrite ?node_38813.
  rewrite ?node_38814.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38816 (s : N.State) (i : N.Inputs) :
  R.v38816 (state s) (inputs i) = Zmod.unsigned (N.v38816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38816 s i)) at 1.
  unfold R.v38816, N.v38816.
  unfold R.v16484, N.v16484.
  rewrite ?node_38815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38817 (s : N.State) (i : N.Inputs) :
  R.v38817 (state s) (inputs i) = Zmod.unsigned (N.v38817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38817 s i)) at 1.
  unfold R.v38817, N.v38817.
  rewrite ?node_38812.
  rewrite ?node_38816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38818 (s : N.State) (i : N.Inputs) :
  R.v38818 (state s) (inputs i) = Zmod.unsigned (N.v38818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38818 s i)) at 1.
  unfold R.v38818, N.v38818.
  unfold R.v6, N.v6.
  rewrite ?node_38817.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38819 (s : N.State) (i : N.Inputs) :
  R.v38819 (state s) (inputs i) = Zmod.unsigned (N.v38819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38819 s i)) at 1.
  unfold R.v38819, N.v38819.
  rewrite ?node_6264.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38820 (s : N.State) (i : N.Inputs) :
  R.v38820 (state s) (inputs i) = Zmod.unsigned (N.v38820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38820 s i)) at 1.
  unfold R.v38820, N.v38820.
  unfold R.v6, N.v6.
  rewrite ?node_6353.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38821 (s : N.State) (i : N.Inputs) :
  R.v38821 (state s) (inputs i) = Zmod.unsigned (N.v38821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38821 s i)) at 1.
  unfold R.v38821, N.v38821.
  rewrite ?node_38819.
  rewrite ?node_38820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38822 (s : N.State) (i : N.Inputs) :
  R.v38822 (state s) (inputs i) = Zmod.unsigned (N.v38822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38822 s i)) at 1.
  unfold R.v38822, N.v38822.
  rewrite ?node_38818.
  rewrite ?node_38821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38823 (s : N.State) (i : N.Inputs) :
  R.v38823 (state s) (inputs i) = Zmod.unsigned (N.v38823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38823 s i)) at 1.
  unfold R.v38823, N.v38823.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38824 (s : N.State) (i : N.Inputs) :
  R.v38824 (state s) (inputs i) = Zmod.unsigned (N.v38824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38824 s i)) at 1.
  unfold R.v38824, N.v38824.
  rewrite ?node_6320.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38825 (s : N.State) (i : N.Inputs) :
  R.v38825 (state s) (inputs i) = Zmod.unsigned (N.v38825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38825 s i)) at 1.
  unfold R.v38825, N.v38825.
  rewrite ?node_6316.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38826 (s : N.State) (i : N.Inputs) :
  R.v38826 (state s) (inputs i) = Zmod.unsigned (N.v38826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38826 s i)) at 1.
  unfold R.v38826, N.v38826.
  rewrite ?node_6308.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38827 (s : N.State) (i : N.Inputs) :
  R.v38827 (state s) (inputs i) = Zmod.unsigned (N.v38827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38827 s i)) at 1.
  unfold R.v38827, N.v38827.
  unfold R.v6, N.v6.
  rewrite ?node_6300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38828 (s : N.State) (i : N.Inputs) :
  R.v38828 (state s) (inputs i) = Zmod.unsigned (N.v38828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38828 s i)) at 1.
  unfold R.v38828, N.v38828.
  unfold R.v6, N.v6.
  rewrite ?node_6293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38829 (s : N.State) (i : N.Inputs) :
  R.v38829 (state s) (inputs i) = Zmod.unsigned (N.v38829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38829 s i)) at 1.
  unfold R.v38829, N.v38829.
  rewrite ?node_38827.
  rewrite ?node_38828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38830 (s : N.State) (i : N.Inputs) :
  R.v38830 (state s) (inputs i) = Zmod.unsigned (N.v38830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38830 s i)) at 1.
  unfold R.v38830, N.v38830.
  unfold R.v16484, N.v16484.
  rewrite ?node_38829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38831 (s : N.State) (i : N.Inputs) :
  R.v38831 (state s) (inputs i) = Zmod.unsigned (N.v38831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38831 s i)) at 1.
  unfold R.v38831, N.v38831.
  rewrite ?node_38824.
  rewrite ?node_38825.
  rewrite ?node_38826.
  rewrite ?node_38830.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38832 (s : N.State) (i : N.Inputs) :
  R.v38832 (state s) (inputs i) = Zmod.unsigned (N.v38832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38832 s i)) at 1.
  unfold R.v38832, N.v38832.
  unfold R.v6, N.v6.
  rewrite ?node_38831.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38833 (s : N.State) (i : N.Inputs) :
  R.v38833 (state s) (inputs i) = Zmod.unsigned (N.v38833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38833 s i)) at 1.
  unfold R.v38833, N.v38833.
  rewrite ?node_6321.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38834 (s : N.State) (i : N.Inputs) :
  R.v38834 (state s) (inputs i) = Zmod.unsigned (N.v38834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38834 s i)) at 1.
  unfold R.v38834, N.v38834.
  unfold R.v6, N.v6.
  rewrite ?node_6397.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38835 (s : N.State) (i : N.Inputs) :
  R.v38835 (state s) (inputs i) = Zmod.unsigned (N.v38835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38835 s i)) at 1.
  unfold R.v38835, N.v38835.
  unfold R.v6, N.v6.
  rewrite ?node_6422.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38836 (s : N.State) (i : N.Inputs) :
  R.v38836 (state s) (inputs i) = Zmod.unsigned (N.v38836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38836 s i)) at 1.
  unfold R.v38836, N.v38836.
  rewrite ?node_38833.
  rewrite ?node_38834.
  rewrite ?node_38835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38837 (s : N.State) (i : N.Inputs) :
  R.v38837 (state s) (inputs i) = Zmod.unsigned (N.v38837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38837 s i)) at 1.
  unfold R.v38837, N.v38837.
  rewrite ?node_38832.
  rewrite ?node_38836.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38838 (s : N.State) (i : N.Inputs) :
  R.v38838 (state s) (inputs i) = Zmod.unsigned (N.v38838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38838 s i)) at 1.
  unfold R.v38838, N.v38838.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38839 (s : N.State) (i : N.Inputs) :
  R.v38839 (state s) (inputs i) = Zmod.unsigned (N.v38839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38839 s i)) at 1.
  unfold R.v38839, N.v38839.
  rewrite ?node_6308.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38840 (s : N.State) (i : N.Inputs) :
  R.v38840 (state s) (inputs i) = Zmod.unsigned (N.v38840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38840 s i)) at 1.
  unfold R.v38840, N.v38840.
  unfold R.v6, N.v6.
  rewrite ?node_6300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38841 (s : N.State) (i : N.Inputs) :
  R.v38841 (state s) (inputs i) = Zmod.unsigned (N.v38841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38841 s i)) at 1.
  unfold R.v38841, N.v38841.
  unfold R.v6, N.v6.
  rewrite ?node_6293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38842 (s : N.State) (i : N.Inputs) :
  R.v38842 (state s) (inputs i) = Zmod.unsigned (N.v38842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38842 s i)) at 1.
  unfold R.v38842, N.v38842.
  rewrite ?node_38840.
  rewrite ?node_38841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38843 (s : N.State) (i : N.Inputs) :
  R.v38843 (state s) (inputs i) = Zmod.unsigned (N.v38843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38843 s i)) at 1.
  unfold R.v38843, N.v38843.
  unfold R.v16484, N.v16484.
  rewrite ?node_38842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38844 (s : N.State) (i : N.Inputs) :
  R.v38844 (state s) (inputs i) = Zmod.unsigned (N.v38844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38844 s i)) at 1.
  unfold R.v38844, N.v38844.
  rewrite ?node_38839.
  rewrite ?node_38843.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38845 (s : N.State) (i : N.Inputs) :
  R.v38845 (state s) (inputs i) = Zmod.unsigned (N.v38845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38845 s i)) at 1.
  unfold R.v38845, N.v38845.
  unfold R.v6, N.v6.
  rewrite ?node_38844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38846 (s : N.State) (i : N.Inputs) :
  R.v38846 (state s) (inputs i) = Zmod.unsigned (N.v38846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38846 s i)) at 1.
  unfold R.v38846, N.v38846.
  rewrite ?node_6309.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38847 (s : N.State) (i : N.Inputs) :
  R.v38847 (state s) (inputs i) = Zmod.unsigned (N.v38847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38847 s i)) at 1.
  unfold R.v38847, N.v38847.
  unfold R.v6, N.v6.
  rewrite ?node_6397.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38848 (s : N.State) (i : N.Inputs) :
  R.v38848 (state s) (inputs i) = Zmod.unsigned (N.v38848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38848 s i)) at 1.
  unfold R.v38848, N.v38848.
  rewrite ?node_38846.
  rewrite ?node_38847.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38849 (s : N.State) (i : N.Inputs) :
  R.v38849 (state s) (inputs i) = Zmod.unsigned (N.v38849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38849 s i)) at 1.
  unfold R.v38849, N.v38849.
  rewrite ?node_38845.
  rewrite ?node_38848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38850 (s : N.State) (i : N.Inputs) :
  R.v38850 (state s) (inputs i) = Zmod.unsigned (N.v38850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38850 s i)) at 1.
  unfold R.v38850, N.v38850.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38851 (s : N.State) (i : N.Inputs) :
  R.v38851 (state s) (inputs i) = Zmod.unsigned (N.v38851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38851 s i)) at 1.
  unfold R.v38851, N.v38851.
  rewrite ?node_6320.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38852 (s : N.State) (i : N.Inputs) :
  R.v38852 (state s) (inputs i) = Zmod.unsigned (N.v38852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38852 s i)) at 1.
  unfold R.v38852, N.v38852.
  unfold R.v6, N.v6.
  rewrite ?node_6316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38853 (s : N.State) (i : N.Inputs) :
  R.v38853 (state s) (inputs i) = Zmod.unsigned (N.v38853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38853 s i)) at 1.
  unfold R.v38853, N.v38853.
  unfold R.v6, N.v6.
  rewrite ?node_6309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38854 (s : N.State) (i : N.Inputs) :
  R.v38854 (state s) (inputs i) = Zmod.unsigned (N.v38854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38854 s i)) at 1.
  unfold R.v38854, N.v38854.
  rewrite ?node_38852.
  rewrite ?node_38853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38855 (s : N.State) (i : N.Inputs) :
  R.v38855 (state s) (inputs i) = Zmod.unsigned (N.v38855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38855 s i)) at 1.
  unfold R.v38855, N.v38855.
  unfold R.v16484, N.v16484.
  rewrite ?node_38854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38856 (s : N.State) (i : N.Inputs) :
  R.v38856 (state s) (inputs i) = Zmod.unsigned (N.v38856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38856 s i)) at 1.
  unfold R.v38856, N.v38856.
  rewrite ?node_38851.
  rewrite ?node_38855.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38857 (s : N.State) (i : N.Inputs) :
  R.v38857 (state s) (inputs i) = Zmod.unsigned (N.v38857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38857 s i)) at 1.
  unfold R.v38857, N.v38857.
  unfold R.v6, N.v6.
  rewrite ?node_38856.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38858 (s : N.State) (i : N.Inputs) :
  R.v38858 (state s) (inputs i) = Zmod.unsigned (N.v38858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38858 s i)) at 1.
  unfold R.v38858, N.v38858.
  rewrite ?node_6321.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38859 (s : N.State) (i : N.Inputs) :
  R.v38859 (state s) (inputs i) = Zmod.unsigned (N.v38859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38859 s i)) at 1.
  unfold R.v38859, N.v38859.
  unfold R.v6, N.v6.
  rewrite ?node_6422.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38860 (s : N.State) (i : N.Inputs) :
  R.v38860 (state s) (inputs i) = Zmod.unsigned (N.v38860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38860 s i)) at 1.
  unfold R.v38860, N.v38860.
  rewrite ?node_38858.
  rewrite ?node_38859.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38861 (s : N.State) (i : N.Inputs) :
  R.v38861 (state s) (inputs i) = Zmod.unsigned (N.v38861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38861 s i)) at 1.
  unfold R.v38861, N.v38861.
  rewrite ?node_38857.
  rewrite ?node_38860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38862 (s : N.State) (i : N.Inputs) :
  R.v38862 (state s) (inputs i) = Zmod.unsigned (N.v38862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38862 s i)) at 1.
  unfold R.v38862, N.v38862.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38863 (s : N.State) (i : N.Inputs) :
  R.v38863 (state s) (inputs i) = Zmod.unsigned (N.v38863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38863 s i)) at 1.
  unfold R.v38863, N.v38863.
  rewrite ?node_6336.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38864 (s : N.State) (i : N.Inputs) :
  R.v38864 (state s) (inputs i) = Zmod.unsigned (N.v38864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38864 s i)) at 1.
  unfold R.v38864, N.v38864.
  rewrite ?node_6332.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38865 (s : N.State) (i : N.Inputs) :
  R.v38865 (state s) (inputs i) = Zmod.unsigned (N.v38865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38865 s i)) at 1.
  unfold R.v38865, N.v38865.
  rewrite ?node_6328.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38866 (s : N.State) (i : N.Inputs) :
  R.v38866 (state s) (inputs i) = Zmod.unsigned (N.v38866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38866 s i)) at 1.
  unfold R.v38866, N.v38866.
  unfold R.v6, N.v6.
  rewrite ?node_6324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38867 (s : N.State) (i : N.Inputs) :
  R.v38867 (state s) (inputs i) = Zmod.unsigned (N.v38867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38867 s i)) at 1.
  unfold R.v38867, N.v38867.
  unfold R.v6, N.v6.
  rewrite !state_r286_nr_5F286.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r286_nr_5F286 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38868 (s : N.State) (i : N.Inputs) :
  R.v38868 (state s) (inputs i) = Zmod.unsigned (N.v38868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38868 s i)) at 1.
  unfold R.v38868, N.v38868.
  rewrite ?node_38866.
  rewrite ?node_38867.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38869 (s : N.State) (i : N.Inputs) :
  R.v38869 (state s) (inputs i) = Zmod.unsigned (N.v38869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38869 s i)) at 1.
  unfold R.v38869, N.v38869.
  unfold R.v16484, N.v16484.
  rewrite ?node_38868.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38870 (s : N.State) (i : N.Inputs) :
  R.v38870 (state s) (inputs i) = Zmod.unsigned (N.v38870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38870 s i)) at 1.
  unfold R.v38870, N.v38870.
  rewrite ?node_38863.
  rewrite ?node_38864.
  rewrite ?node_38865.
  rewrite ?node_38869.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38871 (s : N.State) (i : N.Inputs) :
  R.v38871 (state s) (inputs i) = Zmod.unsigned (N.v38871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38871 s i)) at 1.
  unfold R.v38871, N.v38871.
  unfold R.v6, N.v6.
  rewrite ?node_38870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38872 (s : N.State) (i : N.Inputs) :
  R.v38872 (state s) (inputs i) = Zmod.unsigned (N.v38872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38872 s i)) at 1.
  unfold R.v38872, N.v38872.
  rewrite ?node_6337.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38873 (s : N.State) (i : N.Inputs) :
  R.v38873 (state s) (inputs i) = Zmod.unsigned (N.v38873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38873 s i)) at 1.
  unfold R.v38873, N.v38873.
  unfold R.v6, N.v6.
  rewrite ?node_6413.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38874 (s : N.State) (i : N.Inputs) :
  R.v38874 (state s) (inputs i) = Zmod.unsigned (N.v38874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38874 s i)) at 1.
  unfold R.v38874, N.v38874.
  unfold R.v6, N.v6.
  rewrite ?node_6430.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38875 (s : N.State) (i : N.Inputs) :
  R.v38875 (state s) (inputs i) = Zmod.unsigned (N.v38875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38875 s i)) at 1.
  unfold R.v38875, N.v38875.
  rewrite ?node_38872.
  rewrite ?node_38873.
  rewrite ?node_38874.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38876 (s : N.State) (i : N.Inputs) :
  R.v38876 (state s) (inputs i) = Zmod.unsigned (N.v38876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38876 s i)) at 1.
  unfold R.v38876, N.v38876.
  rewrite ?node_38871.
  rewrite ?node_38875.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38877 (s : N.State) (i : N.Inputs) :
  R.v38877 (state s) (inputs i) = Zmod.unsigned (N.v38877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38877 s i)) at 1.
  unfold R.v38877, N.v38877.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38878 (s : N.State) (i : N.Inputs) :
  R.v38878 (state s) (inputs i) = Zmod.unsigned (N.v38878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38878 s i)) at 1.
  unfold R.v38878, N.v38878.
  rewrite ?node_6328.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38879 (s : N.State) (i : N.Inputs) :
  R.v38879 (state s) (inputs i) = Zmod.unsigned (N.v38879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38879 s i)) at 1.
  unfold R.v38879, N.v38879.
  unfold R.v6, N.v6.
  rewrite ?node_6324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38880 (s : N.State) (i : N.Inputs) :
  R.v38880 (state s) (inputs i) = Zmod.unsigned (N.v38880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38880 s i)) at 1.
  unfold R.v38880, N.v38880.
  unfold R.v6, N.v6.
  rewrite !state_r286_nr_5F286.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r286_nr_5F286 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38881 (s : N.State) (i : N.Inputs) :
  R.v38881 (state s) (inputs i) = Zmod.unsigned (N.v38881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38881 s i)) at 1.
  unfold R.v38881, N.v38881.
  rewrite ?node_38879.
  rewrite ?node_38880.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38882 (s : N.State) (i : N.Inputs) :
  R.v38882 (state s) (inputs i) = Zmod.unsigned (N.v38882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38882 s i)) at 1.
  unfold R.v38882, N.v38882.
  unfold R.v16484, N.v16484.
  rewrite ?node_38881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38883 (s : N.State) (i : N.Inputs) :
  R.v38883 (state s) (inputs i) = Zmod.unsigned (N.v38883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38883 s i)) at 1.
  unfold R.v38883, N.v38883.
  rewrite ?node_38878.
  rewrite ?node_38882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38884 (s : N.State) (i : N.Inputs) :
  R.v38884 (state s) (inputs i) = Zmod.unsigned (N.v38884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38884 s i)) at 1.
  unfold R.v38884, N.v38884.
  unfold R.v6, N.v6.
  rewrite ?node_38883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38885 (s : N.State) (i : N.Inputs) :
  R.v38885 (state s) (inputs i) = Zmod.unsigned (N.v38885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38885 s i)) at 1.
  unfold R.v38885, N.v38885.
  rewrite ?node_6329.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38886 (s : N.State) (i : N.Inputs) :
  R.v38886 (state s) (inputs i) = Zmod.unsigned (N.v38886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38886 s i)) at 1.
  unfold R.v38886, N.v38886.
  unfold R.v6, N.v6.
  rewrite ?node_6413.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38887 (s : N.State) (i : N.Inputs) :
  R.v38887 (state s) (inputs i) = Zmod.unsigned (N.v38887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38887 s i)) at 1.
  unfold R.v38887, N.v38887.
  rewrite ?node_38885.
  rewrite ?node_38886.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38888 (s : N.State) (i : N.Inputs) :
  R.v38888 (state s) (inputs i) = Zmod.unsigned (N.v38888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38888 s i)) at 1.
  unfold R.v38888, N.v38888.
  rewrite ?node_38884.
  rewrite ?node_38887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38889 (s : N.State) (i : N.Inputs) :
  R.v38889 (state s) (inputs i) = Zmod.unsigned (N.v38889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38889 s i)) at 1.
  unfold R.v38889, N.v38889.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38890 (s : N.State) (i : N.Inputs) :
  R.v38890 (state s) (inputs i) = Zmod.unsigned (N.v38890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38890 s i)) at 1.
  unfold R.v38890, N.v38890.
  rewrite ?node_6336.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38891 (s : N.State) (i : N.Inputs) :
  R.v38891 (state s) (inputs i) = Zmod.unsigned (N.v38891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38891 s i)) at 1.
  unfold R.v38891, N.v38891.
  unfold R.v6, N.v6.
  rewrite ?node_6332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38892 (s : N.State) (i : N.Inputs) :
  R.v38892 (state s) (inputs i) = Zmod.unsigned (N.v38892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38892 s i)) at 1.
  unfold R.v38892, N.v38892.
  unfold R.v6, N.v6.
  rewrite ?node_6329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38893 (s : N.State) (i : N.Inputs) :
  R.v38893 (state s) (inputs i) = Zmod.unsigned (N.v38893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38893 s i)) at 1.
  unfold R.v38893, N.v38893.
  rewrite ?node_38891.
  rewrite ?node_38892.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38894 (s : N.State) (i : N.Inputs) :
  R.v38894 (state s) (inputs i) = Zmod.unsigned (N.v38894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38894 s i)) at 1.
  unfold R.v38894, N.v38894.
  unfold R.v16484, N.v16484.
  rewrite ?node_38893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38895 (s : N.State) (i : N.Inputs) :
  R.v38895 (state s) (inputs i) = Zmod.unsigned (N.v38895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38895 s i)) at 1.
  unfold R.v38895, N.v38895.
  rewrite ?node_38890.
  rewrite ?node_38894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38896 (s : N.State) (i : N.Inputs) :
  R.v38896 (state s) (inputs i) = Zmod.unsigned (N.v38896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38896 s i)) at 1.
  unfold R.v38896, N.v38896.
  unfold R.v6, N.v6.
  rewrite ?node_38895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38897 (s : N.State) (i : N.Inputs) :
  R.v38897 (state s) (inputs i) = Zmod.unsigned (N.v38897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38897 s i)) at 1.
  unfold R.v38897, N.v38897.
  rewrite ?node_6337.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38898 (s : N.State) (i : N.Inputs) :
  R.v38898 (state s) (inputs i) = Zmod.unsigned (N.v38898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38898 s i)) at 1.
  unfold R.v38898, N.v38898.
  unfold R.v6, N.v6.
  rewrite ?node_6430.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38899 (s : N.State) (i : N.Inputs) :
  R.v38899 (state s) (inputs i) = Zmod.unsigned (N.v38899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38899 s i)) at 1.
  unfold R.v38899, N.v38899.
  rewrite ?node_38897.
  rewrite ?node_38898.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38900 (s : N.State) (i : N.Inputs) :
  R.v38900 (state s) (inputs i) = Zmod.unsigned (N.v38900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38900 s i)) at 1.
  unfold R.v38900, N.v38900.
  rewrite ?node_38896.
  rewrite ?node_38899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38901 (s : N.State) (i : N.Inputs) :
  R.v38901 (state s) (inputs i) = Zmod.unsigned (N.v38901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38901 s i)) at 1.
  unfold R.v38901, N.v38901.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38902 (s : N.State) (i : N.Inputs) :
  R.v38902 (state s) (inputs i) = Zmod.unsigned (N.v38902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38902 s i)) at 1.
  unfold R.v38902, N.v38902.
  rewrite ?node_6397.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38903 (s : N.State) (i : N.Inputs) :
  R.v38903 (state s) (inputs i) = Zmod.unsigned (N.v38903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38903 s i)) at 1.
  unfold R.v38903, N.v38903.
  rewrite ?node_6393.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38904 (s : N.State) (i : N.Inputs) :
  R.v38904 (state s) (inputs i) = Zmod.unsigned (N.v38904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38904 s i)) at 1.
  unfold R.v38904, N.v38904.
  rewrite ?node_6385.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38905 (s : N.State) (i : N.Inputs) :
  R.v38905 (state s) (inputs i) = Zmod.unsigned (N.v38905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38905 s i)) at 1.
  unfold R.v38905, N.v38905.
  unfold R.v6, N.v6.
  rewrite ?node_6377.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38906 (s : N.State) (i : N.Inputs) :
  R.v38906 (state s) (inputs i) = Zmod.unsigned (N.v38906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38906 s i)) at 1.
  unfold R.v38906, N.v38906.
  unfold R.v6, N.v6.
  rewrite ?node_6370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38907 (s : N.State) (i : N.Inputs) :
  R.v38907 (state s) (inputs i) = Zmod.unsigned (N.v38907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38907 s i)) at 1.
  unfold R.v38907, N.v38907.
  rewrite ?node_38905.
  rewrite ?node_38906.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38908 (s : N.State) (i : N.Inputs) :
  R.v38908 (state s) (inputs i) = Zmod.unsigned (N.v38908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38908 s i)) at 1.
  unfold R.v38908, N.v38908.
  unfold R.v16484, N.v16484.
  rewrite ?node_38907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38909 (s : N.State) (i : N.Inputs) :
  R.v38909 (state s) (inputs i) = Zmod.unsigned (N.v38909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38909 s i)) at 1.
  unfold R.v38909, N.v38909.
  rewrite ?node_38902.
  rewrite ?node_38903.
  rewrite ?node_38904.
  rewrite ?node_38908.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38910 (s : N.State) (i : N.Inputs) :
  R.v38910 (state s) (inputs i) = Zmod.unsigned (N.v38910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38910 s i)) at 1.
  unfold R.v38910, N.v38910.
  unfold R.v6, N.v6.
  rewrite ?node_38909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38911 (s : N.State) (i : N.Inputs) :
  R.v38911 (state s) (inputs i) = Zmod.unsigned (N.v38911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38911 s i)) at 1.
  unfold R.v38911, N.v38911.
  rewrite ?node_6398.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38912 (s : N.State) (i : N.Inputs) :
  R.v38912 (state s) (inputs i) = Zmod.unsigned (N.v38912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38912 s i)) at 1.
  unfold R.v38912, N.v38912.
  unfold R.v6, N.v6.
  rewrite ?node_6476.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38913 (s : N.State) (i : N.Inputs) :
  R.v38913 (state s) (inputs i) = Zmod.unsigned (N.v38913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38913 s i)) at 1.
  unfold R.v38913, N.v38913.
  unfold R.v6, N.v6.
  rewrite ?node_6502.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38914 (s : N.State) (i : N.Inputs) :
  R.v38914 (state s) (inputs i) = Zmod.unsigned (N.v38914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38914 s i)) at 1.
  unfold R.v38914, N.v38914.
  rewrite ?node_38911.
  rewrite ?node_38912.
  rewrite ?node_38913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38915 (s : N.State) (i : N.Inputs) :
  R.v38915 (state s) (inputs i) = Zmod.unsigned (N.v38915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38915 s i)) at 1.
  unfold R.v38915, N.v38915.
  rewrite ?node_38910.
  rewrite ?node_38914.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38916 (s : N.State) (i : N.Inputs) :
  R.v38916 (state s) (inputs i) = Zmod.unsigned (N.v38916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38916 s i)) at 1.
  unfold R.v38916, N.v38916.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38917 (s : N.State) (i : N.Inputs) :
  R.v38917 (state s) (inputs i) = Zmod.unsigned (N.v38917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38917 s i)) at 1.
  unfold R.v38917, N.v38917.
  rewrite ?node_6385.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38918 (s : N.State) (i : N.Inputs) :
  R.v38918 (state s) (inputs i) = Zmod.unsigned (N.v38918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38918 s i)) at 1.
  unfold R.v38918, N.v38918.
  unfold R.v6, N.v6.
  rewrite ?node_6377.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38919 (s : N.State) (i : N.Inputs) :
  R.v38919 (state s) (inputs i) = Zmod.unsigned (N.v38919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38919 s i)) at 1.
  unfold R.v38919, N.v38919.
  unfold R.v6, N.v6.
  rewrite ?node_6370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38920 (s : N.State) (i : N.Inputs) :
  R.v38920 (state s) (inputs i) = Zmod.unsigned (N.v38920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38920 s i)) at 1.
  unfold R.v38920, N.v38920.
  rewrite ?node_38918.
  rewrite ?node_38919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38921 (s : N.State) (i : N.Inputs) :
  R.v38921 (state s) (inputs i) = Zmod.unsigned (N.v38921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38921 s i)) at 1.
  unfold R.v38921, N.v38921.
  unfold R.v16484, N.v16484.
  rewrite ?node_38920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38922 (s : N.State) (i : N.Inputs) :
  R.v38922 (state s) (inputs i) = Zmod.unsigned (N.v38922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38922 s i)) at 1.
  unfold R.v38922, N.v38922.
  rewrite ?node_38917.
  rewrite ?node_38921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38923 (s : N.State) (i : N.Inputs) :
  R.v38923 (state s) (inputs i) = Zmod.unsigned (N.v38923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38923 s i)) at 1.
  unfold R.v38923, N.v38923.
  unfold R.v6, N.v6.
  rewrite ?node_38922.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38924 (s : N.State) (i : N.Inputs) :
  R.v38924 (state s) (inputs i) = Zmod.unsigned (N.v38924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38924 s i)) at 1.
  unfold R.v38924, N.v38924.
  rewrite ?node_6386.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38925 (s : N.State) (i : N.Inputs) :
  R.v38925 (state s) (inputs i) = Zmod.unsigned (N.v38925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38925 s i)) at 1.
  unfold R.v38925, N.v38925.
  unfold R.v6, N.v6.
  rewrite ?node_6476.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38926 (s : N.State) (i : N.Inputs) :
  R.v38926 (state s) (inputs i) = Zmod.unsigned (N.v38926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38926 s i)) at 1.
  unfold R.v38926, N.v38926.
  rewrite ?node_38924.
  rewrite ?node_38925.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38927 (s : N.State) (i : N.Inputs) :
  R.v38927 (state s) (inputs i) = Zmod.unsigned (N.v38927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38927 s i)) at 1.
  unfold R.v38927, N.v38927.
  rewrite ?node_38923.
  rewrite ?node_38926.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38928 (s : N.State) (i : N.Inputs) :
  R.v38928 (state s) (inputs i) = Zmod.unsigned (N.v38928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38928 s i)) at 1.
  unfold R.v38928, N.v38928.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38929 (s : N.State) (i : N.Inputs) :
  R.v38929 (state s) (inputs i) = Zmod.unsigned (N.v38929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38929 s i)) at 1.
  unfold R.v38929, N.v38929.
  rewrite ?node_6397.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38930 (s : N.State) (i : N.Inputs) :
  R.v38930 (state s) (inputs i) = Zmod.unsigned (N.v38930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38930 s i)) at 1.
  unfold R.v38930, N.v38930.
  unfold R.v6, N.v6.
  rewrite ?node_6393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38931 (s : N.State) (i : N.Inputs) :
  R.v38931 (state s) (inputs i) = Zmod.unsigned (N.v38931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38931 s i)) at 1.
  unfold R.v38931, N.v38931.
  unfold R.v6, N.v6.
  rewrite ?node_6386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38932 (s : N.State) (i : N.Inputs) :
  R.v38932 (state s) (inputs i) = Zmod.unsigned (N.v38932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38932 s i)) at 1.
  unfold R.v38932, N.v38932.
  rewrite ?node_38930.
  rewrite ?node_38931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38933 (s : N.State) (i : N.Inputs) :
  R.v38933 (state s) (inputs i) = Zmod.unsigned (N.v38933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38933 s i)) at 1.
  unfold R.v38933, N.v38933.
  unfold R.v16484, N.v16484.
  rewrite ?node_38932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38934 (s : N.State) (i : N.Inputs) :
  R.v38934 (state s) (inputs i) = Zmod.unsigned (N.v38934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38934 s i)) at 1.
  unfold R.v38934, N.v38934.
  rewrite ?node_38929.
  rewrite ?node_38933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38935 (s : N.State) (i : N.Inputs) :
  R.v38935 (state s) (inputs i) = Zmod.unsigned (N.v38935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38935 s i)) at 1.
  unfold R.v38935, N.v38935.
  unfold R.v6, N.v6.
  rewrite ?node_38934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38936 (s : N.State) (i : N.Inputs) :
  R.v38936 (state s) (inputs i) = Zmod.unsigned (N.v38936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38936 s i)) at 1.
  unfold R.v38936, N.v38936.
  rewrite ?node_6398.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38937 (s : N.State) (i : N.Inputs) :
  R.v38937 (state s) (inputs i) = Zmod.unsigned (N.v38937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38937 s i)) at 1.
  unfold R.v38937, N.v38937.
  unfold R.v6, N.v6.
  rewrite ?node_6502.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38938 (s : N.State) (i : N.Inputs) :
  R.v38938 (state s) (inputs i) = Zmod.unsigned (N.v38938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38938 s i)) at 1.
  unfold R.v38938, N.v38938.
  rewrite ?node_38936.
  rewrite ?node_38937.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38939 (s : N.State) (i : N.Inputs) :
  R.v38939 (state s) (inputs i) = Zmod.unsigned (N.v38939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38939 s i)) at 1.
  unfold R.v38939, N.v38939.
  rewrite ?node_38935.
  rewrite ?node_38938.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38940 (s : N.State) (i : N.Inputs) :
  R.v38940 (state s) (inputs i) = Zmod.unsigned (N.v38940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38940 s i)) at 1.
  unfold R.v38940, N.v38940.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38941 (s : N.State) (i : N.Inputs) :
  R.v38941 (state s) (inputs i) = Zmod.unsigned (N.v38941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38941 s i)) at 1.
  unfold R.v38941, N.v38941.
  rewrite ?node_6413.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38942 (s : N.State) (i : N.Inputs) :
  R.v38942 (state s) (inputs i) = Zmod.unsigned (N.v38942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38942 s i)) at 1.
  unfold R.v38942, N.v38942.
  rewrite ?node_6409.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38943 (s : N.State) (i : N.Inputs) :
  R.v38943 (state s) (inputs i) = Zmod.unsigned (N.v38943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38943 s i)) at 1.
  unfold R.v38943, N.v38943.
  rewrite ?node_6405.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38944 (s : N.State) (i : N.Inputs) :
  R.v38944 (state s) (inputs i) = Zmod.unsigned (N.v38944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38944 s i)) at 1.
  unfold R.v38944, N.v38944.
  unfold R.v6, N.v6.
  rewrite ?node_6401.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38945 (s : N.State) (i : N.Inputs) :
  R.v38945 (state s) (inputs i) = Zmod.unsigned (N.v38945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38945 s i)) at 1.
  unfold R.v38945, N.v38945.
  unfold R.v6, N.v6.
  rewrite !state_r303_nr_5F303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r303_nr_5F303 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38946 (s : N.State) (i : N.Inputs) :
  R.v38946 (state s) (inputs i) = Zmod.unsigned (N.v38946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38946 s i)) at 1.
  unfold R.v38946, N.v38946.
  rewrite ?node_38944.
  rewrite ?node_38945.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38947 (s : N.State) (i : N.Inputs) :
  R.v38947 (state s) (inputs i) = Zmod.unsigned (N.v38947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38947 s i)) at 1.
  unfold R.v38947, N.v38947.
  unfold R.v16484, N.v16484.
  rewrite ?node_38946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38948 (s : N.State) (i : N.Inputs) :
  R.v38948 (state s) (inputs i) = Zmod.unsigned (N.v38948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38948 s i)) at 1.
  unfold R.v38948, N.v38948.
  rewrite ?node_38941.
  rewrite ?node_38942.
  rewrite ?node_38943.
  rewrite ?node_38947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38949 (s : N.State) (i : N.Inputs) :
  R.v38949 (state s) (inputs i) = Zmod.unsigned (N.v38949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38949 s i)) at 1.
  unfold R.v38949, N.v38949.
  unfold R.v6, N.v6.
  rewrite ?node_38948.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38950 (s : N.State) (i : N.Inputs) :
  R.v38950 (state s) (inputs i) = Zmod.unsigned (N.v38950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38950 s i)) at 1.
  unfold R.v38950, N.v38950.
  rewrite ?node_6414.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38951 (s : N.State) (i : N.Inputs) :
  R.v38951 (state s) (inputs i) = Zmod.unsigned (N.v38951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38951 s i)) at 1.
  unfold R.v38951, N.v38951.
  unfold R.v6, N.v6.
  rewrite ?node_6493.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38952 (s : N.State) (i : N.Inputs) :
  R.v38952 (state s) (inputs i) = Zmod.unsigned (N.v38952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38952 s i)) at 1.
  unfold R.v38952, N.v38952.
  unfold R.v6, N.v6.
  rewrite ?node_6510.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38953 (s : N.State) (i : N.Inputs) :
  R.v38953 (state s) (inputs i) = Zmod.unsigned (N.v38953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38953 s i)) at 1.
  unfold R.v38953, N.v38953.
  rewrite ?node_38950.
  rewrite ?node_38951.
  rewrite ?node_38952.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38954 (s : N.State) (i : N.Inputs) :
  R.v38954 (state s) (inputs i) = Zmod.unsigned (N.v38954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38954 s i)) at 1.
  unfold R.v38954, N.v38954.
  rewrite ?node_38949.
  rewrite ?node_38953.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38955 (s : N.State) (i : N.Inputs) :
  R.v38955 (state s) (inputs i) = Zmod.unsigned (N.v38955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38955 s i)) at 1.
  unfold R.v38955, N.v38955.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38956 (s : N.State) (i : N.Inputs) :
  R.v38956 (state s) (inputs i) = Zmod.unsigned (N.v38956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38956 s i)) at 1.
  unfold R.v38956, N.v38956.
  rewrite ?node_6405.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38957 (s : N.State) (i : N.Inputs) :
  R.v38957 (state s) (inputs i) = Zmod.unsigned (N.v38957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38957 s i)) at 1.
  unfold R.v38957, N.v38957.
  unfold R.v6, N.v6.
  rewrite ?node_6401.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38958 (s : N.State) (i : N.Inputs) :
  R.v38958 (state s) (inputs i) = Zmod.unsigned (N.v38958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38958 s i)) at 1.
  unfold R.v38958, N.v38958.
  unfold R.v6, N.v6.
  rewrite !state_r303_nr_5F303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r303_nr_5F303 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38959 (s : N.State) (i : N.Inputs) :
  R.v38959 (state s) (inputs i) = Zmod.unsigned (N.v38959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38959 s i)) at 1.
  unfold R.v38959, N.v38959.
  rewrite ?node_38957.
  rewrite ?node_38958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38960 (s : N.State) (i : N.Inputs) :
  R.v38960 (state s) (inputs i) = Zmod.unsigned (N.v38960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38960 s i)) at 1.
  unfold R.v38960, N.v38960.
  unfold R.v16484, N.v16484.
  rewrite ?node_38959.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38961 (s : N.State) (i : N.Inputs) :
  R.v38961 (state s) (inputs i) = Zmod.unsigned (N.v38961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38961 s i)) at 1.
  unfold R.v38961, N.v38961.
  rewrite ?node_38956.
  rewrite ?node_38960.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38962 (s : N.State) (i : N.Inputs) :
  R.v38962 (state s) (inputs i) = Zmod.unsigned (N.v38962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38962 s i)) at 1.
  unfold R.v38962, N.v38962.
  unfold R.v6, N.v6.
  rewrite ?node_38961.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38963 (s : N.State) (i : N.Inputs) :
  R.v38963 (state s) (inputs i) = Zmod.unsigned (N.v38963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38963 s i)) at 1.
  unfold R.v38963, N.v38963.
  rewrite ?node_6406.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38964 (s : N.State) (i : N.Inputs) :
  R.v38964 (state s) (inputs i) = Zmod.unsigned (N.v38964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38964 s i)) at 1.
  unfold R.v38964, N.v38964.
  unfold R.v6, N.v6.
  rewrite ?node_6493.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38965 (s : N.State) (i : N.Inputs) :
  R.v38965 (state s) (inputs i) = Zmod.unsigned (N.v38965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38965 s i)) at 1.
  unfold R.v38965, N.v38965.
  rewrite ?node_38963.
  rewrite ?node_38964.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38966 (s : N.State) (i : N.Inputs) :
  R.v38966 (state s) (inputs i) = Zmod.unsigned (N.v38966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38966 s i)) at 1.
  unfold R.v38966, N.v38966.
  rewrite ?node_38962.
  rewrite ?node_38965.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38967 (s : N.State) (i : N.Inputs) :
  R.v38967 (state s) (inputs i) = Zmod.unsigned (N.v38967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38967 s i)) at 1.
  unfold R.v38967, N.v38967.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38968 (s : N.State) (i : N.Inputs) :
  R.v38968 (state s) (inputs i) = Zmod.unsigned (N.v38968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38968 s i)) at 1.
  unfold R.v38968, N.v38968.
  rewrite ?node_6413.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38969 (s : N.State) (i : N.Inputs) :
  R.v38969 (state s) (inputs i) = Zmod.unsigned (N.v38969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38969 s i)) at 1.
  unfold R.v38969, N.v38969.
  unfold R.v6, N.v6.
  rewrite ?node_6409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38970 (s : N.State) (i : N.Inputs) :
  R.v38970 (state s) (inputs i) = Zmod.unsigned (N.v38970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38970 s i)) at 1.
  unfold R.v38970, N.v38970.
  unfold R.v6, N.v6.
  rewrite ?node_6406.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38971 (s : N.State) (i : N.Inputs) :
  R.v38971 (state s) (inputs i) = Zmod.unsigned (N.v38971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38971 s i)) at 1.
  unfold R.v38971, N.v38971.
  rewrite ?node_38969.
  rewrite ?node_38970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38972 (s : N.State) (i : N.Inputs) :
  R.v38972 (state s) (inputs i) = Zmod.unsigned (N.v38972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38972 s i)) at 1.
  unfold R.v38972, N.v38972.
  unfold R.v16484, N.v16484.
  rewrite ?node_38971.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38973 (s : N.State) (i : N.Inputs) :
  R.v38973 (state s) (inputs i) = Zmod.unsigned (N.v38973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38973 s i)) at 1.
  unfold R.v38973, N.v38973.
  rewrite ?node_38968.
  rewrite ?node_38972.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38974 (s : N.State) (i : N.Inputs) :
  R.v38974 (state s) (inputs i) = Zmod.unsigned (N.v38974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38974 s i)) at 1.
  unfold R.v38974, N.v38974.
  unfold R.v6, N.v6.
  rewrite ?node_38973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38975 (s : N.State) (i : N.Inputs) :
  R.v38975 (state s) (inputs i) = Zmod.unsigned (N.v38975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38975 s i)) at 1.
  unfold R.v38975, N.v38975.
  rewrite ?node_6414.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38976 (s : N.State) (i : N.Inputs) :
  R.v38976 (state s) (inputs i) = Zmod.unsigned (N.v38976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38976 s i)) at 1.
  unfold R.v38976, N.v38976.
  unfold R.v6, N.v6.
  rewrite ?node_6510.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38977 (s : N.State) (i : N.Inputs) :
  R.v38977 (state s) (inputs i) = Zmod.unsigned (N.v38977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38977 s i)) at 1.
  unfold R.v38977, N.v38977.
  rewrite ?node_38975.
  rewrite ?node_38976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38978 (s : N.State) (i : N.Inputs) :
  R.v38978 (state s) (inputs i) = Zmod.unsigned (N.v38978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38978 s i)) at 1.
  unfold R.v38978, N.v38978.
  rewrite ?node_38974.
  rewrite ?node_38977.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38979 (s : N.State) (i : N.Inputs) :
  R.v38979 (state s) (inputs i) = Zmod.unsigned (N.v38979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38979 s i)) at 1.
  unfold R.v38979, N.v38979.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38980 (s : N.State) (i : N.Inputs) :
  R.v38980 (state s) (inputs i) = Zmod.unsigned (N.v38980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38980 s i)) at 1.
  unfold R.v38980, N.v38980.
  rewrite ?node_6476.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38981 (s : N.State) (i : N.Inputs) :
  R.v38981 (state s) (inputs i) = Zmod.unsigned (N.v38981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38981 s i)) at 1.
  unfold R.v38981, N.v38981.
  rewrite ?node_6472.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38982 (s : N.State) (i : N.Inputs) :
  R.v38982 (state s) (inputs i) = Zmod.unsigned (N.v38982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38982 s i)) at 1.
  unfold R.v38982, N.v38982.
  rewrite ?node_6464.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38983 (s : N.State) (i : N.Inputs) :
  R.v38983 (state s) (inputs i) = Zmod.unsigned (N.v38983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38983 s i)) at 1.
  unfold R.v38983, N.v38983.
  unfold R.v6, N.v6.
  rewrite ?node_6456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38984 (s : N.State) (i : N.Inputs) :
  R.v38984 (state s) (inputs i) = Zmod.unsigned (N.v38984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38984 s i)) at 1.
  unfold R.v38984, N.v38984.
  unfold R.v6, N.v6.
  rewrite ?node_6449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38985 (s : N.State) (i : N.Inputs) :
  R.v38985 (state s) (inputs i) = Zmod.unsigned (N.v38985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38985 s i)) at 1.
  unfold R.v38985, N.v38985.
  rewrite ?node_38983.
  rewrite ?node_38984.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38986 (s : N.State) (i : N.Inputs) :
  R.v38986 (state s) (inputs i) = Zmod.unsigned (N.v38986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38986 s i)) at 1.
  unfold R.v38986, N.v38986.
  unfold R.v16484, N.v16484.
  rewrite ?node_38985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38987 (s : N.State) (i : N.Inputs) :
  R.v38987 (state s) (inputs i) = Zmod.unsigned (N.v38987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38987 s i)) at 1.
  unfold R.v38987, N.v38987.
  rewrite ?node_38980.
  rewrite ?node_38981.
  rewrite ?node_38982.
  rewrite ?node_38986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38988 (s : N.State) (i : N.Inputs) :
  R.v38988 (state s) (inputs i) = Zmod.unsigned (N.v38988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38988 s i)) at 1.
  unfold R.v38988, N.v38988.
  unfold R.v6, N.v6.
  rewrite ?node_38987.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38989 (s : N.State) (i : N.Inputs) :
  R.v38989 (state s) (inputs i) = Zmod.unsigned (N.v38989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38989 s i)) at 1.
  unfold R.v38989, N.v38989.
  rewrite ?node_6477.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38990 (s : N.State) (i : N.Inputs) :
  R.v38990 (state s) (inputs i) = Zmod.unsigned (N.v38990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38990 s i)) at 1.
  unfold R.v38990, N.v38990.
  unfold R.v6, N.v6.
  rewrite ?node_6556.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38991 (s : N.State) (i : N.Inputs) :
  R.v38991 (state s) (inputs i) = Zmod.unsigned (N.v38991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38991 s i)) at 1.
  unfold R.v38991, N.v38991.
  unfold R.v6, N.v6.
  rewrite ?node_6584.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38992 (s : N.State) (i : N.Inputs) :
  R.v38992 (state s) (inputs i) = Zmod.unsigned (N.v38992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38992 s i)) at 1.
  unfold R.v38992, N.v38992.
  rewrite ?node_38989.
  rewrite ?node_38990.
  rewrite ?node_38991.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38993 (s : N.State) (i : N.Inputs) :
  R.v38993 (state s) (inputs i) = Zmod.unsigned (N.v38993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38993 s i)) at 1.
  unfold R.v38993, N.v38993.
  rewrite ?node_38988.
  rewrite ?node_38992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38994 (s : N.State) (i : N.Inputs) :
  R.v38994 (state s) (inputs i) = Zmod.unsigned (N.v38994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38994 s i)) at 1.
  unfold R.v38994, N.v38994.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38995 (s : N.State) (i : N.Inputs) :
  R.v38995 (state s) (inputs i) = Zmod.unsigned (N.v38995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38995 s i)) at 1.
  unfold R.v38995, N.v38995.
  rewrite ?node_6464.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38996 (s : N.State) (i : N.Inputs) :
  R.v38996 (state s) (inputs i) = Zmod.unsigned (N.v38996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38996 s i)) at 1.
  unfold R.v38996, N.v38996.
  unfold R.v6, N.v6.
  rewrite ?node_6456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38997 (s : N.State) (i : N.Inputs) :
  R.v38997 (state s) (inputs i) = Zmod.unsigned (N.v38997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38997 s i)) at 1.
  unfold R.v38997, N.v38997.
  unfold R.v6, N.v6.
  rewrite ?node_6449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38998 (s : N.State) (i : N.Inputs) :
  R.v38998 (state s) (inputs i) = Zmod.unsigned (N.v38998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38998 s i)) at 1.
  unfold R.v38998, N.v38998.
  rewrite ?node_38996.
  rewrite ?node_38997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38999 (s : N.State) (i : N.Inputs) :
  R.v38999 (state s) (inputs i) = Zmod.unsigned (N.v38999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38999 s i)) at 1.
  unfold R.v38999, N.v38999.
  unfold R.v16484, N.v16484.
  rewrite ?node_38998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
