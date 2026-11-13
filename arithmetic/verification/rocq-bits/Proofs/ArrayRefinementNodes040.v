(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes039.
Lemma node_40000 (s : N.State) (i : N.Inputs) :
  R.v40000 (state s) (inputs i) = Zmod.unsigned (N.v40000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40000 s i)) at 1.
  unfold R.v40000, N.v40000.
  rewrite ?node_39993.
  rewrite ?node_39994.
  rewrite ?node_39995.
  rewrite ?node_39999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40001 (s : N.State) (i : N.Inputs) :
  R.v40001 (state s) (inputs i) = Zmod.unsigned (N.v40001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40001 s i)) at 1.
  unfold R.v40001, N.v40001.
  unfold R.v6, N.v6.
  rewrite ?node_40000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40002 (s : N.State) (i : N.Inputs) :
  R.v40002 (state s) (inputs i) = Zmod.unsigned (N.v40002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40002 s i)) at 1.
  unfold R.v40002, N.v40002.
  rewrite ?node_7514.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40003 (s : N.State) (i : N.Inputs) :
  R.v40003 (state s) (inputs i) = Zmod.unsigned (N.v40003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40003 s i)) at 1.
  unfold R.v40003, N.v40003.
  unfold R.v6, N.v6.
  rewrite ?node_7624.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40004 (s : N.State) (i : N.Inputs) :
  R.v40004 (state s) (inputs i) = Zmod.unsigned (N.v40004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40004 s i)) at 1.
  unfold R.v40004, N.v40004.
  unfold R.v6, N.v6.
  rewrite ?node_7672.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40005 (s : N.State) (i : N.Inputs) :
  R.v40005 (state s) (inputs i) = Zmod.unsigned (N.v40005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40005 s i)) at 1.
  unfold R.v40005, N.v40005.
  rewrite ?node_40002.
  rewrite ?node_40003.
  rewrite ?node_40004.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40006 (s : N.State) (i : N.Inputs) :
  R.v40006 (state s) (inputs i) = Zmod.unsigned (N.v40006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40006 s i)) at 1.
  unfold R.v40006, N.v40006.
  rewrite ?node_40001.
  rewrite ?node_40005.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40007 (s : N.State) (i : N.Inputs) :
  R.v40007 (state s) (inputs i) = Zmod.unsigned (N.v40007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40007 s i)) at 1.
  unfold R.v40007, N.v40007.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40008 (s : N.State) (i : N.Inputs) :
  R.v40008 (state s) (inputs i) = Zmod.unsigned (N.v40008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40008 s i)) at 1.
  unfold R.v40008, N.v40008.
  rewrite ?node_7501.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40009 (s : N.State) (i : N.Inputs) :
  R.v40009 (state s) (inputs i) = Zmod.unsigned (N.v40009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40009 s i)) at 1.
  unfold R.v40009, N.v40009.
  unfold R.v6, N.v6.
  rewrite ?node_7493.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40010 (s : N.State) (i : N.Inputs) :
  R.v40010 (state s) (inputs i) = Zmod.unsigned (N.v40010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40010 s i)) at 1.
  unfold R.v40010, N.v40010.
  unfold R.v6, N.v6.
  rewrite ?node_7486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40011 (s : N.State) (i : N.Inputs) :
  R.v40011 (state s) (inputs i) = Zmod.unsigned (N.v40011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40011 s i)) at 1.
  unfold R.v40011, N.v40011.
  rewrite ?node_40009.
  rewrite ?node_40010.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40012 (s : N.State) (i : N.Inputs) :
  R.v40012 (state s) (inputs i) = Zmod.unsigned (N.v40012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40012 s i)) at 1.
  unfold R.v40012, N.v40012.
  unfold R.v16484, N.v16484.
  rewrite ?node_40011.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40013 (s : N.State) (i : N.Inputs) :
  R.v40013 (state s) (inputs i) = Zmod.unsigned (N.v40013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40013 s i)) at 1.
  unfold R.v40013, N.v40013.
  rewrite ?node_40008.
  rewrite ?node_40012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40014 (s : N.State) (i : N.Inputs) :
  R.v40014 (state s) (inputs i) = Zmod.unsigned (N.v40014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40014 s i)) at 1.
  unfold R.v40014, N.v40014.
  unfold R.v6, N.v6.
  rewrite ?node_40013.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40015 (s : N.State) (i : N.Inputs) :
  R.v40015 (state s) (inputs i) = Zmod.unsigned (N.v40015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40015 s i)) at 1.
  unfold R.v40015, N.v40015.
  rewrite ?node_7502.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40016 (s : N.State) (i : N.Inputs) :
  R.v40016 (state s) (inputs i) = Zmod.unsigned (N.v40016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40016 s i)) at 1.
  unfold R.v40016, N.v40016.
  unfold R.v6, N.v6.
  rewrite ?node_7624.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40017 (s : N.State) (i : N.Inputs) :
  R.v40017 (state s) (inputs i) = Zmod.unsigned (N.v40017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40017 s i)) at 1.
  unfold R.v40017, N.v40017.
  rewrite ?node_40015.
  rewrite ?node_40016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40018 (s : N.State) (i : N.Inputs) :
  R.v40018 (state s) (inputs i) = Zmod.unsigned (N.v40018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40018 s i)) at 1.
  unfold R.v40018, N.v40018.
  rewrite ?node_40014.
  rewrite ?node_40017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40019 (s : N.State) (i : N.Inputs) :
  R.v40019 (state s) (inputs i) = Zmod.unsigned (N.v40019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40019 s i)) at 1.
  unfold R.v40019, N.v40019.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40020 (s : N.State) (i : N.Inputs) :
  R.v40020 (state s) (inputs i) = Zmod.unsigned (N.v40020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40020 s i)) at 1.
  unfold R.v40020, N.v40020.
  rewrite ?node_7513.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40021 (s : N.State) (i : N.Inputs) :
  R.v40021 (state s) (inputs i) = Zmod.unsigned (N.v40021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40021 s i)) at 1.
  unfold R.v40021, N.v40021.
  unfold R.v6, N.v6.
  rewrite ?node_7509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40022 (s : N.State) (i : N.Inputs) :
  R.v40022 (state s) (inputs i) = Zmod.unsigned (N.v40022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40022 s i)) at 1.
  unfold R.v40022, N.v40022.
  unfold R.v6, N.v6.
  rewrite ?node_7502.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40023 (s : N.State) (i : N.Inputs) :
  R.v40023 (state s) (inputs i) = Zmod.unsigned (N.v40023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40023 s i)) at 1.
  unfold R.v40023, N.v40023.
  rewrite ?node_40021.
  rewrite ?node_40022.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40024 (s : N.State) (i : N.Inputs) :
  R.v40024 (state s) (inputs i) = Zmod.unsigned (N.v40024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40024 s i)) at 1.
  unfold R.v40024, N.v40024.
  unfold R.v16484, N.v16484.
  rewrite ?node_40023.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40025 (s : N.State) (i : N.Inputs) :
  R.v40025 (state s) (inputs i) = Zmod.unsigned (N.v40025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40025 s i)) at 1.
  unfold R.v40025, N.v40025.
  rewrite ?node_40020.
  rewrite ?node_40024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40026 (s : N.State) (i : N.Inputs) :
  R.v40026 (state s) (inputs i) = Zmod.unsigned (N.v40026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40026 s i)) at 1.
  unfold R.v40026, N.v40026.
  unfold R.v6, N.v6.
  rewrite ?node_40025.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40027 (s : N.State) (i : N.Inputs) :
  R.v40027 (state s) (inputs i) = Zmod.unsigned (N.v40027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40027 s i)) at 1.
  unfold R.v40027, N.v40027.
  rewrite ?node_7514.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40028 (s : N.State) (i : N.Inputs) :
  R.v40028 (state s) (inputs i) = Zmod.unsigned (N.v40028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40028 s i)) at 1.
  unfold R.v40028, N.v40028.
  unfold R.v6, N.v6.
  rewrite ?node_7672.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40029 (s : N.State) (i : N.Inputs) :
  R.v40029 (state s) (inputs i) = Zmod.unsigned (N.v40029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40029 s i)) at 1.
  unfold R.v40029, N.v40029.
  rewrite ?node_40027.
  rewrite ?node_40028.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40030 (s : N.State) (i : N.Inputs) :
  R.v40030 (state s) (inputs i) = Zmod.unsigned (N.v40030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40030 s i)) at 1.
  unfold R.v40030, N.v40030.
  rewrite ?node_40026.
  rewrite ?node_40029.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40031 (s : N.State) (i : N.Inputs) :
  R.v40031 (state s) (inputs i) = Zmod.unsigned (N.v40031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40031 s i)) at 1.
  unfold R.v40031, N.v40031.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40032 (s : N.State) (i : N.Inputs) :
  R.v40032 (state s) (inputs i) = Zmod.unsigned (N.v40032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40032 s i)) at 1.
  unfold R.v40032, N.v40032.
  rewrite ?node_7535.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40033 (s : N.State) (i : N.Inputs) :
  R.v40033 (state s) (inputs i) = Zmod.unsigned (N.v40033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40033 s i)) at 1.
  unfold R.v40033, N.v40033.
  rewrite ?node_7531.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40034 (s : N.State) (i : N.Inputs) :
  R.v40034 (state s) (inputs i) = Zmod.unsigned (N.v40034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40034 s i)) at 1.
  unfold R.v40034, N.v40034.
  rewrite ?node_7527.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40035 (s : N.State) (i : N.Inputs) :
  R.v40035 (state s) (inputs i) = Zmod.unsigned (N.v40035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40035 s i)) at 1.
  unfold R.v40035, N.v40035.
  unfold R.v6, N.v6.
  rewrite ?node_7523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40036 (s : N.State) (i : N.Inputs) :
  R.v40036 (state s) (inputs i) = Zmod.unsigned (N.v40036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40036 s i)) at 1.
  unfold R.v40036, N.v40036.
  unfold R.v6, N.v6.
  rewrite ?node_7521.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40037 (s : N.State) (i : N.Inputs) :
  R.v40037 (state s) (inputs i) = Zmod.unsigned (N.v40037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40037 s i)) at 1.
  unfold R.v40037, N.v40037.
  rewrite ?node_40035.
  rewrite ?node_40036.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40038 (s : N.State) (i : N.Inputs) :
  R.v40038 (state s) (inputs i) = Zmod.unsigned (N.v40038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40038 s i)) at 1.
  unfold R.v40038, N.v40038.
  unfold R.v16484, N.v16484.
  rewrite ?node_40037.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40039 (s : N.State) (i : N.Inputs) :
  R.v40039 (state s) (inputs i) = Zmod.unsigned (N.v40039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40039 s i)) at 1.
  unfold R.v40039, N.v40039.
  rewrite ?node_40032.
  rewrite ?node_40033.
  rewrite ?node_40034.
  rewrite ?node_40038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40040 (s : N.State) (i : N.Inputs) :
  R.v40040 (state s) (inputs i) = Zmod.unsigned (N.v40040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40040 s i)) at 1.
  unfold R.v40040, N.v40040.
  unfold R.v6, N.v6.
  rewrite ?node_40039.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40041 (s : N.State) (i : N.Inputs) :
  R.v40041 (state s) (inputs i) = Zmod.unsigned (N.v40041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40041 s i)) at 1.
  unfold R.v40041, N.v40041.
  rewrite ?node_7536.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40042 (s : N.State) (i : N.Inputs) :
  R.v40042 (state s) (inputs i) = Zmod.unsigned (N.v40042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40042 s i)) at 1.
  unfold R.v40042, N.v40042.
  unfold R.v6, N.v6.
  rewrite ?node_7647.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40043 (s : N.State) (i : N.Inputs) :
  R.v40043 (state s) (inputs i) = Zmod.unsigned (N.v40043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40043 s i)) at 1.
  unfold R.v40043, N.v40043.
  unfold R.v6, N.v6.
  rewrite ?node_7680.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40044 (s : N.State) (i : N.Inputs) :
  R.v40044 (state s) (inputs i) = Zmod.unsigned (N.v40044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40044 s i)) at 1.
  unfold R.v40044, N.v40044.
  rewrite ?node_40041.
  rewrite ?node_40042.
  rewrite ?node_40043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40045 (s : N.State) (i : N.Inputs) :
  R.v40045 (state s) (inputs i) = Zmod.unsigned (N.v40045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40045 s i)) at 1.
  unfold R.v40045, N.v40045.
  rewrite ?node_40040.
  rewrite ?node_40044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40046 (s : N.State) (i : N.Inputs) :
  R.v40046 (state s) (inputs i) = Zmod.unsigned (N.v40046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40046 s i)) at 1.
  unfold R.v40046, N.v40046.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40047 (s : N.State) (i : N.Inputs) :
  R.v40047 (state s) (inputs i) = Zmod.unsigned (N.v40047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40047 s i)) at 1.
  unfold R.v40047, N.v40047.
  rewrite ?node_7527.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40048 (s : N.State) (i : N.Inputs) :
  R.v40048 (state s) (inputs i) = Zmod.unsigned (N.v40048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40048 s i)) at 1.
  unfold R.v40048, N.v40048.
  unfold R.v6, N.v6.
  rewrite ?node_7523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40049 (s : N.State) (i : N.Inputs) :
  R.v40049 (state s) (inputs i) = Zmod.unsigned (N.v40049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40049 s i)) at 1.
  unfold R.v40049, N.v40049.
  unfold R.v6, N.v6.
  rewrite ?node_7521.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40050 (s : N.State) (i : N.Inputs) :
  R.v40050 (state s) (inputs i) = Zmod.unsigned (N.v40050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40050 s i)) at 1.
  unfold R.v40050, N.v40050.
  rewrite ?node_40048.
  rewrite ?node_40049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40051 (s : N.State) (i : N.Inputs) :
  R.v40051 (state s) (inputs i) = Zmod.unsigned (N.v40051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40051 s i)) at 1.
  unfold R.v40051, N.v40051.
  unfold R.v16484, N.v16484.
  rewrite ?node_40050.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40052 (s : N.State) (i : N.Inputs) :
  R.v40052 (state s) (inputs i) = Zmod.unsigned (N.v40052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40052 s i)) at 1.
  unfold R.v40052, N.v40052.
  rewrite ?node_40047.
  rewrite ?node_40051.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40053 (s : N.State) (i : N.Inputs) :
  R.v40053 (state s) (inputs i) = Zmod.unsigned (N.v40053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40053 s i)) at 1.
  unfold R.v40053, N.v40053.
  unfold R.v6, N.v6.
  rewrite ?node_40052.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40054 (s : N.State) (i : N.Inputs) :
  R.v40054 (state s) (inputs i) = Zmod.unsigned (N.v40054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40054 s i)) at 1.
  unfold R.v40054, N.v40054.
  rewrite ?node_7528.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40055 (s : N.State) (i : N.Inputs) :
  R.v40055 (state s) (inputs i) = Zmod.unsigned (N.v40055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40055 s i)) at 1.
  unfold R.v40055, N.v40055.
  unfold R.v6, N.v6.
  rewrite ?node_7647.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40056 (s : N.State) (i : N.Inputs) :
  R.v40056 (state s) (inputs i) = Zmod.unsigned (N.v40056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40056 s i)) at 1.
  unfold R.v40056, N.v40056.
  rewrite ?node_40054.
  rewrite ?node_40055.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40057 (s : N.State) (i : N.Inputs) :
  R.v40057 (state s) (inputs i) = Zmod.unsigned (N.v40057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40057 s i)) at 1.
  unfold R.v40057, N.v40057.
  rewrite ?node_40053.
  rewrite ?node_40056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40058 (s : N.State) (i : N.Inputs) :
  R.v40058 (state s) (inputs i) = Zmod.unsigned (N.v40058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40058 s i)) at 1.
  unfold R.v40058, N.v40058.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40059 (s : N.State) (i : N.Inputs) :
  R.v40059 (state s) (inputs i) = Zmod.unsigned (N.v40059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40059 s i)) at 1.
  unfold R.v40059, N.v40059.
  rewrite ?node_7535.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40060 (s : N.State) (i : N.Inputs) :
  R.v40060 (state s) (inputs i) = Zmod.unsigned (N.v40060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40060 s i)) at 1.
  unfold R.v40060, N.v40060.
  unfold R.v6, N.v6.
  rewrite ?node_7531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40061 (s : N.State) (i : N.Inputs) :
  R.v40061 (state s) (inputs i) = Zmod.unsigned (N.v40061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40061 s i)) at 1.
  unfold R.v40061, N.v40061.
  unfold R.v6, N.v6.
  rewrite ?node_7528.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40062 (s : N.State) (i : N.Inputs) :
  R.v40062 (state s) (inputs i) = Zmod.unsigned (N.v40062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40062 s i)) at 1.
  unfold R.v40062, N.v40062.
  rewrite ?node_40060.
  rewrite ?node_40061.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40063 (s : N.State) (i : N.Inputs) :
  R.v40063 (state s) (inputs i) = Zmod.unsigned (N.v40063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40063 s i)) at 1.
  unfold R.v40063, N.v40063.
  unfold R.v16484, N.v16484.
  rewrite ?node_40062.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40064 (s : N.State) (i : N.Inputs) :
  R.v40064 (state s) (inputs i) = Zmod.unsigned (N.v40064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40064 s i)) at 1.
  unfold R.v40064, N.v40064.
  rewrite ?node_40059.
  rewrite ?node_40063.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40065 (s : N.State) (i : N.Inputs) :
  R.v40065 (state s) (inputs i) = Zmod.unsigned (N.v40065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40065 s i)) at 1.
  unfold R.v40065, N.v40065.
  unfold R.v6, N.v6.
  rewrite ?node_40064.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40066 (s : N.State) (i : N.Inputs) :
  R.v40066 (state s) (inputs i) = Zmod.unsigned (N.v40066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40066 s i)) at 1.
  unfold R.v40066, N.v40066.
  rewrite ?node_7536.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40067 (s : N.State) (i : N.Inputs) :
  R.v40067 (state s) (inputs i) = Zmod.unsigned (N.v40067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40067 s i)) at 1.
  unfold R.v40067, N.v40067.
  unfold R.v6, N.v6.
  rewrite ?node_7680.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40068 (s : N.State) (i : N.Inputs) :
  R.v40068 (state s) (inputs i) = Zmod.unsigned (N.v40068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40068 s i)) at 1.
  unfold R.v40068, N.v40068.
  rewrite ?node_40066.
  rewrite ?node_40067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40069 (s : N.State) (i : N.Inputs) :
  R.v40069 (state s) (inputs i) = Zmod.unsigned (N.v40069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40069 s i)) at 1.
  unfold R.v40069, N.v40069.
  rewrite ?node_40065.
  rewrite ?node_40068.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40070 (s : N.State) (i : N.Inputs) :
  R.v40070 (state s) (inputs i) = Zmod.unsigned (N.v40070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40070 s i)) at 1.
  unfold R.v40070, N.v40070.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40071 (s : N.State) (i : N.Inputs) :
  R.v40071 (state s) (inputs i) = Zmod.unsigned (N.v40071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40071 s i)) at 1.
  unfold R.v40071, N.v40071.
  rewrite ?node_7555.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40072 (s : N.State) (i : N.Inputs) :
  R.v40072 (state s) (inputs i) = Zmod.unsigned (N.v40072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40072 s i)) at 1.
  unfold R.v40072, N.v40072.
  rewrite ?node_7551.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40073 (s : N.State) (i : N.Inputs) :
  R.v40073 (state s) (inputs i) = Zmod.unsigned (N.v40073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40073 s i)) at 1.
  unfold R.v40073, N.v40073.
  rewrite ?node_7547.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40074 (s : N.State) (i : N.Inputs) :
  R.v40074 (state s) (inputs i) = Zmod.unsigned (N.v40074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40074 s i)) at 1.
  unfold R.v40074, N.v40074.
  unfold R.v6, N.v6.
  rewrite ?node_7543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40075 (s : N.State) (i : N.Inputs) :
  R.v40075 (state s) (inputs i) = Zmod.unsigned (N.v40075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40075 s i)) at 1.
  unfold R.v40075, N.v40075.
  unfold R.v6, N.v6.
  rewrite ?node_7540.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40076 (s : N.State) (i : N.Inputs) :
  R.v40076 (state s) (inputs i) = Zmod.unsigned (N.v40076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40076 s i)) at 1.
  unfold R.v40076, N.v40076.
  rewrite ?node_40074.
  rewrite ?node_40075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40077 (s : N.State) (i : N.Inputs) :
  R.v40077 (state s) (inputs i) = Zmod.unsigned (N.v40077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40077 s i)) at 1.
  unfold R.v40077, N.v40077.
  unfold R.v16484, N.v16484.
  rewrite ?node_40076.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40078 (s : N.State) (i : N.Inputs) :
  R.v40078 (state s) (inputs i) = Zmod.unsigned (N.v40078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40078 s i)) at 1.
  unfold R.v40078, N.v40078.
  rewrite ?node_40071.
  rewrite ?node_40072.
  rewrite ?node_40073.
  rewrite ?node_40077.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40079 (s : N.State) (i : N.Inputs) :
  R.v40079 (state s) (inputs i) = Zmod.unsigned (N.v40079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40079 s i)) at 1.
  unfold R.v40079, N.v40079.
  unfold R.v6, N.v6.
  rewrite ?node_40078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40080 (s : N.State) (i : N.Inputs) :
  R.v40080 (state s) (inputs i) = Zmod.unsigned (N.v40080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40080 s i)) at 1.
  unfold R.v40080, N.v40080.
  rewrite ?node_7556.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40081 (s : N.State) (i : N.Inputs) :
  R.v40081 (state s) (inputs i) = Zmod.unsigned (N.v40081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40081 s i)) at 1.
  unfold R.v40081, N.v40081.
  unfold R.v6, N.v6.
  rewrite ?node_7667.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40082 (s : N.State) (i : N.Inputs) :
  R.v40082 (state s) (inputs i) = Zmod.unsigned (N.v40082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40082 s i)) at 1.
  unfold R.v40082, N.v40082.
  unfold R.v6, N.v6.
  rewrite ?node_7683.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40083 (s : N.State) (i : N.Inputs) :
  R.v40083 (state s) (inputs i) = Zmod.unsigned (N.v40083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40083 s i)) at 1.
  unfold R.v40083, N.v40083.
  rewrite ?node_40080.
  rewrite ?node_40081.
  rewrite ?node_40082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40084 (s : N.State) (i : N.Inputs) :
  R.v40084 (state s) (inputs i) = Zmod.unsigned (N.v40084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40084 s i)) at 1.
  unfold R.v40084, N.v40084.
  rewrite ?node_40079.
  rewrite ?node_40083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40085 (s : N.State) (i : N.Inputs) :
  R.v40085 (state s) (inputs i) = Zmod.unsigned (N.v40085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40085 s i)) at 1.
  unfold R.v40085, N.v40085.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40086 (s : N.State) (i : N.Inputs) :
  R.v40086 (state s) (inputs i) = Zmod.unsigned (N.v40086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40086 s i)) at 1.
  unfold R.v40086, N.v40086.
  rewrite ?node_7547.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40087 (s : N.State) (i : N.Inputs) :
  R.v40087 (state s) (inputs i) = Zmod.unsigned (N.v40087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40087 s i)) at 1.
  unfold R.v40087, N.v40087.
  unfold R.v6, N.v6.
  rewrite ?node_7543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40088 (s : N.State) (i : N.Inputs) :
  R.v40088 (state s) (inputs i) = Zmod.unsigned (N.v40088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40088 s i)) at 1.
  unfold R.v40088, N.v40088.
  unfold R.v6, N.v6.
  rewrite ?node_7540.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40089 (s : N.State) (i : N.Inputs) :
  R.v40089 (state s) (inputs i) = Zmod.unsigned (N.v40089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40089 s i)) at 1.
  unfold R.v40089, N.v40089.
  rewrite ?node_40087.
  rewrite ?node_40088.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40090 (s : N.State) (i : N.Inputs) :
  R.v40090 (state s) (inputs i) = Zmod.unsigned (N.v40090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40090 s i)) at 1.
  unfold R.v40090, N.v40090.
  unfold R.v16484, N.v16484.
  rewrite ?node_40089.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40091 (s : N.State) (i : N.Inputs) :
  R.v40091 (state s) (inputs i) = Zmod.unsigned (N.v40091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40091 s i)) at 1.
  unfold R.v40091, N.v40091.
  rewrite ?node_40086.
  rewrite ?node_40090.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40092 (s : N.State) (i : N.Inputs) :
  R.v40092 (state s) (inputs i) = Zmod.unsigned (N.v40092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40092 s i)) at 1.
  unfold R.v40092, N.v40092.
  unfold R.v6, N.v6.
  rewrite ?node_40091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40093 (s : N.State) (i : N.Inputs) :
  R.v40093 (state s) (inputs i) = Zmod.unsigned (N.v40093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40093 s i)) at 1.
  unfold R.v40093, N.v40093.
  rewrite ?node_7548.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40094 (s : N.State) (i : N.Inputs) :
  R.v40094 (state s) (inputs i) = Zmod.unsigned (N.v40094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40094 s i)) at 1.
  unfold R.v40094, N.v40094.
  unfold R.v6, N.v6.
  rewrite ?node_7667.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40095 (s : N.State) (i : N.Inputs) :
  R.v40095 (state s) (inputs i) = Zmod.unsigned (N.v40095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40095 s i)) at 1.
  unfold R.v40095, N.v40095.
  rewrite ?node_40093.
  rewrite ?node_40094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40096 (s : N.State) (i : N.Inputs) :
  R.v40096 (state s) (inputs i) = Zmod.unsigned (N.v40096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40096 s i)) at 1.
  unfold R.v40096, N.v40096.
  rewrite ?node_40092.
  rewrite ?node_40095.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40097 (s : N.State) (i : N.Inputs) :
  R.v40097 (state s) (inputs i) = Zmod.unsigned (N.v40097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40097 s i)) at 1.
  unfold R.v40097, N.v40097.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40098 (s : N.State) (i : N.Inputs) :
  R.v40098 (state s) (inputs i) = Zmod.unsigned (N.v40098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40098 s i)) at 1.
  unfold R.v40098, N.v40098.
  rewrite ?node_7555.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40099 (s : N.State) (i : N.Inputs) :
  R.v40099 (state s) (inputs i) = Zmod.unsigned (N.v40099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40099 s i)) at 1.
  unfold R.v40099, N.v40099.
  unfold R.v6, N.v6.
  rewrite ?node_7551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40100 (s : N.State) (i : N.Inputs) :
  R.v40100 (state s) (inputs i) = Zmod.unsigned (N.v40100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40100 s i)) at 1.
  unfold R.v40100, N.v40100.
  unfold R.v6, N.v6.
  rewrite ?node_7548.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40101 (s : N.State) (i : N.Inputs) :
  R.v40101 (state s) (inputs i) = Zmod.unsigned (N.v40101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40101 s i)) at 1.
  unfold R.v40101, N.v40101.
  rewrite ?node_40099.
  rewrite ?node_40100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40102 (s : N.State) (i : N.Inputs) :
  R.v40102 (state s) (inputs i) = Zmod.unsigned (N.v40102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40102 s i)) at 1.
  unfold R.v40102, N.v40102.
  unfold R.v16484, N.v16484.
  rewrite ?node_40101.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40103 (s : N.State) (i : N.Inputs) :
  R.v40103 (state s) (inputs i) = Zmod.unsigned (N.v40103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40103 s i)) at 1.
  unfold R.v40103, N.v40103.
  rewrite ?node_40098.
  rewrite ?node_40102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40104 (s : N.State) (i : N.Inputs) :
  R.v40104 (state s) (inputs i) = Zmod.unsigned (N.v40104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40104 s i)) at 1.
  unfold R.v40104, N.v40104.
  unfold R.v6, N.v6.
  rewrite ?node_40103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40105 (s : N.State) (i : N.Inputs) :
  R.v40105 (state s) (inputs i) = Zmod.unsigned (N.v40105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40105 s i)) at 1.
  unfold R.v40105, N.v40105.
  rewrite ?node_7556.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40106 (s : N.State) (i : N.Inputs) :
  R.v40106 (state s) (inputs i) = Zmod.unsigned (N.v40106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40106 s i)) at 1.
  unfold R.v40106, N.v40106.
  unfold R.v6, N.v6.
  rewrite ?node_7683.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40107 (s : N.State) (i : N.Inputs) :
  R.v40107 (state s) (inputs i) = Zmod.unsigned (N.v40107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40107 s i)) at 1.
  unfold R.v40107, N.v40107.
  rewrite ?node_40105.
  rewrite ?node_40106.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40108 (s : N.State) (i : N.Inputs) :
  R.v40108 (state s) (inputs i) = Zmod.unsigned (N.v40108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40108 s i)) at 1.
  unfold R.v40108, N.v40108.
  rewrite ?node_40104.
  rewrite ?node_40107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40109 (s : N.State) (i : N.Inputs) :
  R.v40109 (state s) (inputs i) = Zmod.unsigned (N.v40109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40109 s i)) at 1.
  unfold R.v40109, N.v40109.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40110 (s : N.State) (i : N.Inputs) :
  R.v40110 (state s) (inputs i) = Zmod.unsigned (N.v40110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40110 s i)) at 1.
  unfold R.v40110, N.v40110.
  rewrite ?node_7624.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40111 (s : N.State) (i : N.Inputs) :
  R.v40111 (state s) (inputs i) = Zmod.unsigned (N.v40111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40111 s i)) at 1.
  unfold R.v40111, N.v40111.
  rewrite ?node_7620.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40112 (s : N.State) (i : N.Inputs) :
  R.v40112 (state s) (inputs i) = Zmod.unsigned (N.v40112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40112 s i)) at 1.
  unfold R.v40112, N.v40112.
  rewrite ?node_7612.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40113 (s : N.State) (i : N.Inputs) :
  R.v40113 (state s) (inputs i) = Zmod.unsigned (N.v40113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40113 s i)) at 1.
  unfold R.v40113, N.v40113.
  unfold R.v6, N.v6.
  rewrite ?node_7604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40114 (s : N.State) (i : N.Inputs) :
  R.v40114 (state s) (inputs i) = Zmod.unsigned (N.v40114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40114 s i)) at 1.
  unfold R.v40114, N.v40114.
  unfold R.v6, N.v6.
  rewrite ?node_7597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40115 (s : N.State) (i : N.Inputs) :
  R.v40115 (state s) (inputs i) = Zmod.unsigned (N.v40115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40115 s i)) at 1.
  unfold R.v40115, N.v40115.
  rewrite ?node_40113.
  rewrite ?node_40114.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40116 (s : N.State) (i : N.Inputs) :
  R.v40116 (state s) (inputs i) = Zmod.unsigned (N.v40116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40116 s i)) at 1.
  unfold R.v40116, N.v40116.
  unfold R.v16484, N.v16484.
  rewrite ?node_40115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40117 (s : N.State) (i : N.Inputs) :
  R.v40117 (state s) (inputs i) = Zmod.unsigned (N.v40117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40117 s i)) at 1.
  unfold R.v40117, N.v40117.
  rewrite ?node_40110.
  rewrite ?node_40111.
  rewrite ?node_40112.
  rewrite ?node_40116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40118 (s : N.State) (i : N.Inputs) :
  R.v40118 (state s) (inputs i) = Zmod.unsigned (N.v40118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40118 s i)) at 1.
  unfold R.v40118, N.v40118.
  unfold R.v6, N.v6.
  rewrite ?node_40117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40119 (s : N.State) (i : N.Inputs) :
  R.v40119 (state s) (inputs i) = Zmod.unsigned (N.v40119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40119 s i)) at 1.
  unfold R.v40119, N.v40119.
  rewrite ?node_7625.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40120 (s : N.State) (i : N.Inputs) :
  R.v40120 (state s) (inputs i) = Zmod.unsigned (N.v40120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40120 s i)) at 1.
  unfold R.v40120, N.v40120.
  unfold R.v6, N.v6.
  rewrite ?node_7736.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40121 (s : N.State) (i : N.Inputs) :
  R.v40121 (state s) (inputs i) = Zmod.unsigned (N.v40121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40121 s i)) at 1.
  unfold R.v40121, N.v40121.
  unfold R.v6, N.v6.
  rewrite ?node_7786.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40122 (s : N.State) (i : N.Inputs) :
  R.v40122 (state s) (inputs i) = Zmod.unsigned (N.v40122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40122 s i)) at 1.
  unfold R.v40122, N.v40122.
  rewrite ?node_40119.
  rewrite ?node_40120.
  rewrite ?node_40121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40123 (s : N.State) (i : N.Inputs) :
  R.v40123 (state s) (inputs i) = Zmod.unsigned (N.v40123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40123 s i)) at 1.
  unfold R.v40123, N.v40123.
  rewrite ?node_40118.
  rewrite ?node_40122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40124 (s : N.State) (i : N.Inputs) :
  R.v40124 (state s) (inputs i) = Zmod.unsigned (N.v40124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40124 s i)) at 1.
  unfold R.v40124, N.v40124.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40125 (s : N.State) (i : N.Inputs) :
  R.v40125 (state s) (inputs i) = Zmod.unsigned (N.v40125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40125 s i)) at 1.
  unfold R.v40125, N.v40125.
  rewrite ?node_7612.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40126 (s : N.State) (i : N.Inputs) :
  R.v40126 (state s) (inputs i) = Zmod.unsigned (N.v40126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40126 s i)) at 1.
  unfold R.v40126, N.v40126.
  unfold R.v6, N.v6.
  rewrite ?node_7604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40127 (s : N.State) (i : N.Inputs) :
  R.v40127 (state s) (inputs i) = Zmod.unsigned (N.v40127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40127 s i)) at 1.
  unfold R.v40127, N.v40127.
  unfold R.v6, N.v6.
  rewrite ?node_7597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40128 (s : N.State) (i : N.Inputs) :
  R.v40128 (state s) (inputs i) = Zmod.unsigned (N.v40128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40128 s i)) at 1.
  unfold R.v40128, N.v40128.
  rewrite ?node_40126.
  rewrite ?node_40127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40129 (s : N.State) (i : N.Inputs) :
  R.v40129 (state s) (inputs i) = Zmod.unsigned (N.v40129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40129 s i)) at 1.
  unfold R.v40129, N.v40129.
  unfold R.v16484, N.v16484.
  rewrite ?node_40128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40130 (s : N.State) (i : N.Inputs) :
  R.v40130 (state s) (inputs i) = Zmod.unsigned (N.v40130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40130 s i)) at 1.
  unfold R.v40130, N.v40130.
  rewrite ?node_40125.
  rewrite ?node_40129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40131 (s : N.State) (i : N.Inputs) :
  R.v40131 (state s) (inputs i) = Zmod.unsigned (N.v40131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40131 s i)) at 1.
  unfold R.v40131, N.v40131.
  unfold R.v6, N.v6.
  rewrite ?node_40130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40132 (s : N.State) (i : N.Inputs) :
  R.v40132 (state s) (inputs i) = Zmod.unsigned (N.v40132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40132 s i)) at 1.
  unfold R.v40132, N.v40132.
  rewrite ?node_7613.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40133 (s : N.State) (i : N.Inputs) :
  R.v40133 (state s) (inputs i) = Zmod.unsigned (N.v40133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40133 s i)) at 1.
  unfold R.v40133, N.v40133.
  unfold R.v6, N.v6.
  rewrite ?node_7736.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40134 (s : N.State) (i : N.Inputs) :
  R.v40134 (state s) (inputs i) = Zmod.unsigned (N.v40134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40134 s i)) at 1.
  unfold R.v40134, N.v40134.
  rewrite ?node_40132.
  rewrite ?node_40133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40135 (s : N.State) (i : N.Inputs) :
  R.v40135 (state s) (inputs i) = Zmod.unsigned (N.v40135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40135 s i)) at 1.
  unfold R.v40135, N.v40135.
  rewrite ?node_40131.
  rewrite ?node_40134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40136 (s : N.State) (i : N.Inputs) :
  R.v40136 (state s) (inputs i) = Zmod.unsigned (N.v40136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40136 s i)) at 1.
  unfold R.v40136, N.v40136.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40137 (s : N.State) (i : N.Inputs) :
  R.v40137 (state s) (inputs i) = Zmod.unsigned (N.v40137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40137 s i)) at 1.
  unfold R.v40137, N.v40137.
  rewrite ?node_7624.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40138 (s : N.State) (i : N.Inputs) :
  R.v40138 (state s) (inputs i) = Zmod.unsigned (N.v40138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40138 s i)) at 1.
  unfold R.v40138, N.v40138.
  unfold R.v6, N.v6.
  rewrite ?node_7620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40139 (s : N.State) (i : N.Inputs) :
  R.v40139 (state s) (inputs i) = Zmod.unsigned (N.v40139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40139 s i)) at 1.
  unfold R.v40139, N.v40139.
  unfold R.v6, N.v6.
  rewrite ?node_7613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40140 (s : N.State) (i : N.Inputs) :
  R.v40140 (state s) (inputs i) = Zmod.unsigned (N.v40140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40140 s i)) at 1.
  unfold R.v40140, N.v40140.
  rewrite ?node_40138.
  rewrite ?node_40139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40141 (s : N.State) (i : N.Inputs) :
  R.v40141 (state s) (inputs i) = Zmod.unsigned (N.v40141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40141 s i)) at 1.
  unfold R.v40141, N.v40141.
  unfold R.v16484, N.v16484.
  rewrite ?node_40140.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40142 (s : N.State) (i : N.Inputs) :
  R.v40142 (state s) (inputs i) = Zmod.unsigned (N.v40142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40142 s i)) at 1.
  unfold R.v40142, N.v40142.
  rewrite ?node_40137.
  rewrite ?node_40141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40143 (s : N.State) (i : N.Inputs) :
  R.v40143 (state s) (inputs i) = Zmod.unsigned (N.v40143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40143 s i)) at 1.
  unfold R.v40143, N.v40143.
  unfold R.v6, N.v6.
  rewrite ?node_40142.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40144 (s : N.State) (i : N.Inputs) :
  R.v40144 (state s) (inputs i) = Zmod.unsigned (N.v40144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40144 s i)) at 1.
  unfold R.v40144, N.v40144.
  rewrite ?node_7625.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40145 (s : N.State) (i : N.Inputs) :
  R.v40145 (state s) (inputs i) = Zmod.unsigned (N.v40145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40145 s i)) at 1.
  unfold R.v40145, N.v40145.
  unfold R.v6, N.v6.
  rewrite ?node_7786.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40146 (s : N.State) (i : N.Inputs) :
  R.v40146 (state s) (inputs i) = Zmod.unsigned (N.v40146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40146 s i)) at 1.
  unfold R.v40146, N.v40146.
  rewrite ?node_40144.
  rewrite ?node_40145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40147 (s : N.State) (i : N.Inputs) :
  R.v40147 (state s) (inputs i) = Zmod.unsigned (N.v40147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40147 s i)) at 1.
  unfold R.v40147, N.v40147.
  rewrite ?node_40143.
  rewrite ?node_40146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40148 (s : N.State) (i : N.Inputs) :
  R.v40148 (state s) (inputs i) = Zmod.unsigned (N.v40148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40148 s i)) at 1.
  unfold R.v40148, N.v40148.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40149 (s : N.State) (i : N.Inputs) :
  R.v40149 (state s) (inputs i) = Zmod.unsigned (N.v40149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40149 s i)) at 1.
  unfold R.v40149, N.v40149.
  rewrite ?node_7647.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40150 (s : N.State) (i : N.Inputs) :
  R.v40150 (state s) (inputs i) = Zmod.unsigned (N.v40150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40150 s i)) at 1.
  unfold R.v40150, N.v40150.
  rewrite ?node_7643.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40151 (s : N.State) (i : N.Inputs) :
  R.v40151 (state s) (inputs i) = Zmod.unsigned (N.v40151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40151 s i)) at 1.
  unfold R.v40151, N.v40151.
  rewrite ?node_7639.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40152 (s : N.State) (i : N.Inputs) :
  R.v40152 (state s) (inputs i) = Zmod.unsigned (N.v40152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40152 s i)) at 1.
  unfold R.v40152, N.v40152.
  unfold R.v6, N.v6.
  rewrite ?node_7635.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40153 (s : N.State) (i : N.Inputs) :
  R.v40153 (state s) (inputs i) = Zmod.unsigned (N.v40153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40153 s i)) at 1.
  unfold R.v40153, N.v40153.
  unfold R.v6, N.v6.
  rewrite ?node_7632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40154 (s : N.State) (i : N.Inputs) :
  R.v40154 (state s) (inputs i) = Zmod.unsigned (N.v40154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40154 s i)) at 1.
  unfold R.v40154, N.v40154.
  rewrite ?node_40152.
  rewrite ?node_40153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40155 (s : N.State) (i : N.Inputs) :
  R.v40155 (state s) (inputs i) = Zmod.unsigned (N.v40155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40155 s i)) at 1.
  unfold R.v40155, N.v40155.
  unfold R.v16484, N.v16484.
  rewrite ?node_40154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40156 (s : N.State) (i : N.Inputs) :
  R.v40156 (state s) (inputs i) = Zmod.unsigned (N.v40156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40156 s i)) at 1.
  unfold R.v40156, N.v40156.
  rewrite ?node_40149.
  rewrite ?node_40150.
  rewrite ?node_40151.
  rewrite ?node_40155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40157 (s : N.State) (i : N.Inputs) :
  R.v40157 (state s) (inputs i) = Zmod.unsigned (N.v40157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40157 s i)) at 1.
  unfold R.v40157, N.v40157.
  unfold R.v6, N.v6.
  rewrite ?node_40156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40158 (s : N.State) (i : N.Inputs) :
  R.v40158 (state s) (inputs i) = Zmod.unsigned (N.v40158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40158 s i)) at 1.
  unfold R.v40158, N.v40158.
  rewrite ?node_7648.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40159 (s : N.State) (i : N.Inputs) :
  R.v40159 (state s) (inputs i) = Zmod.unsigned (N.v40159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40159 s i)) at 1.
  unfold R.v40159, N.v40159.
  unfold R.v6, N.v6.
  rewrite ?node_7763.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40160 (s : N.State) (i : N.Inputs) :
  R.v40160 (state s) (inputs i) = Zmod.unsigned (N.v40160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40160 s i)) at 1.
  unfold R.v40160, N.v40160.
  unfold R.v6, N.v6.
  rewrite ?node_7794.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40161 (s : N.State) (i : N.Inputs) :
  R.v40161 (state s) (inputs i) = Zmod.unsigned (N.v40161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40161 s i)) at 1.
  unfold R.v40161, N.v40161.
  rewrite ?node_40158.
  rewrite ?node_40159.
  rewrite ?node_40160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40162 (s : N.State) (i : N.Inputs) :
  R.v40162 (state s) (inputs i) = Zmod.unsigned (N.v40162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40162 s i)) at 1.
  unfold R.v40162, N.v40162.
  rewrite ?node_40157.
  rewrite ?node_40161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40163 (s : N.State) (i : N.Inputs) :
  R.v40163 (state s) (inputs i) = Zmod.unsigned (N.v40163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40163 s i)) at 1.
  unfold R.v40163, N.v40163.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40164 (s : N.State) (i : N.Inputs) :
  R.v40164 (state s) (inputs i) = Zmod.unsigned (N.v40164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40164 s i)) at 1.
  unfold R.v40164, N.v40164.
  rewrite ?node_7639.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40165 (s : N.State) (i : N.Inputs) :
  R.v40165 (state s) (inputs i) = Zmod.unsigned (N.v40165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40165 s i)) at 1.
  unfold R.v40165, N.v40165.
  unfold R.v6, N.v6.
  rewrite ?node_7635.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40166 (s : N.State) (i : N.Inputs) :
  R.v40166 (state s) (inputs i) = Zmod.unsigned (N.v40166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40166 s i)) at 1.
  unfold R.v40166, N.v40166.
  unfold R.v6, N.v6.
  rewrite ?node_7632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40167 (s : N.State) (i : N.Inputs) :
  R.v40167 (state s) (inputs i) = Zmod.unsigned (N.v40167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40167 s i)) at 1.
  unfold R.v40167, N.v40167.
  rewrite ?node_40165.
  rewrite ?node_40166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40168 (s : N.State) (i : N.Inputs) :
  R.v40168 (state s) (inputs i) = Zmod.unsigned (N.v40168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40168 s i)) at 1.
  unfold R.v40168, N.v40168.
  unfold R.v16484, N.v16484.
  rewrite ?node_40167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40169 (s : N.State) (i : N.Inputs) :
  R.v40169 (state s) (inputs i) = Zmod.unsigned (N.v40169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40169 s i)) at 1.
  unfold R.v40169, N.v40169.
  rewrite ?node_40164.
  rewrite ?node_40168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40170 (s : N.State) (i : N.Inputs) :
  R.v40170 (state s) (inputs i) = Zmod.unsigned (N.v40170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40170 s i)) at 1.
  unfold R.v40170, N.v40170.
  unfold R.v6, N.v6.
  rewrite ?node_40169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40171 (s : N.State) (i : N.Inputs) :
  R.v40171 (state s) (inputs i) = Zmod.unsigned (N.v40171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40171 s i)) at 1.
  unfold R.v40171, N.v40171.
  rewrite ?node_7640.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40172 (s : N.State) (i : N.Inputs) :
  R.v40172 (state s) (inputs i) = Zmod.unsigned (N.v40172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40172 s i)) at 1.
  unfold R.v40172, N.v40172.
  unfold R.v6, N.v6.
  rewrite ?node_7763.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40173 (s : N.State) (i : N.Inputs) :
  R.v40173 (state s) (inputs i) = Zmod.unsigned (N.v40173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40173 s i)) at 1.
  unfold R.v40173, N.v40173.
  rewrite ?node_40171.
  rewrite ?node_40172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40174 (s : N.State) (i : N.Inputs) :
  R.v40174 (state s) (inputs i) = Zmod.unsigned (N.v40174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40174 s i)) at 1.
  unfold R.v40174, N.v40174.
  rewrite ?node_40170.
  rewrite ?node_40173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40175 (s : N.State) (i : N.Inputs) :
  R.v40175 (state s) (inputs i) = Zmod.unsigned (N.v40175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40175 s i)) at 1.
  unfold R.v40175, N.v40175.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40176 (s : N.State) (i : N.Inputs) :
  R.v40176 (state s) (inputs i) = Zmod.unsigned (N.v40176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40176 s i)) at 1.
  unfold R.v40176, N.v40176.
  rewrite ?node_7647.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40177 (s : N.State) (i : N.Inputs) :
  R.v40177 (state s) (inputs i) = Zmod.unsigned (N.v40177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40177 s i)) at 1.
  unfold R.v40177, N.v40177.
  unfold R.v6, N.v6.
  rewrite ?node_7643.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40178 (s : N.State) (i : N.Inputs) :
  R.v40178 (state s) (inputs i) = Zmod.unsigned (N.v40178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40178 s i)) at 1.
  unfold R.v40178, N.v40178.
  unfold R.v6, N.v6.
  rewrite ?node_7640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40179 (s : N.State) (i : N.Inputs) :
  R.v40179 (state s) (inputs i) = Zmod.unsigned (N.v40179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40179 s i)) at 1.
  unfold R.v40179, N.v40179.
  rewrite ?node_40177.
  rewrite ?node_40178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40180 (s : N.State) (i : N.Inputs) :
  R.v40180 (state s) (inputs i) = Zmod.unsigned (N.v40180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40180 s i)) at 1.
  unfold R.v40180, N.v40180.
  unfold R.v16484, N.v16484.
  rewrite ?node_40179.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40181 (s : N.State) (i : N.Inputs) :
  R.v40181 (state s) (inputs i) = Zmod.unsigned (N.v40181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40181 s i)) at 1.
  unfold R.v40181, N.v40181.
  rewrite ?node_40176.
  rewrite ?node_40180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40182 (s : N.State) (i : N.Inputs) :
  R.v40182 (state s) (inputs i) = Zmod.unsigned (N.v40182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40182 s i)) at 1.
  unfold R.v40182, N.v40182.
  unfold R.v6, N.v6.
  rewrite ?node_40181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40183 (s : N.State) (i : N.Inputs) :
  R.v40183 (state s) (inputs i) = Zmod.unsigned (N.v40183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40183 s i)) at 1.
  unfold R.v40183, N.v40183.
  rewrite ?node_7648.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40184 (s : N.State) (i : N.Inputs) :
  R.v40184 (state s) (inputs i) = Zmod.unsigned (N.v40184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40184 s i)) at 1.
  unfold R.v40184, N.v40184.
  unfold R.v6, N.v6.
  rewrite ?node_7794.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40185 (s : N.State) (i : N.Inputs) :
  R.v40185 (state s) (inputs i) = Zmod.unsigned (N.v40185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40185 s i)) at 1.
  unfold R.v40185, N.v40185.
  rewrite ?node_40183.
  rewrite ?node_40184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40186 (s : N.State) (i : N.Inputs) :
  R.v40186 (state s) (inputs i) = Zmod.unsigned (N.v40186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40186 s i)) at 1.
  unfold R.v40186, N.v40186.
  rewrite ?node_40182.
  rewrite ?node_40185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40187 (s : N.State) (i : N.Inputs) :
  R.v40187 (state s) (inputs i) = Zmod.unsigned (N.v40187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40187 s i)) at 1.
  unfold R.v40187, N.v40187.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40188 (s : N.State) (i : N.Inputs) :
  R.v40188 (state s) (inputs i) = Zmod.unsigned (N.v40188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40188 s i)) at 1.
  unfold R.v40188, N.v40188.
  rewrite ?node_7667.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40189 (s : N.State) (i : N.Inputs) :
  R.v40189 (state s) (inputs i) = Zmod.unsigned (N.v40189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40189 s i)) at 1.
  unfold R.v40189, N.v40189.
  rewrite ?node_7663.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40190 (s : N.State) (i : N.Inputs) :
  R.v40190 (state s) (inputs i) = Zmod.unsigned (N.v40190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40190 s i)) at 1.
  unfold R.v40190, N.v40190.
  rewrite ?node_7659.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40191 (s : N.State) (i : N.Inputs) :
  R.v40191 (state s) (inputs i) = Zmod.unsigned (N.v40191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40191 s i)) at 1.
  unfold R.v40191, N.v40191.
  unfold R.v6, N.v6.
  rewrite ?node_7655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40192 (s : N.State) (i : N.Inputs) :
  R.v40192 (state s) (inputs i) = Zmod.unsigned (N.v40192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40192 s i)) at 1.
  unfold R.v40192, N.v40192.
  unfold R.v6, N.v6.
  rewrite ?node_7652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40193 (s : N.State) (i : N.Inputs) :
  R.v40193 (state s) (inputs i) = Zmod.unsigned (N.v40193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40193 s i)) at 1.
  unfold R.v40193, N.v40193.
  rewrite ?node_40191.
  rewrite ?node_40192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40194 (s : N.State) (i : N.Inputs) :
  R.v40194 (state s) (inputs i) = Zmod.unsigned (N.v40194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40194 s i)) at 1.
  unfold R.v40194, N.v40194.
  unfold R.v16484, N.v16484.
  rewrite ?node_40193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40195 (s : N.State) (i : N.Inputs) :
  R.v40195 (state s) (inputs i) = Zmod.unsigned (N.v40195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40195 s i)) at 1.
  unfold R.v40195, N.v40195.
  rewrite ?node_40188.
  rewrite ?node_40189.
  rewrite ?node_40190.
  rewrite ?node_40194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40196 (s : N.State) (i : N.Inputs) :
  R.v40196 (state s) (inputs i) = Zmod.unsigned (N.v40196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40196 s i)) at 1.
  unfold R.v40196, N.v40196.
  unfold R.v6, N.v6.
  rewrite ?node_40195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40197 (s : N.State) (i : N.Inputs) :
  R.v40197 (state s) (inputs i) = Zmod.unsigned (N.v40197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40197 s i)) at 1.
  unfold R.v40197, N.v40197.
  rewrite ?node_7668.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40198 (s : N.State) (i : N.Inputs) :
  R.v40198 (state s) (inputs i) = Zmod.unsigned (N.v40198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40198 s i)) at 1.
  unfold R.v40198, N.v40198.
  unfold R.v6, N.v6.
  rewrite ?node_7781.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40199 (s : N.State) (i : N.Inputs) :
  R.v40199 (state s) (inputs i) = Zmod.unsigned (N.v40199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40199 s i)) at 1.
  unfold R.v40199, N.v40199.
  unfold R.v6, N.v6.
  rewrite ?node_7797.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40200 (s : N.State) (i : N.Inputs) :
  R.v40200 (state s) (inputs i) = Zmod.unsigned (N.v40200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40200 s i)) at 1.
  unfold R.v40200, N.v40200.
  rewrite ?node_40197.
  rewrite ?node_40198.
  rewrite ?node_40199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40201 (s : N.State) (i : N.Inputs) :
  R.v40201 (state s) (inputs i) = Zmod.unsigned (N.v40201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40201 s i)) at 1.
  unfold R.v40201, N.v40201.
  rewrite ?node_40196.
  rewrite ?node_40200.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40202 (s : N.State) (i : N.Inputs) :
  R.v40202 (state s) (inputs i) = Zmod.unsigned (N.v40202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40202 s i)) at 1.
  unfold R.v40202, N.v40202.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40203 (s : N.State) (i : N.Inputs) :
  R.v40203 (state s) (inputs i) = Zmod.unsigned (N.v40203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40203 s i)) at 1.
  unfold R.v40203, N.v40203.
  rewrite ?node_7659.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40204 (s : N.State) (i : N.Inputs) :
  R.v40204 (state s) (inputs i) = Zmod.unsigned (N.v40204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40204 s i)) at 1.
  unfold R.v40204, N.v40204.
  unfold R.v6, N.v6.
  rewrite ?node_7655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40205 (s : N.State) (i : N.Inputs) :
  R.v40205 (state s) (inputs i) = Zmod.unsigned (N.v40205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40205 s i)) at 1.
  unfold R.v40205, N.v40205.
  unfold R.v6, N.v6.
  rewrite ?node_7652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40206 (s : N.State) (i : N.Inputs) :
  R.v40206 (state s) (inputs i) = Zmod.unsigned (N.v40206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40206 s i)) at 1.
  unfold R.v40206, N.v40206.
  rewrite ?node_40204.
  rewrite ?node_40205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40207 (s : N.State) (i : N.Inputs) :
  R.v40207 (state s) (inputs i) = Zmod.unsigned (N.v40207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40207 s i)) at 1.
  unfold R.v40207, N.v40207.
  unfold R.v16484, N.v16484.
  rewrite ?node_40206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40208 (s : N.State) (i : N.Inputs) :
  R.v40208 (state s) (inputs i) = Zmod.unsigned (N.v40208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40208 s i)) at 1.
  unfold R.v40208, N.v40208.
  rewrite ?node_40203.
  rewrite ?node_40207.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40209 (s : N.State) (i : N.Inputs) :
  R.v40209 (state s) (inputs i) = Zmod.unsigned (N.v40209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40209 s i)) at 1.
  unfold R.v40209, N.v40209.
  unfold R.v6, N.v6.
  rewrite ?node_40208.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40210 (s : N.State) (i : N.Inputs) :
  R.v40210 (state s) (inputs i) = Zmod.unsigned (N.v40210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40210 s i)) at 1.
  unfold R.v40210, N.v40210.
  rewrite ?node_7660.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40211 (s : N.State) (i : N.Inputs) :
  R.v40211 (state s) (inputs i) = Zmod.unsigned (N.v40211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40211 s i)) at 1.
  unfold R.v40211, N.v40211.
  unfold R.v6, N.v6.
  rewrite ?node_7781.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40212 (s : N.State) (i : N.Inputs) :
  R.v40212 (state s) (inputs i) = Zmod.unsigned (N.v40212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40212 s i)) at 1.
  unfold R.v40212, N.v40212.
  rewrite ?node_40210.
  rewrite ?node_40211.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40213 (s : N.State) (i : N.Inputs) :
  R.v40213 (state s) (inputs i) = Zmod.unsigned (N.v40213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40213 s i)) at 1.
  unfold R.v40213, N.v40213.
  rewrite ?node_40209.
  rewrite ?node_40212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40214 (s : N.State) (i : N.Inputs) :
  R.v40214 (state s) (inputs i) = Zmod.unsigned (N.v40214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40214 s i)) at 1.
  unfold R.v40214, N.v40214.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40215 (s : N.State) (i : N.Inputs) :
  R.v40215 (state s) (inputs i) = Zmod.unsigned (N.v40215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40215 s i)) at 1.
  unfold R.v40215, N.v40215.
  rewrite ?node_7667.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40216 (s : N.State) (i : N.Inputs) :
  R.v40216 (state s) (inputs i) = Zmod.unsigned (N.v40216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40216 s i)) at 1.
  unfold R.v40216, N.v40216.
  unfold R.v6, N.v6.
  rewrite ?node_7663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40217 (s : N.State) (i : N.Inputs) :
  R.v40217 (state s) (inputs i) = Zmod.unsigned (N.v40217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40217 s i)) at 1.
  unfold R.v40217, N.v40217.
  unfold R.v6, N.v6.
  rewrite ?node_7660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40218 (s : N.State) (i : N.Inputs) :
  R.v40218 (state s) (inputs i) = Zmod.unsigned (N.v40218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40218 s i)) at 1.
  unfold R.v40218, N.v40218.
  rewrite ?node_40216.
  rewrite ?node_40217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40219 (s : N.State) (i : N.Inputs) :
  R.v40219 (state s) (inputs i) = Zmod.unsigned (N.v40219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40219 s i)) at 1.
  unfold R.v40219, N.v40219.
  unfold R.v16484, N.v16484.
  rewrite ?node_40218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40220 (s : N.State) (i : N.Inputs) :
  R.v40220 (state s) (inputs i) = Zmod.unsigned (N.v40220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40220 s i)) at 1.
  unfold R.v40220, N.v40220.
  rewrite ?node_40215.
  rewrite ?node_40219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40221 (s : N.State) (i : N.Inputs) :
  R.v40221 (state s) (inputs i) = Zmod.unsigned (N.v40221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40221 s i)) at 1.
  unfold R.v40221, N.v40221.
  unfold R.v6, N.v6.
  rewrite ?node_40220.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40222 (s : N.State) (i : N.Inputs) :
  R.v40222 (state s) (inputs i) = Zmod.unsigned (N.v40222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40222 s i)) at 1.
  unfold R.v40222, N.v40222.
  rewrite ?node_7668.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40223 (s : N.State) (i : N.Inputs) :
  R.v40223 (state s) (inputs i) = Zmod.unsigned (N.v40223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40223 s i)) at 1.
  unfold R.v40223, N.v40223.
  unfold R.v6, N.v6.
  rewrite ?node_7797.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40224 (s : N.State) (i : N.Inputs) :
  R.v40224 (state s) (inputs i) = Zmod.unsigned (N.v40224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40224 s i)) at 1.
  unfold R.v40224, N.v40224.
  rewrite ?node_40222.
  rewrite ?node_40223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40225 (s : N.State) (i : N.Inputs) :
  R.v40225 (state s) (inputs i) = Zmod.unsigned (N.v40225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40225 s i)) at 1.
  unfold R.v40225, N.v40225.
  rewrite ?node_40221.
  rewrite ?node_40224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40226 (s : N.State) (i : N.Inputs) :
  R.v40226 (state s) (inputs i) = Zmod.unsigned (N.v40226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40226 s i)) at 1.
  unfold R.v40226, N.v40226.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40227 (s : N.State) (i : N.Inputs) :
  R.v40227 (state s) (inputs i) = Zmod.unsigned (N.v40227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40227 s i)) at 1.
  unfold R.v40227, N.v40227.
  rewrite ?node_7736.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40228 (s : N.State) (i : N.Inputs) :
  R.v40228 (state s) (inputs i) = Zmod.unsigned (N.v40228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40228 s i)) at 1.
  unfold R.v40228, N.v40228.
  rewrite ?node_7732.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40229 (s : N.State) (i : N.Inputs) :
  R.v40229 (state s) (inputs i) = Zmod.unsigned (N.v40229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40229 s i)) at 1.
  unfold R.v40229, N.v40229.
  rewrite ?node_7724.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40230 (s : N.State) (i : N.Inputs) :
  R.v40230 (state s) (inputs i) = Zmod.unsigned (N.v40230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40230 s i)) at 1.
  unfold R.v40230, N.v40230.
  unfold R.v6, N.v6.
  rewrite ?node_7716.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40231 (s : N.State) (i : N.Inputs) :
  R.v40231 (state s) (inputs i) = Zmod.unsigned (N.v40231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40231 s i)) at 1.
  unfold R.v40231, N.v40231.
  unfold R.v6, N.v6.
  rewrite ?node_7709.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40232 (s : N.State) (i : N.Inputs) :
  R.v40232 (state s) (inputs i) = Zmod.unsigned (N.v40232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40232 s i)) at 1.
  unfold R.v40232, N.v40232.
  rewrite ?node_40230.
  rewrite ?node_40231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40233 (s : N.State) (i : N.Inputs) :
  R.v40233 (state s) (inputs i) = Zmod.unsigned (N.v40233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40233 s i)) at 1.
  unfold R.v40233, N.v40233.
  unfold R.v16484, N.v16484.
  rewrite ?node_40232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40234 (s : N.State) (i : N.Inputs) :
  R.v40234 (state s) (inputs i) = Zmod.unsigned (N.v40234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40234 s i)) at 1.
  unfold R.v40234, N.v40234.
  rewrite ?node_40227.
  rewrite ?node_40228.
  rewrite ?node_40229.
  rewrite ?node_40233.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40235 (s : N.State) (i : N.Inputs) :
  R.v40235 (state s) (inputs i) = Zmod.unsigned (N.v40235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40235 s i)) at 1.
  unfold R.v40235, N.v40235.
  unfold R.v6, N.v6.
  rewrite ?node_40234.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40236 (s : N.State) (i : N.Inputs) :
  R.v40236 (state s) (inputs i) = Zmod.unsigned (N.v40236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40236 s i)) at 1.
  unfold R.v40236, N.v40236.
  rewrite ?node_7737.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40237 (s : N.State) (i : N.Inputs) :
  R.v40237 (state s) (inputs i) = Zmod.unsigned (N.v40237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40237 s i)) at 1.
  unfold R.v40237, N.v40237.
  unfold R.v6, N.v6.
  rewrite ?node_7850.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40238 (s : N.State) (i : N.Inputs) :
  R.v40238 (state s) (inputs i) = Zmod.unsigned (N.v40238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40238 s i)) at 1.
  unfold R.v40238, N.v40238.
  unfold R.v6, N.v6.
  rewrite ?node_7907.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40239 (s : N.State) (i : N.Inputs) :
  R.v40239 (state s) (inputs i) = Zmod.unsigned (N.v40239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40239 s i)) at 1.
  unfold R.v40239, N.v40239.
  rewrite ?node_40236.
  rewrite ?node_40237.
  rewrite ?node_40238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40240 (s : N.State) (i : N.Inputs) :
  R.v40240 (state s) (inputs i) = Zmod.unsigned (N.v40240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40240 s i)) at 1.
  unfold R.v40240, N.v40240.
  rewrite ?node_40235.
  rewrite ?node_40239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40241 (s : N.State) (i : N.Inputs) :
  R.v40241 (state s) (inputs i) = Zmod.unsigned (N.v40241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40241 s i)) at 1.
  unfold R.v40241, N.v40241.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40242 (s : N.State) (i : N.Inputs) :
  R.v40242 (state s) (inputs i) = Zmod.unsigned (N.v40242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40242 s i)) at 1.
  unfold R.v40242, N.v40242.
  rewrite ?node_7724.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40243 (s : N.State) (i : N.Inputs) :
  R.v40243 (state s) (inputs i) = Zmod.unsigned (N.v40243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40243 s i)) at 1.
  unfold R.v40243, N.v40243.
  unfold R.v6, N.v6.
  rewrite ?node_7716.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40244 (s : N.State) (i : N.Inputs) :
  R.v40244 (state s) (inputs i) = Zmod.unsigned (N.v40244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40244 s i)) at 1.
  unfold R.v40244, N.v40244.
  unfold R.v6, N.v6.
  rewrite ?node_7709.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40245 (s : N.State) (i : N.Inputs) :
  R.v40245 (state s) (inputs i) = Zmod.unsigned (N.v40245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40245 s i)) at 1.
  unfold R.v40245, N.v40245.
  rewrite ?node_40243.
  rewrite ?node_40244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40246 (s : N.State) (i : N.Inputs) :
  R.v40246 (state s) (inputs i) = Zmod.unsigned (N.v40246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40246 s i)) at 1.
  unfold R.v40246, N.v40246.
  unfold R.v16484, N.v16484.
  rewrite ?node_40245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40247 (s : N.State) (i : N.Inputs) :
  R.v40247 (state s) (inputs i) = Zmod.unsigned (N.v40247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40247 s i)) at 1.
  unfold R.v40247, N.v40247.
  rewrite ?node_40242.
  rewrite ?node_40246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40248 (s : N.State) (i : N.Inputs) :
  R.v40248 (state s) (inputs i) = Zmod.unsigned (N.v40248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40248 s i)) at 1.
  unfold R.v40248, N.v40248.
  unfold R.v6, N.v6.
  rewrite ?node_40247.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40249 (s : N.State) (i : N.Inputs) :
  R.v40249 (state s) (inputs i) = Zmod.unsigned (N.v40249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40249 s i)) at 1.
  unfold R.v40249, N.v40249.
  rewrite ?node_7725.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40250 (s : N.State) (i : N.Inputs) :
  R.v40250 (state s) (inputs i) = Zmod.unsigned (N.v40250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40250 s i)) at 1.
  unfold R.v40250, N.v40250.
  unfold R.v6, N.v6.
  rewrite ?node_7850.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40251 (s : N.State) (i : N.Inputs) :
  R.v40251 (state s) (inputs i) = Zmod.unsigned (N.v40251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40251 s i)) at 1.
  unfold R.v40251, N.v40251.
  rewrite ?node_40249.
  rewrite ?node_40250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40252 (s : N.State) (i : N.Inputs) :
  R.v40252 (state s) (inputs i) = Zmod.unsigned (N.v40252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40252 s i)) at 1.
  unfold R.v40252, N.v40252.
  rewrite ?node_40248.
  rewrite ?node_40251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40253 (s : N.State) (i : N.Inputs) :
  R.v40253 (state s) (inputs i) = Zmod.unsigned (N.v40253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40253 s i)) at 1.
  unfold R.v40253, N.v40253.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40254 (s : N.State) (i : N.Inputs) :
  R.v40254 (state s) (inputs i) = Zmod.unsigned (N.v40254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40254 s i)) at 1.
  unfold R.v40254, N.v40254.
  rewrite ?node_7736.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40255 (s : N.State) (i : N.Inputs) :
  R.v40255 (state s) (inputs i) = Zmod.unsigned (N.v40255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40255 s i)) at 1.
  unfold R.v40255, N.v40255.
  unfold R.v6, N.v6.
  rewrite ?node_7732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40256 (s : N.State) (i : N.Inputs) :
  R.v40256 (state s) (inputs i) = Zmod.unsigned (N.v40256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40256 s i)) at 1.
  unfold R.v40256, N.v40256.
  unfold R.v6, N.v6.
  rewrite ?node_7725.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40257 (s : N.State) (i : N.Inputs) :
  R.v40257 (state s) (inputs i) = Zmod.unsigned (N.v40257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40257 s i)) at 1.
  unfold R.v40257, N.v40257.
  rewrite ?node_40255.
  rewrite ?node_40256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40258 (s : N.State) (i : N.Inputs) :
  R.v40258 (state s) (inputs i) = Zmod.unsigned (N.v40258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40258 s i)) at 1.
  unfold R.v40258, N.v40258.
  unfold R.v16484, N.v16484.
  rewrite ?node_40257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40259 (s : N.State) (i : N.Inputs) :
  R.v40259 (state s) (inputs i) = Zmod.unsigned (N.v40259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40259 s i)) at 1.
  unfold R.v40259, N.v40259.
  rewrite ?node_40254.
  rewrite ?node_40258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40260 (s : N.State) (i : N.Inputs) :
  R.v40260 (state s) (inputs i) = Zmod.unsigned (N.v40260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40260 s i)) at 1.
  unfold R.v40260, N.v40260.
  unfold R.v6, N.v6.
  rewrite ?node_40259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40261 (s : N.State) (i : N.Inputs) :
  R.v40261 (state s) (inputs i) = Zmod.unsigned (N.v40261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40261 s i)) at 1.
  unfold R.v40261, N.v40261.
  rewrite ?node_7737.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40262 (s : N.State) (i : N.Inputs) :
  R.v40262 (state s) (inputs i) = Zmod.unsigned (N.v40262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40262 s i)) at 1.
  unfold R.v40262, N.v40262.
  unfold R.v6, N.v6.
  rewrite ?node_7907.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40263 (s : N.State) (i : N.Inputs) :
  R.v40263 (state s) (inputs i) = Zmod.unsigned (N.v40263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40263 s i)) at 1.
  unfold R.v40263, N.v40263.
  rewrite ?node_40261.
  rewrite ?node_40262.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40264 (s : N.State) (i : N.Inputs) :
  R.v40264 (state s) (inputs i) = Zmod.unsigned (N.v40264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40264 s i)) at 1.
  unfold R.v40264, N.v40264.
  rewrite ?node_40260.
  rewrite ?node_40263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40265 (s : N.State) (i : N.Inputs) :
  R.v40265 (state s) (inputs i) = Zmod.unsigned (N.v40265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40265 s i)) at 1.
  unfold R.v40265, N.v40265.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40266 (s : N.State) (i : N.Inputs) :
  R.v40266 (state s) (inputs i) = Zmod.unsigned (N.v40266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40266 s i)) at 1.
  unfold R.v40266, N.v40266.
  rewrite ?node_7763.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40267 (s : N.State) (i : N.Inputs) :
  R.v40267 (state s) (inputs i) = Zmod.unsigned (N.v40267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40267 s i)) at 1.
  unfold R.v40267, N.v40267.
  rewrite ?node_7759.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40268 (s : N.State) (i : N.Inputs) :
  R.v40268 (state s) (inputs i) = Zmod.unsigned (N.v40268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40268 s i)) at 1.
  unfold R.v40268, N.v40268.
  rewrite ?node_7755.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40269 (s : N.State) (i : N.Inputs) :
  R.v40269 (state s) (inputs i) = Zmod.unsigned (N.v40269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40269 s i)) at 1.
  unfold R.v40269, N.v40269.
  unfold R.v6, N.v6.
  rewrite ?node_7751.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40270 (s : N.State) (i : N.Inputs) :
  R.v40270 (state s) (inputs i) = Zmod.unsigned (N.v40270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40270 s i)) at 1.
  unfold R.v40270, N.v40270.
  unfold R.v6, N.v6.
  rewrite ?node_7744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40271 (s : N.State) (i : N.Inputs) :
  R.v40271 (state s) (inputs i) = Zmod.unsigned (N.v40271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40271 s i)) at 1.
  unfold R.v40271, N.v40271.
  rewrite ?node_40269.
  rewrite ?node_40270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40272 (s : N.State) (i : N.Inputs) :
  R.v40272 (state s) (inputs i) = Zmod.unsigned (N.v40272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40272 s i)) at 1.
  unfold R.v40272, N.v40272.
  unfold R.v16484, N.v16484.
  rewrite ?node_40271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40273 (s : N.State) (i : N.Inputs) :
  R.v40273 (state s) (inputs i) = Zmod.unsigned (N.v40273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40273 s i)) at 1.
  unfold R.v40273, N.v40273.
  rewrite ?node_40266.
  rewrite ?node_40267.
  rewrite ?node_40268.
  rewrite ?node_40272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40274 (s : N.State) (i : N.Inputs) :
  R.v40274 (state s) (inputs i) = Zmod.unsigned (N.v40274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40274 s i)) at 1.
  unfold R.v40274, N.v40274.
  unfold R.v6, N.v6.
  rewrite ?node_40273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40275 (s : N.State) (i : N.Inputs) :
  R.v40275 (state s) (inputs i) = Zmod.unsigned (N.v40275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40275 s i)) at 1.
  unfold R.v40275, N.v40275.
  rewrite ?node_7764.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40276 (s : N.State) (i : N.Inputs) :
  R.v40276 (state s) (inputs i) = Zmod.unsigned (N.v40276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40276 s i)) at 1.
  unfold R.v40276, N.v40276.
  unfold R.v6, N.v6.
  rewrite ?node_7874.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40277 (s : N.State) (i : N.Inputs) :
  R.v40277 (state s) (inputs i) = Zmod.unsigned (N.v40277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40277 s i)) at 1.
  unfold R.v40277, N.v40277.
  unfold R.v6, N.v6.
  rewrite ?node_7910.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40278 (s : N.State) (i : N.Inputs) :
  R.v40278 (state s) (inputs i) = Zmod.unsigned (N.v40278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40278 s i)) at 1.
  unfold R.v40278, N.v40278.
  rewrite ?node_40275.
  rewrite ?node_40276.
  rewrite ?node_40277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40279 (s : N.State) (i : N.Inputs) :
  R.v40279 (state s) (inputs i) = Zmod.unsigned (N.v40279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40279 s i)) at 1.
  unfold R.v40279, N.v40279.
  rewrite ?node_40274.
  rewrite ?node_40278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40280 (s : N.State) (i : N.Inputs) :
  R.v40280 (state s) (inputs i) = Zmod.unsigned (N.v40280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40280 s i)) at 1.
  unfold R.v40280, N.v40280.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40281 (s : N.State) (i : N.Inputs) :
  R.v40281 (state s) (inputs i) = Zmod.unsigned (N.v40281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40281 s i)) at 1.
  unfold R.v40281, N.v40281.
  rewrite ?node_7755.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40282 (s : N.State) (i : N.Inputs) :
  R.v40282 (state s) (inputs i) = Zmod.unsigned (N.v40282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40282 s i)) at 1.
  unfold R.v40282, N.v40282.
  unfold R.v6, N.v6.
  rewrite ?node_7751.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40283 (s : N.State) (i : N.Inputs) :
  R.v40283 (state s) (inputs i) = Zmod.unsigned (N.v40283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40283 s i)) at 1.
  unfold R.v40283, N.v40283.
  unfold R.v6, N.v6.
  rewrite ?node_7744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40284 (s : N.State) (i : N.Inputs) :
  R.v40284 (state s) (inputs i) = Zmod.unsigned (N.v40284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40284 s i)) at 1.
  unfold R.v40284, N.v40284.
  rewrite ?node_40282.
  rewrite ?node_40283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40285 (s : N.State) (i : N.Inputs) :
  R.v40285 (state s) (inputs i) = Zmod.unsigned (N.v40285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40285 s i)) at 1.
  unfold R.v40285, N.v40285.
  unfold R.v16484, N.v16484.
  rewrite ?node_40284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40286 (s : N.State) (i : N.Inputs) :
  R.v40286 (state s) (inputs i) = Zmod.unsigned (N.v40286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40286 s i)) at 1.
  unfold R.v40286, N.v40286.
  rewrite ?node_40281.
  rewrite ?node_40285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40287 (s : N.State) (i : N.Inputs) :
  R.v40287 (state s) (inputs i) = Zmod.unsigned (N.v40287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40287 s i)) at 1.
  unfold R.v40287, N.v40287.
  unfold R.v6, N.v6.
  rewrite ?node_40286.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40288 (s : N.State) (i : N.Inputs) :
  R.v40288 (state s) (inputs i) = Zmod.unsigned (N.v40288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40288 s i)) at 1.
  unfold R.v40288, N.v40288.
  rewrite ?node_7756.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40289 (s : N.State) (i : N.Inputs) :
  R.v40289 (state s) (inputs i) = Zmod.unsigned (N.v40289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40289 s i)) at 1.
  unfold R.v40289, N.v40289.
  unfold R.v6, N.v6.
  rewrite ?node_7874.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40290 (s : N.State) (i : N.Inputs) :
  R.v40290 (state s) (inputs i) = Zmod.unsigned (N.v40290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40290 s i)) at 1.
  unfold R.v40290, N.v40290.
  rewrite ?node_40288.
  rewrite ?node_40289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40291 (s : N.State) (i : N.Inputs) :
  R.v40291 (state s) (inputs i) = Zmod.unsigned (N.v40291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40291 s i)) at 1.
  unfold R.v40291, N.v40291.
  rewrite ?node_40287.
  rewrite ?node_40290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40292 (s : N.State) (i : N.Inputs) :
  R.v40292 (state s) (inputs i) = Zmod.unsigned (N.v40292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40292 s i)) at 1.
  unfold R.v40292, N.v40292.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40293 (s : N.State) (i : N.Inputs) :
  R.v40293 (state s) (inputs i) = Zmod.unsigned (N.v40293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40293 s i)) at 1.
  unfold R.v40293, N.v40293.
  rewrite ?node_7763.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40294 (s : N.State) (i : N.Inputs) :
  R.v40294 (state s) (inputs i) = Zmod.unsigned (N.v40294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40294 s i)) at 1.
  unfold R.v40294, N.v40294.
  unfold R.v6, N.v6.
  rewrite ?node_7759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40295 (s : N.State) (i : N.Inputs) :
  R.v40295 (state s) (inputs i) = Zmod.unsigned (N.v40295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40295 s i)) at 1.
  unfold R.v40295, N.v40295.
  unfold R.v6, N.v6.
  rewrite ?node_7756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40296 (s : N.State) (i : N.Inputs) :
  R.v40296 (state s) (inputs i) = Zmod.unsigned (N.v40296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40296 s i)) at 1.
  unfold R.v40296, N.v40296.
  rewrite ?node_40294.
  rewrite ?node_40295.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40297 (s : N.State) (i : N.Inputs) :
  R.v40297 (state s) (inputs i) = Zmod.unsigned (N.v40297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40297 s i)) at 1.
  unfold R.v40297, N.v40297.
  unfold R.v16484, N.v16484.
  rewrite ?node_40296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40298 (s : N.State) (i : N.Inputs) :
  R.v40298 (state s) (inputs i) = Zmod.unsigned (N.v40298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40298 s i)) at 1.
  unfold R.v40298, N.v40298.
  rewrite ?node_40293.
  rewrite ?node_40297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40299 (s : N.State) (i : N.Inputs) :
  R.v40299 (state s) (inputs i) = Zmod.unsigned (N.v40299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40299 s i)) at 1.
  unfold R.v40299, N.v40299.
  unfold R.v6, N.v6.
  rewrite ?node_40298.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40300 (s : N.State) (i : N.Inputs) :
  R.v40300 (state s) (inputs i) = Zmod.unsigned (N.v40300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40300 s i)) at 1.
  unfold R.v40300, N.v40300.
  rewrite ?node_7764.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40301 (s : N.State) (i : N.Inputs) :
  R.v40301 (state s) (inputs i) = Zmod.unsigned (N.v40301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40301 s i)) at 1.
  unfold R.v40301, N.v40301.
  unfold R.v6, N.v6.
  rewrite ?node_7910.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40302 (s : N.State) (i : N.Inputs) :
  R.v40302 (state s) (inputs i) = Zmod.unsigned (N.v40302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40302 s i)) at 1.
  unfold R.v40302, N.v40302.
  rewrite ?node_40300.
  rewrite ?node_40301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40303 (s : N.State) (i : N.Inputs) :
  R.v40303 (state s) (inputs i) = Zmod.unsigned (N.v40303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40303 s i)) at 1.
  unfold R.v40303, N.v40303.
  rewrite ?node_40299.
  rewrite ?node_40302.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40304 (s : N.State) (i : N.Inputs) :
  R.v40304 (state s) (inputs i) = Zmod.unsigned (N.v40304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40304 s i)) at 1.
  unfold R.v40304, N.v40304.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40305 (s : N.State) (i : N.Inputs) :
  R.v40305 (state s) (inputs i) = Zmod.unsigned (N.v40305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40305 s i)) at 1.
  unfold R.v40305, N.v40305.
  rewrite ?node_7781.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40306 (s : N.State) (i : N.Inputs) :
  R.v40306 (state s) (inputs i) = Zmod.unsigned (N.v40306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40306 s i)) at 1.
  unfold R.v40306, N.v40306.
  rewrite ?node_7777.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40307 (s : N.State) (i : N.Inputs) :
  R.v40307 (state s) (inputs i) = Zmod.unsigned (N.v40307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40307 s i)) at 1.
  unfold R.v40307, N.v40307.
  rewrite ?node_7775.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40308 (s : N.State) (i : N.Inputs) :
  R.v40308 (state s) (inputs i) = Zmod.unsigned (N.v40308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40308 s i)) at 1.
  unfold R.v40308, N.v40308.
  unfold R.v6, N.v6.
  rewrite ?node_7771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40309 (s : N.State) (i : N.Inputs) :
  R.v40309 (state s) (inputs i) = Zmod.unsigned (N.v40309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40309 s i)) at 1.
  unfold R.v40309, N.v40309.
  unfold R.v6, N.v6.
  rewrite ?node_7768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40310 (s : N.State) (i : N.Inputs) :
  R.v40310 (state s) (inputs i) = Zmod.unsigned (N.v40310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40310 s i)) at 1.
  unfold R.v40310, N.v40310.
  rewrite ?node_40308.
  rewrite ?node_40309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40311 (s : N.State) (i : N.Inputs) :
  R.v40311 (state s) (inputs i) = Zmod.unsigned (N.v40311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40311 s i)) at 1.
  unfold R.v40311, N.v40311.
  unfold R.v16484, N.v16484.
  rewrite ?node_40310.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40312 (s : N.State) (i : N.Inputs) :
  R.v40312 (state s) (inputs i) = Zmod.unsigned (N.v40312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40312 s i)) at 1.
  unfold R.v40312, N.v40312.
  rewrite ?node_40305.
  rewrite ?node_40306.
  rewrite ?node_40307.
  rewrite ?node_40311.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40313 (s : N.State) (i : N.Inputs) :
  R.v40313 (state s) (inputs i) = Zmod.unsigned (N.v40313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40313 s i)) at 1.
  unfold R.v40313, N.v40313.
  unfold R.v6, N.v6.
  rewrite ?node_40312.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40314 (s : N.State) (i : N.Inputs) :
  R.v40314 (state s) (inputs i) = Zmod.unsigned (N.v40314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40314 s i)) at 1.
  unfold R.v40314, N.v40314.
  rewrite ?node_7782.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40315 (s : N.State) (i : N.Inputs) :
  R.v40315 (state s) (inputs i) = Zmod.unsigned (N.v40315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40315 s i)) at 1.
  unfold R.v40315, N.v40315.
  unfold R.v6, N.v6.
  rewrite ?node_7894.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40316 (s : N.State) (i : N.Inputs) :
  R.v40316 (state s) (inputs i) = Zmod.unsigned (N.v40316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40316 s i)) at 1.
  unfold R.v40316, N.v40316.
  unfold R.v6, N.v6.
  rewrite ?node_7914.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40317 (s : N.State) (i : N.Inputs) :
  R.v40317 (state s) (inputs i) = Zmod.unsigned (N.v40317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40317 s i)) at 1.
  unfold R.v40317, N.v40317.
  rewrite ?node_40314.
  rewrite ?node_40315.
  rewrite ?node_40316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40318 (s : N.State) (i : N.Inputs) :
  R.v40318 (state s) (inputs i) = Zmod.unsigned (N.v40318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40318 s i)) at 1.
  unfold R.v40318, N.v40318.
  rewrite ?node_40313.
  rewrite ?node_40317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40319 (s : N.State) (i : N.Inputs) :
  R.v40319 (state s) (inputs i) = Zmod.unsigned (N.v40319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40319 s i)) at 1.
  unfold R.v40319, N.v40319.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40320 (s : N.State) (i : N.Inputs) :
  R.v40320 (state s) (inputs i) = Zmod.unsigned (N.v40320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40320 s i)) at 1.
  unfold R.v40320, N.v40320.
  rewrite ?node_7775.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40321 (s : N.State) (i : N.Inputs) :
  R.v40321 (state s) (inputs i) = Zmod.unsigned (N.v40321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40321 s i)) at 1.
  unfold R.v40321, N.v40321.
  unfold R.v6, N.v6.
  rewrite ?node_7771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40322 (s : N.State) (i : N.Inputs) :
  R.v40322 (state s) (inputs i) = Zmod.unsigned (N.v40322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40322 s i)) at 1.
  unfold R.v40322, N.v40322.
  unfold R.v6, N.v6.
  rewrite ?node_7768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40323 (s : N.State) (i : N.Inputs) :
  R.v40323 (state s) (inputs i) = Zmod.unsigned (N.v40323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40323 s i)) at 1.
  unfold R.v40323, N.v40323.
  rewrite ?node_40321.
  rewrite ?node_40322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40324 (s : N.State) (i : N.Inputs) :
  R.v40324 (state s) (inputs i) = Zmod.unsigned (N.v40324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40324 s i)) at 1.
  unfold R.v40324, N.v40324.
  unfold R.v16484, N.v16484.
  rewrite ?node_40323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40325 (s : N.State) (i : N.Inputs) :
  R.v40325 (state s) (inputs i) = Zmod.unsigned (N.v40325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40325 s i)) at 1.
  unfold R.v40325, N.v40325.
  rewrite ?node_40320.
  rewrite ?node_40324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40326 (s : N.State) (i : N.Inputs) :
  R.v40326 (state s) (inputs i) = Zmod.unsigned (N.v40326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40326 s i)) at 1.
  unfold R.v40326, N.v40326.
  unfold R.v6, N.v6.
  rewrite ?node_40325.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40327 (s : N.State) (i : N.Inputs) :
  R.v40327 (state s) (inputs i) = Zmod.unsigned (N.v40327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40327 s i)) at 1.
  unfold R.v40327, N.v40327.
  rewrite ?node_7776.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40328 (s : N.State) (i : N.Inputs) :
  R.v40328 (state s) (inputs i) = Zmod.unsigned (N.v40328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40328 s i)) at 1.
  unfold R.v40328, N.v40328.
  unfold R.v6, N.v6.
  rewrite ?node_7894.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40329 (s : N.State) (i : N.Inputs) :
  R.v40329 (state s) (inputs i) = Zmod.unsigned (N.v40329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40329 s i)) at 1.
  unfold R.v40329, N.v40329.
  rewrite ?node_40327.
  rewrite ?node_40328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40330 (s : N.State) (i : N.Inputs) :
  R.v40330 (state s) (inputs i) = Zmod.unsigned (N.v40330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40330 s i)) at 1.
  unfold R.v40330, N.v40330.
  rewrite ?node_40326.
  rewrite ?node_40329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40331 (s : N.State) (i : N.Inputs) :
  R.v40331 (state s) (inputs i) = Zmod.unsigned (N.v40331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40331 s i)) at 1.
  unfold R.v40331, N.v40331.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40332 (s : N.State) (i : N.Inputs) :
  R.v40332 (state s) (inputs i) = Zmod.unsigned (N.v40332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40332 s i)) at 1.
  unfold R.v40332, N.v40332.
  rewrite ?node_7781.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40333 (s : N.State) (i : N.Inputs) :
  R.v40333 (state s) (inputs i) = Zmod.unsigned (N.v40333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40333 s i)) at 1.
  unfold R.v40333, N.v40333.
  unfold R.v6, N.v6.
  rewrite ?node_7777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40334 (s : N.State) (i : N.Inputs) :
  R.v40334 (state s) (inputs i) = Zmod.unsigned (N.v40334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40334 s i)) at 1.
  unfold R.v40334, N.v40334.
  unfold R.v6, N.v6.
  rewrite ?node_7776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40335 (s : N.State) (i : N.Inputs) :
  R.v40335 (state s) (inputs i) = Zmod.unsigned (N.v40335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40335 s i)) at 1.
  unfold R.v40335, N.v40335.
  rewrite ?node_40333.
  rewrite ?node_40334.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40336 (s : N.State) (i : N.Inputs) :
  R.v40336 (state s) (inputs i) = Zmod.unsigned (N.v40336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40336 s i)) at 1.
  unfold R.v40336, N.v40336.
  unfold R.v16484, N.v16484.
  rewrite ?node_40335.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40337 (s : N.State) (i : N.Inputs) :
  R.v40337 (state s) (inputs i) = Zmod.unsigned (N.v40337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40337 s i)) at 1.
  unfold R.v40337, N.v40337.
  rewrite ?node_40332.
  rewrite ?node_40336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40338 (s : N.State) (i : N.Inputs) :
  R.v40338 (state s) (inputs i) = Zmod.unsigned (N.v40338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40338 s i)) at 1.
  unfold R.v40338, N.v40338.
  unfold R.v6, N.v6.
  rewrite ?node_40337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40339 (s : N.State) (i : N.Inputs) :
  R.v40339 (state s) (inputs i) = Zmod.unsigned (N.v40339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40339 s i)) at 1.
  unfold R.v40339, N.v40339.
  rewrite ?node_7782.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40340 (s : N.State) (i : N.Inputs) :
  R.v40340 (state s) (inputs i) = Zmod.unsigned (N.v40340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40340 s i)) at 1.
  unfold R.v40340, N.v40340.
  unfold R.v6, N.v6.
  rewrite ?node_7914.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40341 (s : N.State) (i : N.Inputs) :
  R.v40341 (state s) (inputs i) = Zmod.unsigned (N.v40341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40341 s i)) at 1.
  unfold R.v40341, N.v40341.
  rewrite ?node_40339.
  rewrite ?node_40340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40342 (s : N.State) (i : N.Inputs) :
  R.v40342 (state s) (inputs i) = Zmod.unsigned (N.v40342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40342 s i)) at 1.
  unfold R.v40342, N.v40342.
  rewrite ?node_40338.
  rewrite ?node_40341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40343 (s : N.State) (i : N.Inputs) :
  R.v40343 (state s) (inputs i) = Zmod.unsigned (N.v40343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40343 s i)) at 1.
  unfold R.v40343, N.v40343.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40344 (s : N.State) (i : N.Inputs) :
  R.v40344 (state s) (inputs i) = Zmod.unsigned (N.v40344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40344 s i)) at 1.
  unfold R.v40344, N.v40344.
  rewrite ?node_7850.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40345 (s : N.State) (i : N.Inputs) :
  R.v40345 (state s) (inputs i) = Zmod.unsigned (N.v40345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40345 s i)) at 1.
  unfold R.v40345, N.v40345.
  rewrite ?node_7846.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40346 (s : N.State) (i : N.Inputs) :
  R.v40346 (state s) (inputs i) = Zmod.unsigned (N.v40346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40346 s i)) at 1.
  unfold R.v40346, N.v40346.
  rewrite ?node_7838.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40347 (s : N.State) (i : N.Inputs) :
  R.v40347 (state s) (inputs i) = Zmod.unsigned (N.v40347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40347 s i)) at 1.
  unfold R.v40347, N.v40347.
  unfold R.v6, N.v6.
  rewrite ?node_7830.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40348 (s : N.State) (i : N.Inputs) :
  R.v40348 (state s) (inputs i) = Zmod.unsigned (N.v40348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40348 s i)) at 1.
  unfold R.v40348, N.v40348.
  unfold R.v6, N.v6.
  rewrite ?node_7823.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40349 (s : N.State) (i : N.Inputs) :
  R.v40349 (state s) (inputs i) = Zmod.unsigned (N.v40349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40349 s i)) at 1.
  unfold R.v40349, N.v40349.
  rewrite ?node_40347.
  rewrite ?node_40348.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40350 (s : N.State) (i : N.Inputs) :
  R.v40350 (state s) (inputs i) = Zmod.unsigned (N.v40350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40350 s i)) at 1.
  unfold R.v40350, N.v40350.
  unfold R.v16484, N.v16484.
  rewrite ?node_40349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40351 (s : N.State) (i : N.Inputs) :
  R.v40351 (state s) (inputs i) = Zmod.unsigned (N.v40351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40351 s i)) at 1.
  unfold R.v40351, N.v40351.
  rewrite ?node_40344.
  rewrite ?node_40345.
  rewrite ?node_40346.
  rewrite ?node_40350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40352 (s : N.State) (i : N.Inputs) :
  R.v40352 (state s) (inputs i) = Zmod.unsigned (N.v40352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40352 s i)) at 1.
  unfold R.v40352, N.v40352.
  unfold R.v6, N.v6.
  rewrite ?node_40351.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40353 (s : N.State) (i : N.Inputs) :
  R.v40353 (state s) (inputs i) = Zmod.unsigned (N.v40353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40353 s i)) at 1.
  unfold R.v40353, N.v40353.
  rewrite ?node_7851.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40354 (s : N.State) (i : N.Inputs) :
  R.v40354 (state s) (inputs i) = Zmod.unsigned (N.v40354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40354 s i)) at 1.
  unfold R.v40354, N.v40354.
  unfold R.v6, N.v6.
  rewrite ?node_7967.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40355 (s : N.State) (i : N.Inputs) :
  R.v40355 (state s) (inputs i) = Zmod.unsigned (N.v40355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40355 s i)) at 1.
  unfold R.v40355, N.v40355.
  unfold R.v6, N.v6.
  rewrite ?node_8024.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40356 (s : N.State) (i : N.Inputs) :
  R.v40356 (state s) (inputs i) = Zmod.unsigned (N.v40356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40356 s i)) at 1.
  unfold R.v40356, N.v40356.
  rewrite ?node_40353.
  rewrite ?node_40354.
  rewrite ?node_40355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40357 (s : N.State) (i : N.Inputs) :
  R.v40357 (state s) (inputs i) = Zmod.unsigned (N.v40357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40357 s i)) at 1.
  unfold R.v40357, N.v40357.
  rewrite ?node_40352.
  rewrite ?node_40356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40358 (s : N.State) (i : N.Inputs) :
  R.v40358 (state s) (inputs i) = Zmod.unsigned (N.v40358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40358 s i)) at 1.
  unfold R.v40358, N.v40358.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40359 (s : N.State) (i : N.Inputs) :
  R.v40359 (state s) (inputs i) = Zmod.unsigned (N.v40359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40359 s i)) at 1.
  unfold R.v40359, N.v40359.
  rewrite ?node_7838.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40360 (s : N.State) (i : N.Inputs) :
  R.v40360 (state s) (inputs i) = Zmod.unsigned (N.v40360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40360 s i)) at 1.
  unfold R.v40360, N.v40360.
  unfold R.v6, N.v6.
  rewrite ?node_7830.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40361 (s : N.State) (i : N.Inputs) :
  R.v40361 (state s) (inputs i) = Zmod.unsigned (N.v40361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40361 s i)) at 1.
  unfold R.v40361, N.v40361.
  unfold R.v6, N.v6.
  rewrite ?node_7823.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40362 (s : N.State) (i : N.Inputs) :
  R.v40362 (state s) (inputs i) = Zmod.unsigned (N.v40362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40362 s i)) at 1.
  unfold R.v40362, N.v40362.
  rewrite ?node_40360.
  rewrite ?node_40361.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40363 (s : N.State) (i : N.Inputs) :
  R.v40363 (state s) (inputs i) = Zmod.unsigned (N.v40363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40363 s i)) at 1.
  unfold R.v40363, N.v40363.
  unfold R.v16484, N.v16484.
  rewrite ?node_40362.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40364 (s : N.State) (i : N.Inputs) :
  R.v40364 (state s) (inputs i) = Zmod.unsigned (N.v40364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40364 s i)) at 1.
  unfold R.v40364, N.v40364.
  rewrite ?node_40359.
  rewrite ?node_40363.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40365 (s : N.State) (i : N.Inputs) :
  R.v40365 (state s) (inputs i) = Zmod.unsigned (N.v40365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40365 s i)) at 1.
  unfold R.v40365, N.v40365.
  unfold R.v6, N.v6.
  rewrite ?node_40364.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40366 (s : N.State) (i : N.Inputs) :
  R.v40366 (state s) (inputs i) = Zmod.unsigned (N.v40366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40366 s i)) at 1.
  unfold R.v40366, N.v40366.
  rewrite ?node_7839.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40367 (s : N.State) (i : N.Inputs) :
  R.v40367 (state s) (inputs i) = Zmod.unsigned (N.v40367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40367 s i)) at 1.
  unfold R.v40367, N.v40367.
  unfold R.v6, N.v6.
  rewrite ?node_7967.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40368 (s : N.State) (i : N.Inputs) :
  R.v40368 (state s) (inputs i) = Zmod.unsigned (N.v40368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40368 s i)) at 1.
  unfold R.v40368, N.v40368.
  rewrite ?node_40366.
  rewrite ?node_40367.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40369 (s : N.State) (i : N.Inputs) :
  R.v40369 (state s) (inputs i) = Zmod.unsigned (N.v40369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40369 s i)) at 1.
  unfold R.v40369, N.v40369.
  rewrite ?node_40365.
  rewrite ?node_40368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40370 (s : N.State) (i : N.Inputs) :
  R.v40370 (state s) (inputs i) = Zmod.unsigned (N.v40370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40370 s i)) at 1.
  unfold R.v40370, N.v40370.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40371 (s : N.State) (i : N.Inputs) :
  R.v40371 (state s) (inputs i) = Zmod.unsigned (N.v40371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40371 s i)) at 1.
  unfold R.v40371, N.v40371.
  rewrite ?node_7850.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40372 (s : N.State) (i : N.Inputs) :
  R.v40372 (state s) (inputs i) = Zmod.unsigned (N.v40372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40372 s i)) at 1.
  unfold R.v40372, N.v40372.
  unfold R.v6, N.v6.
  rewrite ?node_7846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40373 (s : N.State) (i : N.Inputs) :
  R.v40373 (state s) (inputs i) = Zmod.unsigned (N.v40373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40373 s i)) at 1.
  unfold R.v40373, N.v40373.
  unfold R.v6, N.v6.
  rewrite ?node_7839.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40374 (s : N.State) (i : N.Inputs) :
  R.v40374 (state s) (inputs i) = Zmod.unsigned (N.v40374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40374 s i)) at 1.
  unfold R.v40374, N.v40374.
  rewrite ?node_40372.
  rewrite ?node_40373.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40375 (s : N.State) (i : N.Inputs) :
  R.v40375 (state s) (inputs i) = Zmod.unsigned (N.v40375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40375 s i)) at 1.
  unfold R.v40375, N.v40375.
  unfold R.v16484, N.v16484.
  rewrite ?node_40374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40376 (s : N.State) (i : N.Inputs) :
  R.v40376 (state s) (inputs i) = Zmod.unsigned (N.v40376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40376 s i)) at 1.
  unfold R.v40376, N.v40376.
  rewrite ?node_40371.
  rewrite ?node_40375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40377 (s : N.State) (i : N.Inputs) :
  R.v40377 (state s) (inputs i) = Zmod.unsigned (N.v40377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40377 s i)) at 1.
  unfold R.v40377, N.v40377.
  unfold R.v6, N.v6.
  rewrite ?node_40376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40378 (s : N.State) (i : N.Inputs) :
  R.v40378 (state s) (inputs i) = Zmod.unsigned (N.v40378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40378 s i)) at 1.
  unfold R.v40378, N.v40378.
  rewrite ?node_7851.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40379 (s : N.State) (i : N.Inputs) :
  R.v40379 (state s) (inputs i) = Zmod.unsigned (N.v40379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40379 s i)) at 1.
  unfold R.v40379, N.v40379.
  unfold R.v6, N.v6.
  rewrite ?node_8024.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40380 (s : N.State) (i : N.Inputs) :
  R.v40380 (state s) (inputs i) = Zmod.unsigned (N.v40380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40380 s i)) at 1.
  unfold R.v40380, N.v40380.
  rewrite ?node_40378.
  rewrite ?node_40379.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40381 (s : N.State) (i : N.Inputs) :
  R.v40381 (state s) (inputs i) = Zmod.unsigned (N.v40381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40381 s i)) at 1.
  unfold R.v40381, N.v40381.
  rewrite ?node_40377.
  rewrite ?node_40380.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40382 (s : N.State) (i : N.Inputs) :
  R.v40382 (state s) (inputs i) = Zmod.unsigned (N.v40382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40382 s i)) at 1.
  unfold R.v40382, N.v40382.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40383 (s : N.State) (i : N.Inputs) :
  R.v40383 (state s) (inputs i) = Zmod.unsigned (N.v40383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40383 s i)) at 1.
  unfold R.v40383, N.v40383.
  rewrite ?node_7874.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40384 (s : N.State) (i : N.Inputs) :
  R.v40384 (state s) (inputs i) = Zmod.unsigned (N.v40384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40384 s i)) at 1.
  unfold R.v40384, N.v40384.
  rewrite ?node_7870.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40385 (s : N.State) (i : N.Inputs) :
  R.v40385 (state s) (inputs i) = Zmod.unsigned (N.v40385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40385 s i)) at 1.
  unfold R.v40385, N.v40385.
  unfold R.v16463, N.v16463.
  rewrite !state_r622_nr_5F622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r622_nr_5F622 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40386 (s : N.State) (i : N.Inputs) :
  R.v40386 (state s) (inputs i) = Zmod.unsigned (N.v40386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40386 s i)) at 1.
  unfold R.v40386, N.v40386.
  unfold R.v6, N.v6.
  rewrite ?node_7865.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40387 (s : N.State) (i : N.Inputs) :
  R.v40387 (state s) (inputs i) = Zmod.unsigned (N.v40387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40387 s i)) at 1.
  unfold R.v40387, N.v40387.
  unfold R.v6, N.v6.
  rewrite ?node_7858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40388 (s : N.State) (i : N.Inputs) :
  R.v40388 (state s) (inputs i) = Zmod.unsigned (N.v40388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40388 s i)) at 1.
  unfold R.v40388, N.v40388.
  rewrite ?node_40386.
  rewrite ?node_40387.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40389 (s : N.State) (i : N.Inputs) :
  R.v40389 (state s) (inputs i) = Zmod.unsigned (N.v40389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40389 s i)) at 1.
  unfold R.v40389, N.v40389.
  unfold R.v16484, N.v16484.
  rewrite ?node_40388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40390 (s : N.State) (i : N.Inputs) :
  R.v40390 (state s) (inputs i) = Zmod.unsigned (N.v40390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40390 s i)) at 1.
  unfold R.v40390, N.v40390.
  rewrite ?node_40383.
  rewrite ?node_40384.
  rewrite ?node_40385.
  rewrite ?node_40389.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40391 (s : N.State) (i : N.Inputs) :
  R.v40391 (state s) (inputs i) = Zmod.unsigned (N.v40391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40391 s i)) at 1.
  unfold R.v40391, N.v40391.
  unfold R.v6, N.v6.
  rewrite ?node_40390.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40392 (s : N.State) (i : N.Inputs) :
  R.v40392 (state s) (inputs i) = Zmod.unsigned (N.v40392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40392 s i)) at 1.
  unfold R.v40392, N.v40392.
  rewrite ?node_7875.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40393 (s : N.State) (i : N.Inputs) :
  R.v40393 (state s) (inputs i) = Zmod.unsigned (N.v40393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40393 s i)) at 1.
  unfold R.v40393, N.v40393.
  unfold R.v6, N.v6.
  rewrite ?node_7991.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40394 (s : N.State) (i : N.Inputs) :
  R.v40394 (state s) (inputs i) = Zmod.unsigned (N.v40394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40394 s i)) at 1.
  unfold R.v40394, N.v40394.
  unfold R.v6, N.v6.
  rewrite ?node_8027.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40395 (s : N.State) (i : N.Inputs) :
  R.v40395 (state s) (inputs i) = Zmod.unsigned (N.v40395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40395 s i)) at 1.
  unfold R.v40395, N.v40395.
  rewrite ?node_40392.
  rewrite ?node_40393.
  rewrite ?node_40394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40396 (s : N.State) (i : N.Inputs) :
  R.v40396 (state s) (inputs i) = Zmod.unsigned (N.v40396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40396 s i)) at 1.
  unfold R.v40396, N.v40396.
  rewrite ?node_40391.
  rewrite ?node_40395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40397 (s : N.State) (i : N.Inputs) :
  R.v40397 (state s) (inputs i) = Zmod.unsigned (N.v40397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40397 s i)) at 1.
  unfold R.v40397, N.v40397.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40398 (s : N.State) (i : N.Inputs) :
  R.v40398 (state s) (inputs i) = Zmod.unsigned (N.v40398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40398 s i)) at 1.
  unfold R.v40398, N.v40398.
  unfold R.v16463, N.v16463.
  rewrite !state_r622_nr_5F622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r622_nr_5F622 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40399 (s : N.State) (i : N.Inputs) :
  R.v40399 (state s) (inputs i) = Zmod.unsigned (N.v40399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40399 s i)) at 1.
  unfold R.v40399, N.v40399.
  unfold R.v6, N.v6.
  rewrite ?node_7865.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40400 (s : N.State) (i : N.Inputs) :
  R.v40400 (state s) (inputs i) = Zmod.unsigned (N.v40400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40400 s i)) at 1.
  unfold R.v40400, N.v40400.
  unfold R.v6, N.v6.
  rewrite ?node_7858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40401 (s : N.State) (i : N.Inputs) :
  R.v40401 (state s) (inputs i) = Zmod.unsigned (N.v40401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40401 s i)) at 1.
  unfold R.v40401, N.v40401.
  rewrite ?node_40399.
  rewrite ?node_40400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40402 (s : N.State) (i : N.Inputs) :
  R.v40402 (state s) (inputs i) = Zmod.unsigned (N.v40402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40402 s i)) at 1.
  unfold R.v40402, N.v40402.
  unfold R.v16484, N.v16484.
  rewrite ?node_40401.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40403 (s : N.State) (i : N.Inputs) :
  R.v40403 (state s) (inputs i) = Zmod.unsigned (N.v40403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40403 s i)) at 1.
  unfold R.v40403, N.v40403.
  rewrite ?node_40398.
  rewrite ?node_40402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40404 (s : N.State) (i : N.Inputs) :
  R.v40404 (state s) (inputs i) = Zmod.unsigned (N.v40404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40404 s i)) at 1.
  unfold R.v40404, N.v40404.
  unfold R.v6, N.v6.
  rewrite ?node_40403.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40405 (s : N.State) (i : N.Inputs) :
  R.v40405 (state s) (inputs i) = Zmod.unsigned (N.v40405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40405 s i)) at 1.
  unfold R.v40405, N.v40405.
  rewrite ?node_7867.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40406 (s : N.State) (i : N.Inputs) :
  R.v40406 (state s) (inputs i) = Zmod.unsigned (N.v40406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40406 s i)) at 1.
  unfold R.v40406, N.v40406.
  unfold R.v6, N.v6.
  rewrite ?node_7991.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40407 (s : N.State) (i : N.Inputs) :
  R.v40407 (state s) (inputs i) = Zmod.unsigned (N.v40407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40407 s i)) at 1.
  unfold R.v40407, N.v40407.
  rewrite ?node_40405.
  rewrite ?node_40406.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40408 (s : N.State) (i : N.Inputs) :
  R.v40408 (state s) (inputs i) = Zmod.unsigned (N.v40408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40408 s i)) at 1.
  unfold R.v40408, N.v40408.
  rewrite ?node_40404.
  rewrite ?node_40407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40409 (s : N.State) (i : N.Inputs) :
  R.v40409 (state s) (inputs i) = Zmod.unsigned (N.v40409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40409 s i)) at 1.
  unfold R.v40409, N.v40409.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40410 (s : N.State) (i : N.Inputs) :
  R.v40410 (state s) (inputs i) = Zmod.unsigned (N.v40410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40410 s i)) at 1.
  unfold R.v40410, N.v40410.
  rewrite ?node_7874.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40411 (s : N.State) (i : N.Inputs) :
  R.v40411 (state s) (inputs i) = Zmod.unsigned (N.v40411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40411 s i)) at 1.
  unfold R.v40411, N.v40411.
  unfold R.v6, N.v6.
  rewrite ?node_7870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40412 (s : N.State) (i : N.Inputs) :
  R.v40412 (state s) (inputs i) = Zmod.unsigned (N.v40412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40412 s i)) at 1.
  unfold R.v40412, N.v40412.
  unfold R.v6, N.v6.
  rewrite ?node_7867.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40413 (s : N.State) (i : N.Inputs) :
  R.v40413 (state s) (inputs i) = Zmod.unsigned (N.v40413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40413 s i)) at 1.
  unfold R.v40413, N.v40413.
  rewrite ?node_40411.
  rewrite ?node_40412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40414 (s : N.State) (i : N.Inputs) :
  R.v40414 (state s) (inputs i) = Zmod.unsigned (N.v40414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40414 s i)) at 1.
  unfold R.v40414, N.v40414.
  unfold R.v16484, N.v16484.
  rewrite ?node_40413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40415 (s : N.State) (i : N.Inputs) :
  R.v40415 (state s) (inputs i) = Zmod.unsigned (N.v40415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40415 s i)) at 1.
  unfold R.v40415, N.v40415.
  rewrite ?node_40410.
  rewrite ?node_40414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40416 (s : N.State) (i : N.Inputs) :
  R.v40416 (state s) (inputs i) = Zmod.unsigned (N.v40416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40416 s i)) at 1.
  unfold R.v40416, N.v40416.
  unfold R.v6, N.v6.
  rewrite ?node_40415.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40417 (s : N.State) (i : N.Inputs) :
  R.v40417 (state s) (inputs i) = Zmod.unsigned (N.v40417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40417 s i)) at 1.
  unfold R.v40417, N.v40417.
  rewrite ?node_7875.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40418 (s : N.State) (i : N.Inputs) :
  R.v40418 (state s) (inputs i) = Zmod.unsigned (N.v40418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40418 s i)) at 1.
  unfold R.v40418, N.v40418.
  unfold R.v6, N.v6.
  rewrite ?node_8027.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40419 (s : N.State) (i : N.Inputs) :
  R.v40419 (state s) (inputs i) = Zmod.unsigned (N.v40419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40419 s i)) at 1.
  unfold R.v40419, N.v40419.
  rewrite ?node_40417.
  rewrite ?node_40418.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40420 (s : N.State) (i : N.Inputs) :
  R.v40420 (state s) (inputs i) = Zmod.unsigned (N.v40420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40420 s i)) at 1.
  unfold R.v40420, N.v40420.
  rewrite ?node_40416.
  rewrite ?node_40419.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40421 (s : N.State) (i : N.Inputs) :
  R.v40421 (state s) (inputs i) = Zmod.unsigned (N.v40421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40421 s i)) at 1.
  unfold R.v40421, N.v40421.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40422 (s : N.State) (i : N.Inputs) :
  R.v40422 (state s) (inputs i) = Zmod.unsigned (N.v40422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40422 s i)) at 1.
  unfold R.v40422, N.v40422.
  rewrite ?node_7894.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40423 (s : N.State) (i : N.Inputs) :
  R.v40423 (state s) (inputs i) = Zmod.unsigned (N.v40423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40423 s i)) at 1.
  unfold R.v40423, N.v40423.
  rewrite ?node_7890.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40424 (s : N.State) (i : N.Inputs) :
  R.v40424 (state s) (inputs i) = Zmod.unsigned (N.v40424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40424 s i)) at 1.
  unfold R.v40424, N.v40424.
  rewrite ?node_7886.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40425 (s : N.State) (i : N.Inputs) :
  R.v40425 (state s) (inputs i) = Zmod.unsigned (N.v40425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40425 s i)) at 1.
  unfold R.v40425, N.v40425.
  unfold R.v6, N.v6.
  rewrite ?node_7882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40426 (s : N.State) (i : N.Inputs) :
  R.v40426 (state s) (inputs i) = Zmod.unsigned (N.v40426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40426 s i)) at 1.
  unfold R.v40426, N.v40426.
  unfold R.v6, N.v6.
  rewrite ?node_7879.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40427 (s : N.State) (i : N.Inputs) :
  R.v40427 (state s) (inputs i) = Zmod.unsigned (N.v40427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40427 s i)) at 1.
  unfold R.v40427, N.v40427.
  rewrite ?node_40425.
  rewrite ?node_40426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40428 (s : N.State) (i : N.Inputs) :
  R.v40428 (state s) (inputs i) = Zmod.unsigned (N.v40428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40428 s i)) at 1.
  unfold R.v40428, N.v40428.
  unfold R.v16484, N.v16484.
  rewrite ?node_40427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40429 (s : N.State) (i : N.Inputs) :
  R.v40429 (state s) (inputs i) = Zmod.unsigned (N.v40429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40429 s i)) at 1.
  unfold R.v40429, N.v40429.
  rewrite ?node_40422.
  rewrite ?node_40423.
  rewrite ?node_40424.
  rewrite ?node_40428.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40430 (s : N.State) (i : N.Inputs) :
  R.v40430 (state s) (inputs i) = Zmod.unsigned (N.v40430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40430 s i)) at 1.
  unfold R.v40430, N.v40430.
  unfold R.v6, N.v6.
  rewrite ?node_40429.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40431 (s : N.State) (i : N.Inputs) :
  R.v40431 (state s) (inputs i) = Zmod.unsigned (N.v40431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40431 s i)) at 1.
  unfold R.v40431, N.v40431.
  rewrite ?node_7895.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40432 (s : N.State) (i : N.Inputs) :
  R.v40432 (state s) (inputs i) = Zmod.unsigned (N.v40432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40432 s i)) at 1.
  unfold R.v40432, N.v40432.
  unfold R.v6, N.v6.
  rewrite ?node_8011.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40433 (s : N.State) (i : N.Inputs) :
  R.v40433 (state s) (inputs i) = Zmod.unsigned (N.v40433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40433 s i)) at 1.
  unfold R.v40433, N.v40433.
  unfold R.v6, N.v6.
  rewrite ?node_8031.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40434 (s : N.State) (i : N.Inputs) :
  R.v40434 (state s) (inputs i) = Zmod.unsigned (N.v40434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40434 s i)) at 1.
  unfold R.v40434, N.v40434.
  rewrite ?node_40431.
  rewrite ?node_40432.
  rewrite ?node_40433.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40435 (s : N.State) (i : N.Inputs) :
  R.v40435 (state s) (inputs i) = Zmod.unsigned (N.v40435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40435 s i)) at 1.
  unfold R.v40435, N.v40435.
  rewrite ?node_40430.
  rewrite ?node_40434.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40436 (s : N.State) (i : N.Inputs) :
  R.v40436 (state s) (inputs i) = Zmod.unsigned (N.v40436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40436 s i)) at 1.
  unfold R.v40436, N.v40436.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40437 (s : N.State) (i : N.Inputs) :
  R.v40437 (state s) (inputs i) = Zmod.unsigned (N.v40437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40437 s i)) at 1.
  unfold R.v40437, N.v40437.
  rewrite ?node_7886.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40438 (s : N.State) (i : N.Inputs) :
  R.v40438 (state s) (inputs i) = Zmod.unsigned (N.v40438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40438 s i)) at 1.
  unfold R.v40438, N.v40438.
  unfold R.v6, N.v6.
  rewrite ?node_7882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40439 (s : N.State) (i : N.Inputs) :
  R.v40439 (state s) (inputs i) = Zmod.unsigned (N.v40439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40439 s i)) at 1.
  unfold R.v40439, N.v40439.
  unfold R.v6, N.v6.
  rewrite ?node_7879.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40440 (s : N.State) (i : N.Inputs) :
  R.v40440 (state s) (inputs i) = Zmod.unsigned (N.v40440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40440 s i)) at 1.
  unfold R.v40440, N.v40440.
  rewrite ?node_40438.
  rewrite ?node_40439.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40441 (s : N.State) (i : N.Inputs) :
  R.v40441 (state s) (inputs i) = Zmod.unsigned (N.v40441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40441 s i)) at 1.
  unfold R.v40441, N.v40441.
  unfold R.v16484, N.v16484.
  rewrite ?node_40440.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40442 (s : N.State) (i : N.Inputs) :
  R.v40442 (state s) (inputs i) = Zmod.unsigned (N.v40442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40442 s i)) at 1.
  unfold R.v40442, N.v40442.
  rewrite ?node_40437.
  rewrite ?node_40441.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40443 (s : N.State) (i : N.Inputs) :
  R.v40443 (state s) (inputs i) = Zmod.unsigned (N.v40443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40443 s i)) at 1.
  unfold R.v40443, N.v40443.
  unfold R.v6, N.v6.
  rewrite ?node_40442.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40444 (s : N.State) (i : N.Inputs) :
  R.v40444 (state s) (inputs i) = Zmod.unsigned (N.v40444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40444 s i)) at 1.
  unfold R.v40444, N.v40444.
  rewrite ?node_7887.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40445 (s : N.State) (i : N.Inputs) :
  R.v40445 (state s) (inputs i) = Zmod.unsigned (N.v40445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40445 s i)) at 1.
  unfold R.v40445, N.v40445.
  unfold R.v6, N.v6.
  rewrite ?node_8011.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40446 (s : N.State) (i : N.Inputs) :
  R.v40446 (state s) (inputs i) = Zmod.unsigned (N.v40446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40446 s i)) at 1.
  unfold R.v40446, N.v40446.
  rewrite ?node_40444.
  rewrite ?node_40445.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40447 (s : N.State) (i : N.Inputs) :
  R.v40447 (state s) (inputs i) = Zmod.unsigned (N.v40447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40447 s i)) at 1.
  unfold R.v40447, N.v40447.
  rewrite ?node_40443.
  rewrite ?node_40446.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40448 (s : N.State) (i : N.Inputs) :
  R.v40448 (state s) (inputs i) = Zmod.unsigned (N.v40448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40448 s i)) at 1.
  unfold R.v40448, N.v40448.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40449 (s : N.State) (i : N.Inputs) :
  R.v40449 (state s) (inputs i) = Zmod.unsigned (N.v40449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40449 s i)) at 1.
  unfold R.v40449, N.v40449.
  rewrite ?node_7894.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40450 (s : N.State) (i : N.Inputs) :
  R.v40450 (state s) (inputs i) = Zmod.unsigned (N.v40450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40450 s i)) at 1.
  unfold R.v40450, N.v40450.
  unfold R.v6, N.v6.
  rewrite ?node_7890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40451 (s : N.State) (i : N.Inputs) :
  R.v40451 (state s) (inputs i) = Zmod.unsigned (N.v40451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40451 s i)) at 1.
  unfold R.v40451, N.v40451.
  unfold R.v6, N.v6.
  rewrite ?node_7887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40452 (s : N.State) (i : N.Inputs) :
  R.v40452 (state s) (inputs i) = Zmod.unsigned (N.v40452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40452 s i)) at 1.
  unfold R.v40452, N.v40452.
  rewrite ?node_40450.
  rewrite ?node_40451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40453 (s : N.State) (i : N.Inputs) :
  R.v40453 (state s) (inputs i) = Zmod.unsigned (N.v40453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40453 s i)) at 1.
  unfold R.v40453, N.v40453.
  unfold R.v16484, N.v16484.
  rewrite ?node_40452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40454 (s : N.State) (i : N.Inputs) :
  R.v40454 (state s) (inputs i) = Zmod.unsigned (N.v40454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40454 s i)) at 1.
  unfold R.v40454, N.v40454.
  rewrite ?node_40449.
  rewrite ?node_40453.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40455 (s : N.State) (i : N.Inputs) :
  R.v40455 (state s) (inputs i) = Zmod.unsigned (N.v40455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40455 s i)) at 1.
  unfold R.v40455, N.v40455.
  unfold R.v6, N.v6.
  rewrite ?node_40454.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40456 (s : N.State) (i : N.Inputs) :
  R.v40456 (state s) (inputs i) = Zmod.unsigned (N.v40456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40456 s i)) at 1.
  unfold R.v40456, N.v40456.
  rewrite ?node_7895.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40457 (s : N.State) (i : N.Inputs) :
  R.v40457 (state s) (inputs i) = Zmod.unsigned (N.v40457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40457 s i)) at 1.
  unfold R.v40457, N.v40457.
  unfold R.v6, N.v6.
  rewrite ?node_8031.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40458 (s : N.State) (i : N.Inputs) :
  R.v40458 (state s) (inputs i) = Zmod.unsigned (N.v40458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40458 s i)) at 1.
  unfold R.v40458, N.v40458.
  rewrite ?node_40456.
  rewrite ?node_40457.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40459 (s : N.State) (i : N.Inputs) :
  R.v40459 (state s) (inputs i) = Zmod.unsigned (N.v40459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40459 s i)) at 1.
  unfold R.v40459, N.v40459.
  rewrite ?node_40455.
  rewrite ?node_40458.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40460 (s : N.State) (i : N.Inputs) :
  R.v40460 (state s) (inputs i) = Zmod.unsigned (N.v40460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40460 s i)) at 1.
  unfold R.v40460, N.v40460.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40461 (s : N.State) (i : N.Inputs) :
  R.v40461 (state s) (inputs i) = Zmod.unsigned (N.v40461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40461 s i)) at 1.
  unfold R.v40461, N.v40461.
  rewrite ?node_7967.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40462 (s : N.State) (i : N.Inputs) :
  R.v40462 (state s) (inputs i) = Zmod.unsigned (N.v40462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40462 s i)) at 1.
  unfold R.v40462, N.v40462.
  rewrite ?node_7963.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40463 (s : N.State) (i : N.Inputs) :
  R.v40463 (state s) (inputs i) = Zmod.unsigned (N.v40463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40463 s i)) at 1.
  unfold R.v40463, N.v40463.
  rewrite ?node_7955.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40464 (s : N.State) (i : N.Inputs) :
  R.v40464 (state s) (inputs i) = Zmod.unsigned (N.v40464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40464 s i)) at 1.
  unfold R.v40464, N.v40464.
  unfold R.v6, N.v6.
  rewrite ?node_7947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40465 (s : N.State) (i : N.Inputs) :
  R.v40465 (state s) (inputs i) = Zmod.unsigned (N.v40465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40465 s i)) at 1.
  unfold R.v40465, N.v40465.
  unfold R.v6, N.v6.
  rewrite ?node_7940.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40466 (s : N.State) (i : N.Inputs) :
  R.v40466 (state s) (inputs i) = Zmod.unsigned (N.v40466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40466 s i)) at 1.
  unfold R.v40466, N.v40466.
  rewrite ?node_40464.
  rewrite ?node_40465.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40467 (s : N.State) (i : N.Inputs) :
  R.v40467 (state s) (inputs i) = Zmod.unsigned (N.v40467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40467 s i)) at 1.
  unfold R.v40467, N.v40467.
  unfold R.v16484, N.v16484.
  rewrite ?node_40466.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40468 (s : N.State) (i : N.Inputs) :
  R.v40468 (state s) (inputs i) = Zmod.unsigned (N.v40468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40468 s i)) at 1.
  unfold R.v40468, N.v40468.
  rewrite ?node_40461.
  rewrite ?node_40462.
  rewrite ?node_40463.
  rewrite ?node_40467.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40469 (s : N.State) (i : N.Inputs) :
  R.v40469 (state s) (inputs i) = Zmod.unsigned (N.v40469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40469 s i)) at 1.
  unfold R.v40469, N.v40469.
  unfold R.v6, N.v6.
  rewrite ?node_40468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40470 (s : N.State) (i : N.Inputs) :
  R.v40470 (state s) (inputs i) = Zmod.unsigned (N.v40470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40470 s i)) at 1.
  unfold R.v40470, N.v40470.
  rewrite ?node_7968.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40471 (s : N.State) (i : N.Inputs) :
  R.v40471 (state s) (inputs i) = Zmod.unsigned (N.v40471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40471 s i)) at 1.
  unfold R.v40471, N.v40471.
  unfold R.v6, N.v6.
  rewrite ?node_8086.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40472 (s : N.State) (i : N.Inputs) :
  R.v40472 (state s) (inputs i) = Zmod.unsigned (N.v40472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40472 s i)) at 1.
  unfold R.v40472, N.v40472.
  unfold R.v6, N.v6.
  rewrite ?node_8144.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40473 (s : N.State) (i : N.Inputs) :
  R.v40473 (state s) (inputs i) = Zmod.unsigned (N.v40473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40473 s i)) at 1.
  unfold R.v40473, N.v40473.
  rewrite ?node_40470.
  rewrite ?node_40471.
  rewrite ?node_40472.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40474 (s : N.State) (i : N.Inputs) :
  R.v40474 (state s) (inputs i) = Zmod.unsigned (N.v40474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40474 s i)) at 1.
  unfold R.v40474, N.v40474.
  rewrite ?node_40469.
  rewrite ?node_40473.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40475 (s : N.State) (i : N.Inputs) :
  R.v40475 (state s) (inputs i) = Zmod.unsigned (N.v40475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40475 s i)) at 1.
  unfold R.v40475, N.v40475.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40476 (s : N.State) (i : N.Inputs) :
  R.v40476 (state s) (inputs i) = Zmod.unsigned (N.v40476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40476 s i)) at 1.
  unfold R.v40476, N.v40476.
  rewrite ?node_7955.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40477 (s : N.State) (i : N.Inputs) :
  R.v40477 (state s) (inputs i) = Zmod.unsigned (N.v40477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40477 s i)) at 1.
  unfold R.v40477, N.v40477.
  unfold R.v6, N.v6.
  rewrite ?node_7947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40478 (s : N.State) (i : N.Inputs) :
  R.v40478 (state s) (inputs i) = Zmod.unsigned (N.v40478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40478 s i)) at 1.
  unfold R.v40478, N.v40478.
  unfold R.v6, N.v6.
  rewrite ?node_7940.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40479 (s : N.State) (i : N.Inputs) :
  R.v40479 (state s) (inputs i) = Zmod.unsigned (N.v40479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40479 s i)) at 1.
  unfold R.v40479, N.v40479.
  rewrite ?node_40477.
  rewrite ?node_40478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40480 (s : N.State) (i : N.Inputs) :
  R.v40480 (state s) (inputs i) = Zmod.unsigned (N.v40480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40480 s i)) at 1.
  unfold R.v40480, N.v40480.
  unfold R.v16484, N.v16484.
  rewrite ?node_40479.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40481 (s : N.State) (i : N.Inputs) :
  R.v40481 (state s) (inputs i) = Zmod.unsigned (N.v40481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40481 s i)) at 1.
  unfold R.v40481, N.v40481.
  rewrite ?node_40476.
  rewrite ?node_40480.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40482 (s : N.State) (i : N.Inputs) :
  R.v40482 (state s) (inputs i) = Zmod.unsigned (N.v40482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40482 s i)) at 1.
  unfold R.v40482, N.v40482.
  unfold R.v6, N.v6.
  rewrite ?node_40481.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40483 (s : N.State) (i : N.Inputs) :
  R.v40483 (state s) (inputs i) = Zmod.unsigned (N.v40483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40483 s i)) at 1.
  unfold R.v40483, N.v40483.
  rewrite ?node_7956.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40484 (s : N.State) (i : N.Inputs) :
  R.v40484 (state s) (inputs i) = Zmod.unsigned (N.v40484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40484 s i)) at 1.
  unfold R.v40484, N.v40484.
  unfold R.v6, N.v6.
  rewrite ?node_8086.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40485 (s : N.State) (i : N.Inputs) :
  R.v40485 (state s) (inputs i) = Zmod.unsigned (N.v40485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40485 s i)) at 1.
  unfold R.v40485, N.v40485.
  rewrite ?node_40483.
  rewrite ?node_40484.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40486 (s : N.State) (i : N.Inputs) :
  R.v40486 (state s) (inputs i) = Zmod.unsigned (N.v40486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40486 s i)) at 1.
  unfold R.v40486, N.v40486.
  rewrite ?node_40482.
  rewrite ?node_40485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40487 (s : N.State) (i : N.Inputs) :
  R.v40487 (state s) (inputs i) = Zmod.unsigned (N.v40487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40487 s i)) at 1.
  unfold R.v40487, N.v40487.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40488 (s : N.State) (i : N.Inputs) :
  R.v40488 (state s) (inputs i) = Zmod.unsigned (N.v40488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40488 s i)) at 1.
  unfold R.v40488, N.v40488.
  rewrite ?node_7967.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40489 (s : N.State) (i : N.Inputs) :
  R.v40489 (state s) (inputs i) = Zmod.unsigned (N.v40489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40489 s i)) at 1.
  unfold R.v40489, N.v40489.
  unfold R.v6, N.v6.
  rewrite ?node_7963.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40490 (s : N.State) (i : N.Inputs) :
  R.v40490 (state s) (inputs i) = Zmod.unsigned (N.v40490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40490 s i)) at 1.
  unfold R.v40490, N.v40490.
  unfold R.v6, N.v6.
  rewrite ?node_7956.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40491 (s : N.State) (i : N.Inputs) :
  R.v40491 (state s) (inputs i) = Zmod.unsigned (N.v40491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40491 s i)) at 1.
  unfold R.v40491, N.v40491.
  rewrite ?node_40489.
  rewrite ?node_40490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40492 (s : N.State) (i : N.Inputs) :
  R.v40492 (state s) (inputs i) = Zmod.unsigned (N.v40492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40492 s i)) at 1.
  unfold R.v40492, N.v40492.
  unfold R.v16484, N.v16484.
  rewrite ?node_40491.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40493 (s : N.State) (i : N.Inputs) :
  R.v40493 (state s) (inputs i) = Zmod.unsigned (N.v40493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40493 s i)) at 1.
  unfold R.v40493, N.v40493.
  rewrite ?node_40488.
  rewrite ?node_40492.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40494 (s : N.State) (i : N.Inputs) :
  R.v40494 (state s) (inputs i) = Zmod.unsigned (N.v40494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40494 s i)) at 1.
  unfold R.v40494, N.v40494.
  unfold R.v6, N.v6.
  rewrite ?node_40493.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40495 (s : N.State) (i : N.Inputs) :
  R.v40495 (state s) (inputs i) = Zmod.unsigned (N.v40495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40495 s i)) at 1.
  unfold R.v40495, N.v40495.
  rewrite ?node_7968.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40496 (s : N.State) (i : N.Inputs) :
  R.v40496 (state s) (inputs i) = Zmod.unsigned (N.v40496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40496 s i)) at 1.
  unfold R.v40496, N.v40496.
  unfold R.v6, N.v6.
  rewrite ?node_8144.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40497 (s : N.State) (i : N.Inputs) :
  R.v40497 (state s) (inputs i) = Zmod.unsigned (N.v40497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40497 s i)) at 1.
  unfold R.v40497, N.v40497.
  rewrite ?node_40495.
  rewrite ?node_40496.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40498 (s : N.State) (i : N.Inputs) :
  R.v40498 (state s) (inputs i) = Zmod.unsigned (N.v40498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40498 s i)) at 1.
  unfold R.v40498, N.v40498.
  rewrite ?node_40494.
  rewrite ?node_40497.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40499 (s : N.State) (i : N.Inputs) :
  R.v40499 (state s) (inputs i) = Zmod.unsigned (N.v40499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40499 s i)) at 1.
  unfold R.v40499, N.v40499.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40500 (s : N.State) (i : N.Inputs) :
  R.v40500 (state s) (inputs i) = Zmod.unsigned (N.v40500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40500 s i)) at 1.
  unfold R.v40500, N.v40500.
  rewrite ?node_7991.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40501 (s : N.State) (i : N.Inputs) :
  R.v40501 (state s) (inputs i) = Zmod.unsigned (N.v40501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40501 s i)) at 1.
  unfold R.v40501, N.v40501.
  rewrite ?node_7987.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40502 (s : N.State) (i : N.Inputs) :
  R.v40502 (state s) (inputs i) = Zmod.unsigned (N.v40502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40502 s i)) at 1.
  unfold R.v40502, N.v40502.
  unfold R.v16463, N.v16463.
  rewrite !state_r647_nr_5F647.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r647_nr_5F647 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40503 (s : N.State) (i : N.Inputs) :
  R.v40503 (state s) (inputs i) = Zmod.unsigned (N.v40503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40503 s i)) at 1.
  unfold R.v40503, N.v40503.
  unfold R.v6, N.v6.
  rewrite ?node_7982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40504 (s : N.State) (i : N.Inputs) :
  R.v40504 (state s) (inputs i) = Zmod.unsigned (N.v40504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40504 s i)) at 1.
  unfold R.v40504, N.v40504.
  unfold R.v6, N.v6.
  rewrite ?node_7975.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40505 (s : N.State) (i : N.Inputs) :
  R.v40505 (state s) (inputs i) = Zmod.unsigned (N.v40505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40505 s i)) at 1.
  unfold R.v40505, N.v40505.
  rewrite ?node_40503.
  rewrite ?node_40504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40506 (s : N.State) (i : N.Inputs) :
  R.v40506 (state s) (inputs i) = Zmod.unsigned (N.v40506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40506 s i)) at 1.
  unfold R.v40506, N.v40506.
  unfold R.v16484, N.v16484.
  rewrite ?node_40505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40507 (s : N.State) (i : N.Inputs) :
  R.v40507 (state s) (inputs i) = Zmod.unsigned (N.v40507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40507 s i)) at 1.
  unfold R.v40507, N.v40507.
  rewrite ?node_40500.
  rewrite ?node_40501.
  rewrite ?node_40502.
  rewrite ?node_40506.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40508 (s : N.State) (i : N.Inputs) :
  R.v40508 (state s) (inputs i) = Zmod.unsigned (N.v40508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40508 s i)) at 1.
  unfold R.v40508, N.v40508.
  unfold R.v6, N.v6.
  rewrite ?node_40507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40509 (s : N.State) (i : N.Inputs) :
  R.v40509 (state s) (inputs i) = Zmod.unsigned (N.v40509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40509 s i)) at 1.
  unfold R.v40509, N.v40509.
  rewrite ?node_7992.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40510 (s : N.State) (i : N.Inputs) :
  R.v40510 (state s) (inputs i) = Zmod.unsigned (N.v40510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40510 s i)) at 1.
  unfold R.v40510, N.v40510.
  unfold R.v6, N.v6.
  rewrite ?node_8111.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40511 (s : N.State) (i : N.Inputs) :
  R.v40511 (state s) (inputs i) = Zmod.unsigned (N.v40511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40511 s i)) at 1.
  unfold R.v40511, N.v40511.
  unfold R.v6, N.v6.
  rewrite ?node_8147.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40512 (s : N.State) (i : N.Inputs) :
  R.v40512 (state s) (inputs i) = Zmod.unsigned (N.v40512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40512 s i)) at 1.
  unfold R.v40512, N.v40512.
  rewrite ?node_40509.
  rewrite ?node_40510.
  rewrite ?node_40511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40513 (s : N.State) (i : N.Inputs) :
  R.v40513 (state s) (inputs i) = Zmod.unsigned (N.v40513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40513 s i)) at 1.
  unfold R.v40513, N.v40513.
  rewrite ?node_40508.
  rewrite ?node_40512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40514 (s : N.State) (i : N.Inputs) :
  R.v40514 (state s) (inputs i) = Zmod.unsigned (N.v40514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40514 s i)) at 1.
  unfold R.v40514, N.v40514.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40515 (s : N.State) (i : N.Inputs) :
  R.v40515 (state s) (inputs i) = Zmod.unsigned (N.v40515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40515 s i)) at 1.
  unfold R.v40515, N.v40515.
  unfold R.v16463, N.v16463.
  rewrite !state_r647_nr_5F647.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r647_nr_5F647 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40516 (s : N.State) (i : N.Inputs) :
  R.v40516 (state s) (inputs i) = Zmod.unsigned (N.v40516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40516 s i)) at 1.
  unfold R.v40516, N.v40516.
  unfold R.v6, N.v6.
  rewrite ?node_7982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40517 (s : N.State) (i : N.Inputs) :
  R.v40517 (state s) (inputs i) = Zmod.unsigned (N.v40517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40517 s i)) at 1.
  unfold R.v40517, N.v40517.
  unfold R.v6, N.v6.
  rewrite ?node_7975.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40518 (s : N.State) (i : N.Inputs) :
  R.v40518 (state s) (inputs i) = Zmod.unsigned (N.v40518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40518 s i)) at 1.
  unfold R.v40518, N.v40518.
  rewrite ?node_40516.
  rewrite ?node_40517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40519 (s : N.State) (i : N.Inputs) :
  R.v40519 (state s) (inputs i) = Zmod.unsigned (N.v40519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40519 s i)) at 1.
  unfold R.v40519, N.v40519.
  unfold R.v16484, N.v16484.
  rewrite ?node_40518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40520 (s : N.State) (i : N.Inputs) :
  R.v40520 (state s) (inputs i) = Zmod.unsigned (N.v40520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40520 s i)) at 1.
  unfold R.v40520, N.v40520.
  rewrite ?node_40515.
  rewrite ?node_40519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40521 (s : N.State) (i : N.Inputs) :
  R.v40521 (state s) (inputs i) = Zmod.unsigned (N.v40521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40521 s i)) at 1.
  unfold R.v40521, N.v40521.
  unfold R.v6, N.v6.
  rewrite ?node_40520.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40522 (s : N.State) (i : N.Inputs) :
  R.v40522 (state s) (inputs i) = Zmod.unsigned (N.v40522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40522 s i)) at 1.
  unfold R.v40522, N.v40522.
  rewrite ?node_7984.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40523 (s : N.State) (i : N.Inputs) :
  R.v40523 (state s) (inputs i) = Zmod.unsigned (N.v40523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40523 s i)) at 1.
  unfold R.v40523, N.v40523.
  unfold R.v6, N.v6.
  rewrite ?node_8111.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40524 (s : N.State) (i : N.Inputs) :
  R.v40524 (state s) (inputs i) = Zmod.unsigned (N.v40524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40524 s i)) at 1.
  unfold R.v40524, N.v40524.
  rewrite ?node_40522.
  rewrite ?node_40523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40525 (s : N.State) (i : N.Inputs) :
  R.v40525 (state s) (inputs i) = Zmod.unsigned (N.v40525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40525 s i)) at 1.
  unfold R.v40525, N.v40525.
  rewrite ?node_40521.
  rewrite ?node_40524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40526 (s : N.State) (i : N.Inputs) :
  R.v40526 (state s) (inputs i) = Zmod.unsigned (N.v40526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40526 s i)) at 1.
  unfold R.v40526, N.v40526.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40527 (s : N.State) (i : N.Inputs) :
  R.v40527 (state s) (inputs i) = Zmod.unsigned (N.v40527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40527 s i)) at 1.
  unfold R.v40527, N.v40527.
  rewrite ?node_7991.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40528 (s : N.State) (i : N.Inputs) :
  R.v40528 (state s) (inputs i) = Zmod.unsigned (N.v40528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40528 s i)) at 1.
  unfold R.v40528, N.v40528.
  unfold R.v6, N.v6.
  rewrite ?node_7987.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40529 (s : N.State) (i : N.Inputs) :
  R.v40529 (state s) (inputs i) = Zmod.unsigned (N.v40529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40529 s i)) at 1.
  unfold R.v40529, N.v40529.
  unfold R.v6, N.v6.
  rewrite ?node_7984.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40530 (s : N.State) (i : N.Inputs) :
  R.v40530 (state s) (inputs i) = Zmod.unsigned (N.v40530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40530 s i)) at 1.
  unfold R.v40530, N.v40530.
  rewrite ?node_40528.
  rewrite ?node_40529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40531 (s : N.State) (i : N.Inputs) :
  R.v40531 (state s) (inputs i) = Zmod.unsigned (N.v40531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40531 s i)) at 1.
  unfold R.v40531, N.v40531.
  unfold R.v16484, N.v16484.
  rewrite ?node_40530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40532 (s : N.State) (i : N.Inputs) :
  R.v40532 (state s) (inputs i) = Zmod.unsigned (N.v40532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40532 s i)) at 1.
  unfold R.v40532, N.v40532.
  rewrite ?node_40527.
  rewrite ?node_40531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40533 (s : N.State) (i : N.Inputs) :
  R.v40533 (state s) (inputs i) = Zmod.unsigned (N.v40533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40533 s i)) at 1.
  unfold R.v40533, N.v40533.
  unfold R.v6, N.v6.
  rewrite ?node_40532.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40534 (s : N.State) (i : N.Inputs) :
  R.v40534 (state s) (inputs i) = Zmod.unsigned (N.v40534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40534 s i)) at 1.
  unfold R.v40534, N.v40534.
  rewrite ?node_7992.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40535 (s : N.State) (i : N.Inputs) :
  R.v40535 (state s) (inputs i) = Zmod.unsigned (N.v40535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40535 s i)) at 1.
  unfold R.v40535, N.v40535.
  unfold R.v6, N.v6.
  rewrite ?node_8147.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40536 (s : N.State) (i : N.Inputs) :
  R.v40536 (state s) (inputs i) = Zmod.unsigned (N.v40536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40536 s i)) at 1.
  unfold R.v40536, N.v40536.
  rewrite ?node_40534.
  rewrite ?node_40535.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40537 (s : N.State) (i : N.Inputs) :
  R.v40537 (state s) (inputs i) = Zmod.unsigned (N.v40537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40537 s i)) at 1.
  unfold R.v40537, N.v40537.
  rewrite ?node_40533.
  rewrite ?node_40536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40538 (s : N.State) (i : N.Inputs) :
  R.v40538 (state s) (inputs i) = Zmod.unsigned (N.v40538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40538 s i)) at 1.
  unfold R.v40538, N.v40538.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40539 (s : N.State) (i : N.Inputs) :
  R.v40539 (state s) (inputs i) = Zmod.unsigned (N.v40539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40539 s i)) at 1.
  unfold R.v40539, N.v40539.
  rewrite ?node_8011.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40540 (s : N.State) (i : N.Inputs) :
  R.v40540 (state s) (inputs i) = Zmod.unsigned (N.v40540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40540 s i)) at 1.
  unfold R.v40540, N.v40540.
  rewrite ?node_8007.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40541 (s : N.State) (i : N.Inputs) :
  R.v40541 (state s) (inputs i) = Zmod.unsigned (N.v40541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40541 s i)) at 1.
  unfold R.v40541, N.v40541.
  rewrite ?node_8003.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40542 (s : N.State) (i : N.Inputs) :
  R.v40542 (state s) (inputs i) = Zmod.unsigned (N.v40542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40542 s i)) at 1.
  unfold R.v40542, N.v40542.
  unfold R.v6, N.v6.
  rewrite ?node_7999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40543 (s : N.State) (i : N.Inputs) :
  R.v40543 (state s) (inputs i) = Zmod.unsigned (N.v40543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40543 s i)) at 1.
  unfold R.v40543, N.v40543.
  unfold R.v6, N.v6.
  rewrite ?node_7996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40544 (s : N.State) (i : N.Inputs) :
  R.v40544 (state s) (inputs i) = Zmod.unsigned (N.v40544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40544 s i)) at 1.
  unfold R.v40544, N.v40544.
  rewrite ?node_40542.
  rewrite ?node_40543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40545 (s : N.State) (i : N.Inputs) :
  R.v40545 (state s) (inputs i) = Zmod.unsigned (N.v40545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40545 s i)) at 1.
  unfold R.v40545, N.v40545.
  unfold R.v16484, N.v16484.
  rewrite ?node_40544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40546 (s : N.State) (i : N.Inputs) :
  R.v40546 (state s) (inputs i) = Zmod.unsigned (N.v40546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40546 s i)) at 1.
  unfold R.v40546, N.v40546.
  rewrite ?node_40539.
  rewrite ?node_40540.
  rewrite ?node_40541.
  rewrite ?node_40545.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40547 (s : N.State) (i : N.Inputs) :
  R.v40547 (state s) (inputs i) = Zmod.unsigned (N.v40547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40547 s i)) at 1.
  unfold R.v40547, N.v40547.
  unfold R.v6, N.v6.
  rewrite ?node_40546.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40548 (s : N.State) (i : N.Inputs) :
  R.v40548 (state s) (inputs i) = Zmod.unsigned (N.v40548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40548 s i)) at 1.
  unfold R.v40548, N.v40548.
  rewrite ?node_8012.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40549 (s : N.State) (i : N.Inputs) :
  R.v40549 (state s) (inputs i) = Zmod.unsigned (N.v40549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40549 s i)) at 1.
  unfold R.v40549, N.v40549.
  unfold R.v6, N.v6.
  rewrite ?node_8131.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40550 (s : N.State) (i : N.Inputs) :
  R.v40550 (state s) (inputs i) = Zmod.unsigned (N.v40550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40550 s i)) at 1.
  unfold R.v40550, N.v40550.
  unfold R.v6, N.v6.
  rewrite ?node_8151.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40551 (s : N.State) (i : N.Inputs) :
  R.v40551 (state s) (inputs i) = Zmod.unsigned (N.v40551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40551 s i)) at 1.
  unfold R.v40551, N.v40551.
  rewrite ?node_40548.
  rewrite ?node_40549.
  rewrite ?node_40550.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40552 (s : N.State) (i : N.Inputs) :
  R.v40552 (state s) (inputs i) = Zmod.unsigned (N.v40552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40552 s i)) at 1.
  unfold R.v40552, N.v40552.
  rewrite ?node_40547.
  rewrite ?node_40551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40553 (s : N.State) (i : N.Inputs) :
  R.v40553 (state s) (inputs i) = Zmod.unsigned (N.v40553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40553 s i)) at 1.
  unfold R.v40553, N.v40553.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40554 (s : N.State) (i : N.Inputs) :
  R.v40554 (state s) (inputs i) = Zmod.unsigned (N.v40554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40554 s i)) at 1.
  unfold R.v40554, N.v40554.
  rewrite ?node_8003.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40555 (s : N.State) (i : N.Inputs) :
  R.v40555 (state s) (inputs i) = Zmod.unsigned (N.v40555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40555 s i)) at 1.
  unfold R.v40555, N.v40555.
  unfold R.v6, N.v6.
  rewrite ?node_7999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40556 (s : N.State) (i : N.Inputs) :
  R.v40556 (state s) (inputs i) = Zmod.unsigned (N.v40556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40556 s i)) at 1.
  unfold R.v40556, N.v40556.
  unfold R.v6, N.v6.
  rewrite ?node_7996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40557 (s : N.State) (i : N.Inputs) :
  R.v40557 (state s) (inputs i) = Zmod.unsigned (N.v40557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40557 s i)) at 1.
  unfold R.v40557, N.v40557.
  rewrite ?node_40555.
  rewrite ?node_40556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40558 (s : N.State) (i : N.Inputs) :
  R.v40558 (state s) (inputs i) = Zmod.unsigned (N.v40558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40558 s i)) at 1.
  unfold R.v40558, N.v40558.
  unfold R.v16484, N.v16484.
  rewrite ?node_40557.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40559 (s : N.State) (i : N.Inputs) :
  R.v40559 (state s) (inputs i) = Zmod.unsigned (N.v40559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40559 s i)) at 1.
  unfold R.v40559, N.v40559.
  rewrite ?node_40554.
  rewrite ?node_40558.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40560 (s : N.State) (i : N.Inputs) :
  R.v40560 (state s) (inputs i) = Zmod.unsigned (N.v40560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40560 s i)) at 1.
  unfold R.v40560, N.v40560.
  unfold R.v6, N.v6.
  rewrite ?node_40559.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40561 (s : N.State) (i : N.Inputs) :
  R.v40561 (state s) (inputs i) = Zmod.unsigned (N.v40561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40561 s i)) at 1.
  unfold R.v40561, N.v40561.
  rewrite ?node_8004.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40562 (s : N.State) (i : N.Inputs) :
  R.v40562 (state s) (inputs i) = Zmod.unsigned (N.v40562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40562 s i)) at 1.
  unfold R.v40562, N.v40562.
  unfold R.v6, N.v6.
  rewrite ?node_8131.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40563 (s : N.State) (i : N.Inputs) :
  R.v40563 (state s) (inputs i) = Zmod.unsigned (N.v40563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40563 s i)) at 1.
  unfold R.v40563, N.v40563.
  rewrite ?node_40561.
  rewrite ?node_40562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40564 (s : N.State) (i : N.Inputs) :
  R.v40564 (state s) (inputs i) = Zmod.unsigned (N.v40564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40564 s i)) at 1.
  unfold R.v40564, N.v40564.
  rewrite ?node_40560.
  rewrite ?node_40563.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40565 (s : N.State) (i : N.Inputs) :
  R.v40565 (state s) (inputs i) = Zmod.unsigned (N.v40565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40565 s i)) at 1.
  unfold R.v40565, N.v40565.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40566 (s : N.State) (i : N.Inputs) :
  R.v40566 (state s) (inputs i) = Zmod.unsigned (N.v40566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40566 s i)) at 1.
  unfold R.v40566, N.v40566.
  rewrite ?node_8011.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40567 (s : N.State) (i : N.Inputs) :
  R.v40567 (state s) (inputs i) = Zmod.unsigned (N.v40567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40567 s i)) at 1.
  unfold R.v40567, N.v40567.
  unfold R.v6, N.v6.
  rewrite ?node_8007.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40568 (s : N.State) (i : N.Inputs) :
  R.v40568 (state s) (inputs i) = Zmod.unsigned (N.v40568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40568 s i)) at 1.
  unfold R.v40568, N.v40568.
  unfold R.v6, N.v6.
  rewrite ?node_8004.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40569 (s : N.State) (i : N.Inputs) :
  R.v40569 (state s) (inputs i) = Zmod.unsigned (N.v40569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40569 s i)) at 1.
  unfold R.v40569, N.v40569.
  rewrite ?node_40567.
  rewrite ?node_40568.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40570 (s : N.State) (i : N.Inputs) :
  R.v40570 (state s) (inputs i) = Zmod.unsigned (N.v40570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40570 s i)) at 1.
  unfold R.v40570, N.v40570.
  unfold R.v16484, N.v16484.
  rewrite ?node_40569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40571 (s : N.State) (i : N.Inputs) :
  R.v40571 (state s) (inputs i) = Zmod.unsigned (N.v40571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40571 s i)) at 1.
  unfold R.v40571, N.v40571.
  rewrite ?node_40566.
  rewrite ?node_40570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40572 (s : N.State) (i : N.Inputs) :
  R.v40572 (state s) (inputs i) = Zmod.unsigned (N.v40572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40572 s i)) at 1.
  unfold R.v40572, N.v40572.
  unfold R.v6, N.v6.
  rewrite ?node_40571.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40573 (s : N.State) (i : N.Inputs) :
  R.v40573 (state s) (inputs i) = Zmod.unsigned (N.v40573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40573 s i)) at 1.
  unfold R.v40573, N.v40573.
  rewrite ?node_8012.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40574 (s : N.State) (i : N.Inputs) :
  R.v40574 (state s) (inputs i) = Zmod.unsigned (N.v40574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40574 s i)) at 1.
  unfold R.v40574, N.v40574.
  unfold R.v6, N.v6.
  rewrite ?node_8151.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40575 (s : N.State) (i : N.Inputs) :
  R.v40575 (state s) (inputs i) = Zmod.unsigned (N.v40575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40575 s i)) at 1.
  unfold R.v40575, N.v40575.
  rewrite ?node_40573.
  rewrite ?node_40574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40576 (s : N.State) (i : N.Inputs) :
  R.v40576 (state s) (inputs i) = Zmod.unsigned (N.v40576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40576 s i)) at 1.
  unfold R.v40576, N.v40576.
  rewrite ?node_40572.
  rewrite ?node_40575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40577 (s : N.State) (i : N.Inputs) :
  R.v40577 (state s) (inputs i) = Zmod.unsigned (N.v40577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40577 s i)) at 1.
  unfold R.v40577, N.v40577.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40578 (s : N.State) (i : N.Inputs) :
  R.v40578 (state s) (inputs i) = Zmod.unsigned (N.v40578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40578 s i)) at 1.
  unfold R.v40578, N.v40578.
  rewrite ?node_8086.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40579 (s : N.State) (i : N.Inputs) :
  R.v40579 (state s) (inputs i) = Zmod.unsigned (N.v40579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40579 s i)) at 1.
  unfold R.v40579, N.v40579.
  rewrite ?node_8082.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40580 (s : N.State) (i : N.Inputs) :
  R.v40580 (state s) (inputs i) = Zmod.unsigned (N.v40580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40580 s i)) at 1.
  unfold R.v40580, N.v40580.
  rewrite ?node_8074.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40581 (s : N.State) (i : N.Inputs) :
  R.v40581 (state s) (inputs i) = Zmod.unsigned (N.v40581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40581 s i)) at 1.
  unfold R.v40581, N.v40581.
  unfold R.v6, N.v6.
  rewrite ?node_8066.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40582 (s : N.State) (i : N.Inputs) :
  R.v40582 (state s) (inputs i) = Zmod.unsigned (N.v40582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40582 s i)) at 1.
  unfold R.v40582, N.v40582.
  unfold R.v6, N.v6.
  rewrite ?node_8059.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40583 (s : N.State) (i : N.Inputs) :
  R.v40583 (state s) (inputs i) = Zmod.unsigned (N.v40583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40583 s i)) at 1.
  unfold R.v40583, N.v40583.
  rewrite ?node_40581.
  rewrite ?node_40582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40584 (s : N.State) (i : N.Inputs) :
  R.v40584 (state s) (inputs i) = Zmod.unsigned (N.v40584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40584 s i)) at 1.
  unfold R.v40584, N.v40584.
  unfold R.v16484, N.v16484.
  rewrite ?node_40583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40585 (s : N.State) (i : N.Inputs) :
  R.v40585 (state s) (inputs i) = Zmod.unsigned (N.v40585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40585 s i)) at 1.
  unfold R.v40585, N.v40585.
  rewrite ?node_40578.
  rewrite ?node_40579.
  rewrite ?node_40580.
  rewrite ?node_40584.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40586 (s : N.State) (i : N.Inputs) :
  R.v40586 (state s) (inputs i) = Zmod.unsigned (N.v40586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40586 s i)) at 1.
  unfold R.v40586, N.v40586.
  unfold R.v6, N.v6.
  rewrite ?node_40585.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40587 (s : N.State) (i : N.Inputs) :
  R.v40587 (state s) (inputs i) = Zmod.unsigned (N.v40587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40587 s i)) at 1.
  unfold R.v40587, N.v40587.
  rewrite ?node_8087.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40588 (s : N.State) (i : N.Inputs) :
  R.v40588 (state s) (inputs i) = Zmod.unsigned (N.v40588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40588 s i)) at 1.
  unfold R.v40588, N.v40588.
  unfold R.v6, N.v6.
  rewrite ?node_8206.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40589 (s : N.State) (i : N.Inputs) :
  R.v40589 (state s) (inputs i) = Zmod.unsigned (N.v40589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40589 s i)) at 1.
  unfold R.v40589, N.v40589.
  unfold R.v6, N.v6.
  rewrite ?node_8266.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40590 (s : N.State) (i : N.Inputs) :
  R.v40590 (state s) (inputs i) = Zmod.unsigned (N.v40590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40590 s i)) at 1.
  unfold R.v40590, N.v40590.
  rewrite ?node_40587.
  rewrite ?node_40588.
  rewrite ?node_40589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40591 (s : N.State) (i : N.Inputs) :
  R.v40591 (state s) (inputs i) = Zmod.unsigned (N.v40591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40591 s i)) at 1.
  unfold R.v40591, N.v40591.
  rewrite ?node_40586.
  rewrite ?node_40590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40592 (s : N.State) (i : N.Inputs) :
  R.v40592 (state s) (inputs i) = Zmod.unsigned (N.v40592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40592 s i)) at 1.
  unfold R.v40592, N.v40592.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40593 (s : N.State) (i : N.Inputs) :
  R.v40593 (state s) (inputs i) = Zmod.unsigned (N.v40593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40593 s i)) at 1.
  unfold R.v40593, N.v40593.
  rewrite ?node_8074.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40594 (s : N.State) (i : N.Inputs) :
  R.v40594 (state s) (inputs i) = Zmod.unsigned (N.v40594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40594 s i)) at 1.
  unfold R.v40594, N.v40594.
  unfold R.v6, N.v6.
  rewrite ?node_8066.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40595 (s : N.State) (i : N.Inputs) :
  R.v40595 (state s) (inputs i) = Zmod.unsigned (N.v40595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40595 s i)) at 1.
  unfold R.v40595, N.v40595.
  unfold R.v6, N.v6.
  rewrite ?node_8059.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40596 (s : N.State) (i : N.Inputs) :
  R.v40596 (state s) (inputs i) = Zmod.unsigned (N.v40596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40596 s i)) at 1.
  unfold R.v40596, N.v40596.
  rewrite ?node_40594.
  rewrite ?node_40595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40597 (s : N.State) (i : N.Inputs) :
  R.v40597 (state s) (inputs i) = Zmod.unsigned (N.v40597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40597 s i)) at 1.
  unfold R.v40597, N.v40597.
  unfold R.v16484, N.v16484.
  rewrite ?node_40596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40598 (s : N.State) (i : N.Inputs) :
  R.v40598 (state s) (inputs i) = Zmod.unsigned (N.v40598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40598 s i)) at 1.
  unfold R.v40598, N.v40598.
  rewrite ?node_40593.
  rewrite ?node_40597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40599 (s : N.State) (i : N.Inputs) :
  R.v40599 (state s) (inputs i) = Zmod.unsigned (N.v40599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40599 s i)) at 1.
  unfold R.v40599, N.v40599.
  unfold R.v6, N.v6.
  rewrite ?node_40598.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40600 (s : N.State) (i : N.Inputs) :
  R.v40600 (state s) (inputs i) = Zmod.unsigned (N.v40600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40600 s i)) at 1.
  unfold R.v40600, N.v40600.
  rewrite ?node_8075.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40601 (s : N.State) (i : N.Inputs) :
  R.v40601 (state s) (inputs i) = Zmod.unsigned (N.v40601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40601 s i)) at 1.
  unfold R.v40601, N.v40601.
  unfold R.v6, N.v6.
  rewrite ?node_8206.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40602 (s : N.State) (i : N.Inputs) :
  R.v40602 (state s) (inputs i) = Zmod.unsigned (N.v40602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40602 s i)) at 1.
  unfold R.v40602, N.v40602.
  rewrite ?node_40600.
  rewrite ?node_40601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40603 (s : N.State) (i : N.Inputs) :
  R.v40603 (state s) (inputs i) = Zmod.unsigned (N.v40603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40603 s i)) at 1.
  unfold R.v40603, N.v40603.
  rewrite ?node_40599.
  rewrite ?node_40602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40604 (s : N.State) (i : N.Inputs) :
  R.v40604 (state s) (inputs i) = Zmod.unsigned (N.v40604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40604 s i)) at 1.
  unfold R.v40604, N.v40604.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40605 (s : N.State) (i : N.Inputs) :
  R.v40605 (state s) (inputs i) = Zmod.unsigned (N.v40605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40605 s i)) at 1.
  unfold R.v40605, N.v40605.
  rewrite ?node_8086.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40606 (s : N.State) (i : N.Inputs) :
  R.v40606 (state s) (inputs i) = Zmod.unsigned (N.v40606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40606 s i)) at 1.
  unfold R.v40606, N.v40606.
  unfold R.v6, N.v6.
  rewrite ?node_8082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40607 (s : N.State) (i : N.Inputs) :
  R.v40607 (state s) (inputs i) = Zmod.unsigned (N.v40607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40607 s i)) at 1.
  unfold R.v40607, N.v40607.
  unfold R.v6, N.v6.
  rewrite ?node_8075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40608 (s : N.State) (i : N.Inputs) :
  R.v40608 (state s) (inputs i) = Zmod.unsigned (N.v40608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40608 s i)) at 1.
  unfold R.v40608, N.v40608.
  rewrite ?node_40606.
  rewrite ?node_40607.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40609 (s : N.State) (i : N.Inputs) :
  R.v40609 (state s) (inputs i) = Zmod.unsigned (N.v40609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40609 s i)) at 1.
  unfold R.v40609, N.v40609.
  unfold R.v16484, N.v16484.
  rewrite ?node_40608.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40610 (s : N.State) (i : N.Inputs) :
  R.v40610 (state s) (inputs i) = Zmod.unsigned (N.v40610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40610 s i)) at 1.
  unfold R.v40610, N.v40610.
  rewrite ?node_40605.
  rewrite ?node_40609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40611 (s : N.State) (i : N.Inputs) :
  R.v40611 (state s) (inputs i) = Zmod.unsigned (N.v40611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40611 s i)) at 1.
  unfold R.v40611, N.v40611.
  unfold R.v6, N.v6.
  rewrite ?node_40610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40612 (s : N.State) (i : N.Inputs) :
  R.v40612 (state s) (inputs i) = Zmod.unsigned (N.v40612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40612 s i)) at 1.
  unfold R.v40612, N.v40612.
  rewrite ?node_8087.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40613 (s : N.State) (i : N.Inputs) :
  R.v40613 (state s) (inputs i) = Zmod.unsigned (N.v40613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40613 s i)) at 1.
  unfold R.v40613, N.v40613.
  unfold R.v6, N.v6.
  rewrite ?node_8266.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40614 (s : N.State) (i : N.Inputs) :
  R.v40614 (state s) (inputs i) = Zmod.unsigned (N.v40614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40614 s i)) at 1.
  unfold R.v40614, N.v40614.
  rewrite ?node_40612.
  rewrite ?node_40613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40615 (s : N.State) (i : N.Inputs) :
  R.v40615 (state s) (inputs i) = Zmod.unsigned (N.v40615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40615 s i)) at 1.
  unfold R.v40615, N.v40615.
  rewrite ?node_40611.
  rewrite ?node_40614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40616 (s : N.State) (i : N.Inputs) :
  R.v40616 (state s) (inputs i) = Zmod.unsigned (N.v40616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40616 s i)) at 1.
  unfold R.v40616, N.v40616.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40617 (s : N.State) (i : N.Inputs) :
  R.v40617 (state s) (inputs i) = Zmod.unsigned (N.v40617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40617 s i)) at 1.
  unfold R.v40617, N.v40617.
  rewrite ?node_8111.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40618 (s : N.State) (i : N.Inputs) :
  R.v40618 (state s) (inputs i) = Zmod.unsigned (N.v40618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40618 s i)) at 1.
  unfold R.v40618, N.v40618.
  rewrite ?node_8107.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40619 (s : N.State) (i : N.Inputs) :
  R.v40619 (state s) (inputs i) = Zmod.unsigned (N.v40619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40619 s i)) at 1.
  unfold R.v40619, N.v40619.
  rewrite ?node_8103.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40620 (s : N.State) (i : N.Inputs) :
  R.v40620 (state s) (inputs i) = Zmod.unsigned (N.v40620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40620 s i)) at 1.
  unfold R.v40620, N.v40620.
  unfold R.v6, N.v6.
  rewrite ?node_8101.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40621 (s : N.State) (i : N.Inputs) :
  R.v40621 (state s) (inputs i) = Zmod.unsigned (N.v40621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40621 s i)) at 1.
  unfold R.v40621, N.v40621.
  unfold R.v6, N.v6.
  rewrite ?node_8094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40622 (s : N.State) (i : N.Inputs) :
  R.v40622 (state s) (inputs i) = Zmod.unsigned (N.v40622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40622 s i)) at 1.
  unfold R.v40622, N.v40622.
  rewrite ?node_40620.
  rewrite ?node_40621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40623 (s : N.State) (i : N.Inputs) :
  R.v40623 (state s) (inputs i) = Zmod.unsigned (N.v40623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40623 s i)) at 1.
  unfold R.v40623, N.v40623.
  unfold R.v16484, N.v16484.
  rewrite ?node_40622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40624 (s : N.State) (i : N.Inputs) :
  R.v40624 (state s) (inputs i) = Zmod.unsigned (N.v40624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40624 s i)) at 1.
  unfold R.v40624, N.v40624.
  rewrite ?node_40617.
  rewrite ?node_40618.
  rewrite ?node_40619.
  rewrite ?node_40623.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40625 (s : N.State) (i : N.Inputs) :
  R.v40625 (state s) (inputs i) = Zmod.unsigned (N.v40625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40625 s i)) at 1.
  unfold R.v40625, N.v40625.
  unfold R.v6, N.v6.
  rewrite ?node_40624.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40626 (s : N.State) (i : N.Inputs) :
  R.v40626 (state s) (inputs i) = Zmod.unsigned (N.v40626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40626 s i)) at 1.
  unfold R.v40626, N.v40626.
  rewrite ?node_8112.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40627 (s : N.State) (i : N.Inputs) :
  R.v40627 (state s) (inputs i) = Zmod.unsigned (N.v40627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40627 s i)) at 1.
  unfold R.v40627, N.v40627.
  unfold R.v6, N.v6.
  rewrite ?node_8231.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40628 (s : N.State) (i : N.Inputs) :
  R.v40628 (state s) (inputs i) = Zmod.unsigned (N.v40628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40628 s i)) at 1.
  unfold R.v40628, N.v40628.
  unfold R.v6, N.v6.
  rewrite ?node_8269.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40629 (s : N.State) (i : N.Inputs) :
  R.v40629 (state s) (inputs i) = Zmod.unsigned (N.v40629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40629 s i)) at 1.
  unfold R.v40629, N.v40629.
  rewrite ?node_40626.
  rewrite ?node_40627.
  rewrite ?node_40628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40630 (s : N.State) (i : N.Inputs) :
  R.v40630 (state s) (inputs i) = Zmod.unsigned (N.v40630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40630 s i)) at 1.
  unfold R.v40630, N.v40630.
  rewrite ?node_40625.
  rewrite ?node_40629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40631 (s : N.State) (i : N.Inputs) :
  R.v40631 (state s) (inputs i) = Zmod.unsigned (N.v40631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40631 s i)) at 1.
  unfold R.v40631, N.v40631.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40632 (s : N.State) (i : N.Inputs) :
  R.v40632 (state s) (inputs i) = Zmod.unsigned (N.v40632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40632 s i)) at 1.
  unfold R.v40632, N.v40632.
  rewrite ?node_8103.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40633 (s : N.State) (i : N.Inputs) :
  R.v40633 (state s) (inputs i) = Zmod.unsigned (N.v40633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40633 s i)) at 1.
  unfold R.v40633, N.v40633.
  unfold R.v6, N.v6.
  rewrite ?node_8101.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40634 (s : N.State) (i : N.Inputs) :
  R.v40634 (state s) (inputs i) = Zmod.unsigned (N.v40634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40634 s i)) at 1.
  unfold R.v40634, N.v40634.
  unfold R.v6, N.v6.
  rewrite ?node_8094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40635 (s : N.State) (i : N.Inputs) :
  R.v40635 (state s) (inputs i) = Zmod.unsigned (N.v40635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40635 s i)) at 1.
  unfold R.v40635, N.v40635.
  rewrite ?node_40633.
  rewrite ?node_40634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40636 (s : N.State) (i : N.Inputs) :
  R.v40636 (state s) (inputs i) = Zmod.unsigned (N.v40636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40636 s i)) at 1.
  unfold R.v40636, N.v40636.
  unfold R.v16484, N.v16484.
  rewrite ?node_40635.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40637 (s : N.State) (i : N.Inputs) :
  R.v40637 (state s) (inputs i) = Zmod.unsigned (N.v40637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40637 s i)) at 1.
  unfold R.v40637, N.v40637.
  rewrite ?node_40632.
  rewrite ?node_40636.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40638 (s : N.State) (i : N.Inputs) :
  R.v40638 (state s) (inputs i) = Zmod.unsigned (N.v40638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40638 s i)) at 1.
  unfold R.v40638, N.v40638.
  unfold R.v6, N.v6.
  rewrite ?node_40637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40639 (s : N.State) (i : N.Inputs) :
  R.v40639 (state s) (inputs i) = Zmod.unsigned (N.v40639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40639 s i)) at 1.
  unfold R.v40639, N.v40639.
  rewrite ?node_8104.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40640 (s : N.State) (i : N.Inputs) :
  R.v40640 (state s) (inputs i) = Zmod.unsigned (N.v40640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40640 s i)) at 1.
  unfold R.v40640, N.v40640.
  unfold R.v6, N.v6.
  rewrite ?node_8231.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40641 (s : N.State) (i : N.Inputs) :
  R.v40641 (state s) (inputs i) = Zmod.unsigned (N.v40641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40641 s i)) at 1.
  unfold R.v40641, N.v40641.
  rewrite ?node_40639.
  rewrite ?node_40640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40642 (s : N.State) (i : N.Inputs) :
  R.v40642 (state s) (inputs i) = Zmod.unsigned (N.v40642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40642 s i)) at 1.
  unfold R.v40642, N.v40642.
  rewrite ?node_40638.
  rewrite ?node_40641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40643 (s : N.State) (i : N.Inputs) :
  R.v40643 (state s) (inputs i) = Zmod.unsigned (N.v40643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40643 s i)) at 1.
  unfold R.v40643, N.v40643.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40644 (s : N.State) (i : N.Inputs) :
  R.v40644 (state s) (inputs i) = Zmod.unsigned (N.v40644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40644 s i)) at 1.
  unfold R.v40644, N.v40644.
  rewrite ?node_8111.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40645 (s : N.State) (i : N.Inputs) :
  R.v40645 (state s) (inputs i) = Zmod.unsigned (N.v40645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40645 s i)) at 1.
  unfold R.v40645, N.v40645.
  unfold R.v6, N.v6.
  rewrite ?node_8107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40646 (s : N.State) (i : N.Inputs) :
  R.v40646 (state s) (inputs i) = Zmod.unsigned (N.v40646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40646 s i)) at 1.
  unfold R.v40646, N.v40646.
  unfold R.v6, N.v6.
  rewrite ?node_8104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40647 (s : N.State) (i : N.Inputs) :
  R.v40647 (state s) (inputs i) = Zmod.unsigned (N.v40647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40647 s i)) at 1.
  unfold R.v40647, N.v40647.
  rewrite ?node_40645.
  rewrite ?node_40646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40648 (s : N.State) (i : N.Inputs) :
  R.v40648 (state s) (inputs i) = Zmod.unsigned (N.v40648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40648 s i)) at 1.
  unfold R.v40648, N.v40648.
  unfold R.v16484, N.v16484.
  rewrite ?node_40647.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40649 (s : N.State) (i : N.Inputs) :
  R.v40649 (state s) (inputs i) = Zmod.unsigned (N.v40649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40649 s i)) at 1.
  unfold R.v40649, N.v40649.
  rewrite ?node_40644.
  rewrite ?node_40648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40650 (s : N.State) (i : N.Inputs) :
  R.v40650 (state s) (inputs i) = Zmod.unsigned (N.v40650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40650 s i)) at 1.
  unfold R.v40650, N.v40650.
  unfold R.v6, N.v6.
  rewrite ?node_40649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40651 (s : N.State) (i : N.Inputs) :
  R.v40651 (state s) (inputs i) = Zmod.unsigned (N.v40651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40651 s i)) at 1.
  unfold R.v40651, N.v40651.
  rewrite ?node_8112.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40652 (s : N.State) (i : N.Inputs) :
  R.v40652 (state s) (inputs i) = Zmod.unsigned (N.v40652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40652 s i)) at 1.
  unfold R.v40652, N.v40652.
  unfold R.v6, N.v6.
  rewrite ?node_8269.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40653 (s : N.State) (i : N.Inputs) :
  R.v40653 (state s) (inputs i) = Zmod.unsigned (N.v40653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40653 s i)) at 1.
  unfold R.v40653, N.v40653.
  rewrite ?node_40651.
  rewrite ?node_40652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40654 (s : N.State) (i : N.Inputs) :
  R.v40654 (state s) (inputs i) = Zmod.unsigned (N.v40654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40654 s i)) at 1.
  unfold R.v40654, N.v40654.
  rewrite ?node_40650.
  rewrite ?node_40653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40655 (s : N.State) (i : N.Inputs) :
  R.v40655 (state s) (inputs i) = Zmod.unsigned (N.v40655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40655 s i)) at 1.
  unfold R.v40655, N.v40655.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40656 (s : N.State) (i : N.Inputs) :
  R.v40656 (state s) (inputs i) = Zmod.unsigned (N.v40656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40656 s i)) at 1.
  unfold R.v40656, N.v40656.
  rewrite ?node_8131.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40657 (s : N.State) (i : N.Inputs) :
  R.v40657 (state s) (inputs i) = Zmod.unsigned (N.v40657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40657 s i)) at 1.
  unfold R.v40657, N.v40657.
  rewrite ?node_8127.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40658 (s : N.State) (i : N.Inputs) :
  R.v40658 (state s) (inputs i) = Zmod.unsigned (N.v40658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40658 s i)) at 1.
  unfold R.v40658, N.v40658.
  rewrite ?node_8123.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40659 (s : N.State) (i : N.Inputs) :
  R.v40659 (state s) (inputs i) = Zmod.unsigned (N.v40659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40659 s i)) at 1.
  unfold R.v40659, N.v40659.
  unfold R.v6, N.v6.
  rewrite ?node_8119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40660 (s : N.State) (i : N.Inputs) :
  R.v40660 (state s) (inputs i) = Zmod.unsigned (N.v40660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40660 s i)) at 1.
  unfold R.v40660, N.v40660.
  unfold R.v6, N.v6.
  rewrite ?node_8116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40661 (s : N.State) (i : N.Inputs) :
  R.v40661 (state s) (inputs i) = Zmod.unsigned (N.v40661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40661 s i)) at 1.
  unfold R.v40661, N.v40661.
  rewrite ?node_40659.
  rewrite ?node_40660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40662 (s : N.State) (i : N.Inputs) :
  R.v40662 (state s) (inputs i) = Zmod.unsigned (N.v40662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40662 s i)) at 1.
  unfold R.v40662, N.v40662.
  unfold R.v16484, N.v16484.
  rewrite ?node_40661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40663 (s : N.State) (i : N.Inputs) :
  R.v40663 (state s) (inputs i) = Zmod.unsigned (N.v40663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40663 s i)) at 1.
  unfold R.v40663, N.v40663.
  rewrite ?node_40656.
  rewrite ?node_40657.
  rewrite ?node_40658.
  rewrite ?node_40662.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40664 (s : N.State) (i : N.Inputs) :
  R.v40664 (state s) (inputs i) = Zmod.unsigned (N.v40664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40664 s i)) at 1.
  unfold R.v40664, N.v40664.
  unfold R.v6, N.v6.
  rewrite ?node_40663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40665 (s : N.State) (i : N.Inputs) :
  R.v40665 (state s) (inputs i) = Zmod.unsigned (N.v40665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40665 s i)) at 1.
  unfold R.v40665, N.v40665.
  rewrite ?node_8132.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40666 (s : N.State) (i : N.Inputs) :
  R.v40666 (state s) (inputs i) = Zmod.unsigned (N.v40666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40666 s i)) at 1.
  unfold R.v40666, N.v40666.
  unfold R.v6, N.v6.
  rewrite ?node_8251.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40667 (s : N.State) (i : N.Inputs) :
  R.v40667 (state s) (inputs i) = Zmod.unsigned (N.v40667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40667 s i)) at 1.
  unfold R.v40667, N.v40667.
  unfold R.v6, N.v6.
  rewrite ?node_8273.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40668 (s : N.State) (i : N.Inputs) :
  R.v40668 (state s) (inputs i) = Zmod.unsigned (N.v40668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40668 s i)) at 1.
  unfold R.v40668, N.v40668.
  rewrite ?node_40665.
  rewrite ?node_40666.
  rewrite ?node_40667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40669 (s : N.State) (i : N.Inputs) :
  R.v40669 (state s) (inputs i) = Zmod.unsigned (N.v40669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40669 s i)) at 1.
  unfold R.v40669, N.v40669.
  rewrite ?node_40664.
  rewrite ?node_40668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40670 (s : N.State) (i : N.Inputs) :
  R.v40670 (state s) (inputs i) = Zmod.unsigned (N.v40670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40670 s i)) at 1.
  unfold R.v40670, N.v40670.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40671 (s : N.State) (i : N.Inputs) :
  R.v40671 (state s) (inputs i) = Zmod.unsigned (N.v40671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40671 s i)) at 1.
  unfold R.v40671, N.v40671.
  rewrite ?node_8123.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40672 (s : N.State) (i : N.Inputs) :
  R.v40672 (state s) (inputs i) = Zmod.unsigned (N.v40672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40672 s i)) at 1.
  unfold R.v40672, N.v40672.
  unfold R.v6, N.v6.
  rewrite ?node_8119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40673 (s : N.State) (i : N.Inputs) :
  R.v40673 (state s) (inputs i) = Zmod.unsigned (N.v40673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40673 s i)) at 1.
  unfold R.v40673, N.v40673.
  unfold R.v6, N.v6.
  rewrite ?node_8116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40674 (s : N.State) (i : N.Inputs) :
  R.v40674 (state s) (inputs i) = Zmod.unsigned (N.v40674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40674 s i)) at 1.
  unfold R.v40674, N.v40674.
  rewrite ?node_40672.
  rewrite ?node_40673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40675 (s : N.State) (i : N.Inputs) :
  R.v40675 (state s) (inputs i) = Zmod.unsigned (N.v40675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40675 s i)) at 1.
  unfold R.v40675, N.v40675.
  unfold R.v16484, N.v16484.
  rewrite ?node_40674.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40676 (s : N.State) (i : N.Inputs) :
  R.v40676 (state s) (inputs i) = Zmod.unsigned (N.v40676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40676 s i)) at 1.
  unfold R.v40676, N.v40676.
  rewrite ?node_40671.
  rewrite ?node_40675.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40677 (s : N.State) (i : N.Inputs) :
  R.v40677 (state s) (inputs i) = Zmod.unsigned (N.v40677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40677 s i)) at 1.
  unfold R.v40677, N.v40677.
  unfold R.v6, N.v6.
  rewrite ?node_40676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40678 (s : N.State) (i : N.Inputs) :
  R.v40678 (state s) (inputs i) = Zmod.unsigned (N.v40678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40678 s i)) at 1.
  unfold R.v40678, N.v40678.
  rewrite ?node_8124.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40679 (s : N.State) (i : N.Inputs) :
  R.v40679 (state s) (inputs i) = Zmod.unsigned (N.v40679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40679 s i)) at 1.
  unfold R.v40679, N.v40679.
  unfold R.v6, N.v6.
  rewrite ?node_8251.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40680 (s : N.State) (i : N.Inputs) :
  R.v40680 (state s) (inputs i) = Zmod.unsigned (N.v40680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40680 s i)) at 1.
  unfold R.v40680, N.v40680.
  rewrite ?node_40678.
  rewrite ?node_40679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40681 (s : N.State) (i : N.Inputs) :
  R.v40681 (state s) (inputs i) = Zmod.unsigned (N.v40681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40681 s i)) at 1.
  unfold R.v40681, N.v40681.
  rewrite ?node_40677.
  rewrite ?node_40680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40682 (s : N.State) (i : N.Inputs) :
  R.v40682 (state s) (inputs i) = Zmod.unsigned (N.v40682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40682 s i)) at 1.
  unfold R.v40682, N.v40682.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40683 (s : N.State) (i : N.Inputs) :
  R.v40683 (state s) (inputs i) = Zmod.unsigned (N.v40683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40683 s i)) at 1.
  unfold R.v40683, N.v40683.
  rewrite ?node_8131.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40684 (s : N.State) (i : N.Inputs) :
  R.v40684 (state s) (inputs i) = Zmod.unsigned (N.v40684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40684 s i)) at 1.
  unfold R.v40684, N.v40684.
  unfold R.v6, N.v6.
  rewrite ?node_8127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40685 (s : N.State) (i : N.Inputs) :
  R.v40685 (state s) (inputs i) = Zmod.unsigned (N.v40685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40685 s i)) at 1.
  unfold R.v40685, N.v40685.
  unfold R.v6, N.v6.
  rewrite ?node_8124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40686 (s : N.State) (i : N.Inputs) :
  R.v40686 (state s) (inputs i) = Zmod.unsigned (N.v40686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40686 s i)) at 1.
  unfold R.v40686, N.v40686.
  rewrite ?node_40684.
  rewrite ?node_40685.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40687 (s : N.State) (i : N.Inputs) :
  R.v40687 (state s) (inputs i) = Zmod.unsigned (N.v40687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40687 s i)) at 1.
  unfold R.v40687, N.v40687.
  unfold R.v16484, N.v16484.
  rewrite ?node_40686.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40688 (s : N.State) (i : N.Inputs) :
  R.v40688 (state s) (inputs i) = Zmod.unsigned (N.v40688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40688 s i)) at 1.
  unfold R.v40688, N.v40688.
  rewrite ?node_40683.
  rewrite ?node_40687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40689 (s : N.State) (i : N.Inputs) :
  R.v40689 (state s) (inputs i) = Zmod.unsigned (N.v40689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40689 s i)) at 1.
  unfold R.v40689, N.v40689.
  unfold R.v6, N.v6.
  rewrite ?node_40688.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40690 (s : N.State) (i : N.Inputs) :
  R.v40690 (state s) (inputs i) = Zmod.unsigned (N.v40690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40690 s i)) at 1.
  unfold R.v40690, N.v40690.
  rewrite ?node_8132.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40691 (s : N.State) (i : N.Inputs) :
  R.v40691 (state s) (inputs i) = Zmod.unsigned (N.v40691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40691 s i)) at 1.
  unfold R.v40691, N.v40691.
  unfold R.v6, N.v6.
  rewrite ?node_8273.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40692 (s : N.State) (i : N.Inputs) :
  R.v40692 (state s) (inputs i) = Zmod.unsigned (N.v40692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40692 s i)) at 1.
  unfold R.v40692, N.v40692.
  rewrite ?node_40690.
  rewrite ?node_40691.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40693 (s : N.State) (i : N.Inputs) :
  R.v40693 (state s) (inputs i) = Zmod.unsigned (N.v40693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40693 s i)) at 1.
  unfold R.v40693, N.v40693.
  rewrite ?node_40689.
  rewrite ?node_40692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40694 (s : N.State) (i : N.Inputs) :
  R.v40694 (state s) (inputs i) = Zmod.unsigned (N.v40694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40694 s i)) at 1.
  unfold R.v40694, N.v40694.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40695 (s : N.State) (i : N.Inputs) :
  R.v40695 (state s) (inputs i) = Zmod.unsigned (N.v40695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40695 s i)) at 1.
  unfold R.v40695, N.v40695.
  rewrite ?node_8206.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40696 (s : N.State) (i : N.Inputs) :
  R.v40696 (state s) (inputs i) = Zmod.unsigned (N.v40696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40696 s i)) at 1.
  unfold R.v40696, N.v40696.
  rewrite ?node_8202.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40697 (s : N.State) (i : N.Inputs) :
  R.v40697 (state s) (inputs i) = Zmod.unsigned (N.v40697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40697 s i)) at 1.
  unfold R.v40697, N.v40697.
  rewrite ?node_8194.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40698 (s : N.State) (i : N.Inputs) :
  R.v40698 (state s) (inputs i) = Zmod.unsigned (N.v40698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40698 s i)) at 1.
  unfold R.v40698, N.v40698.
  unfold R.v6, N.v6.
  rewrite ?node_8186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40699 (s : N.State) (i : N.Inputs) :
  R.v40699 (state s) (inputs i) = Zmod.unsigned (N.v40699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40699 s i)) at 1.
  unfold R.v40699, N.v40699.
  unfold R.v6, N.v6.
  rewrite ?node_8179.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40700 (s : N.State) (i : N.Inputs) :
  R.v40700 (state s) (inputs i) = Zmod.unsigned (N.v40700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40700 s i)) at 1.
  unfold R.v40700, N.v40700.
  rewrite ?node_40698.
  rewrite ?node_40699.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40701 (s : N.State) (i : N.Inputs) :
  R.v40701 (state s) (inputs i) = Zmod.unsigned (N.v40701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40701 s i)) at 1.
  unfold R.v40701, N.v40701.
  unfold R.v16484, N.v16484.
  rewrite ?node_40700.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40702 (s : N.State) (i : N.Inputs) :
  R.v40702 (state s) (inputs i) = Zmod.unsigned (N.v40702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40702 s i)) at 1.
  unfold R.v40702, N.v40702.
  rewrite ?node_40695.
  rewrite ?node_40696.
  rewrite ?node_40697.
  rewrite ?node_40701.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40703 (s : N.State) (i : N.Inputs) :
  R.v40703 (state s) (inputs i) = Zmod.unsigned (N.v40703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40703 s i)) at 1.
  unfold R.v40703, N.v40703.
  unfold R.v6, N.v6.
  rewrite ?node_40702.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40704 (s : N.State) (i : N.Inputs) :
  R.v40704 (state s) (inputs i) = Zmod.unsigned (N.v40704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40704 s i)) at 1.
  unfold R.v40704, N.v40704.
  rewrite ?node_8207.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40705 (s : N.State) (i : N.Inputs) :
  R.v40705 (state s) (inputs i) = Zmod.unsigned (N.v40705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40705 s i)) at 1.
  unfold R.v40705, N.v40705.
  unfold R.v6, N.v6.
  rewrite ?node_8328.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40706 (s : N.State) (i : N.Inputs) :
  R.v40706 (state s) (inputs i) = Zmod.unsigned (N.v40706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40706 s i)) at 1.
  unfold R.v40706, N.v40706.
  unfold R.v6, N.v6.
  rewrite ?node_8389.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40707 (s : N.State) (i : N.Inputs) :
  R.v40707 (state s) (inputs i) = Zmod.unsigned (N.v40707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40707 s i)) at 1.
  unfold R.v40707, N.v40707.
  rewrite ?node_40704.
  rewrite ?node_40705.
  rewrite ?node_40706.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40708 (s : N.State) (i : N.Inputs) :
  R.v40708 (state s) (inputs i) = Zmod.unsigned (N.v40708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40708 s i)) at 1.
  unfold R.v40708, N.v40708.
  rewrite ?node_40703.
  rewrite ?node_40707.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40709 (s : N.State) (i : N.Inputs) :
  R.v40709 (state s) (inputs i) = Zmod.unsigned (N.v40709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40709 s i)) at 1.
  unfold R.v40709, N.v40709.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40710 (s : N.State) (i : N.Inputs) :
  R.v40710 (state s) (inputs i) = Zmod.unsigned (N.v40710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40710 s i)) at 1.
  unfold R.v40710, N.v40710.
  rewrite ?node_8194.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40711 (s : N.State) (i : N.Inputs) :
  R.v40711 (state s) (inputs i) = Zmod.unsigned (N.v40711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40711 s i)) at 1.
  unfold R.v40711, N.v40711.
  unfold R.v6, N.v6.
  rewrite ?node_8186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40712 (s : N.State) (i : N.Inputs) :
  R.v40712 (state s) (inputs i) = Zmod.unsigned (N.v40712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40712 s i)) at 1.
  unfold R.v40712, N.v40712.
  unfold R.v6, N.v6.
  rewrite ?node_8179.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40713 (s : N.State) (i : N.Inputs) :
  R.v40713 (state s) (inputs i) = Zmod.unsigned (N.v40713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40713 s i)) at 1.
  unfold R.v40713, N.v40713.
  rewrite ?node_40711.
  rewrite ?node_40712.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40714 (s : N.State) (i : N.Inputs) :
  R.v40714 (state s) (inputs i) = Zmod.unsigned (N.v40714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40714 s i)) at 1.
  unfold R.v40714, N.v40714.
  unfold R.v16484, N.v16484.
  rewrite ?node_40713.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40715 (s : N.State) (i : N.Inputs) :
  R.v40715 (state s) (inputs i) = Zmod.unsigned (N.v40715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40715 s i)) at 1.
  unfold R.v40715, N.v40715.
  rewrite ?node_40710.
  rewrite ?node_40714.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40716 (s : N.State) (i : N.Inputs) :
  R.v40716 (state s) (inputs i) = Zmod.unsigned (N.v40716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40716 s i)) at 1.
  unfold R.v40716, N.v40716.
  unfold R.v6, N.v6.
  rewrite ?node_40715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40717 (s : N.State) (i : N.Inputs) :
  R.v40717 (state s) (inputs i) = Zmod.unsigned (N.v40717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40717 s i)) at 1.
  unfold R.v40717, N.v40717.
  rewrite ?node_8195.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40718 (s : N.State) (i : N.Inputs) :
  R.v40718 (state s) (inputs i) = Zmod.unsigned (N.v40718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40718 s i)) at 1.
  unfold R.v40718, N.v40718.
  unfold R.v6, N.v6.
  rewrite ?node_8328.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40719 (s : N.State) (i : N.Inputs) :
  R.v40719 (state s) (inputs i) = Zmod.unsigned (N.v40719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40719 s i)) at 1.
  unfold R.v40719, N.v40719.
  rewrite ?node_40717.
  rewrite ?node_40718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40720 (s : N.State) (i : N.Inputs) :
  R.v40720 (state s) (inputs i) = Zmod.unsigned (N.v40720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40720 s i)) at 1.
  unfold R.v40720, N.v40720.
  rewrite ?node_40716.
  rewrite ?node_40719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40721 (s : N.State) (i : N.Inputs) :
  R.v40721 (state s) (inputs i) = Zmod.unsigned (N.v40721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40721 s i)) at 1.
  unfold R.v40721, N.v40721.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40722 (s : N.State) (i : N.Inputs) :
  R.v40722 (state s) (inputs i) = Zmod.unsigned (N.v40722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40722 s i)) at 1.
  unfold R.v40722, N.v40722.
  rewrite ?node_8206.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40723 (s : N.State) (i : N.Inputs) :
  R.v40723 (state s) (inputs i) = Zmod.unsigned (N.v40723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40723 s i)) at 1.
  unfold R.v40723, N.v40723.
  unfold R.v6, N.v6.
  rewrite ?node_8202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40724 (s : N.State) (i : N.Inputs) :
  R.v40724 (state s) (inputs i) = Zmod.unsigned (N.v40724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40724 s i)) at 1.
  unfold R.v40724, N.v40724.
  unfold R.v6, N.v6.
  rewrite ?node_8195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40725 (s : N.State) (i : N.Inputs) :
  R.v40725 (state s) (inputs i) = Zmod.unsigned (N.v40725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40725 s i)) at 1.
  unfold R.v40725, N.v40725.
  rewrite ?node_40723.
  rewrite ?node_40724.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40726 (s : N.State) (i : N.Inputs) :
  R.v40726 (state s) (inputs i) = Zmod.unsigned (N.v40726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40726 s i)) at 1.
  unfold R.v40726, N.v40726.
  unfold R.v16484, N.v16484.
  rewrite ?node_40725.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40727 (s : N.State) (i : N.Inputs) :
  R.v40727 (state s) (inputs i) = Zmod.unsigned (N.v40727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40727 s i)) at 1.
  unfold R.v40727, N.v40727.
  rewrite ?node_40722.
  rewrite ?node_40726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40728 (s : N.State) (i : N.Inputs) :
  R.v40728 (state s) (inputs i) = Zmod.unsigned (N.v40728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40728 s i)) at 1.
  unfold R.v40728, N.v40728.
  unfold R.v6, N.v6.
  rewrite ?node_40727.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40729 (s : N.State) (i : N.Inputs) :
  R.v40729 (state s) (inputs i) = Zmod.unsigned (N.v40729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40729 s i)) at 1.
  unfold R.v40729, N.v40729.
  rewrite ?node_8207.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40730 (s : N.State) (i : N.Inputs) :
  R.v40730 (state s) (inputs i) = Zmod.unsigned (N.v40730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40730 s i)) at 1.
  unfold R.v40730, N.v40730.
  unfold R.v6, N.v6.
  rewrite ?node_8389.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40731 (s : N.State) (i : N.Inputs) :
  R.v40731 (state s) (inputs i) = Zmod.unsigned (N.v40731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40731 s i)) at 1.
  unfold R.v40731, N.v40731.
  rewrite ?node_40729.
  rewrite ?node_40730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40732 (s : N.State) (i : N.Inputs) :
  R.v40732 (state s) (inputs i) = Zmod.unsigned (N.v40732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40732 s i)) at 1.
  unfold R.v40732, N.v40732.
  rewrite ?node_40728.
  rewrite ?node_40731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40733 (s : N.State) (i : N.Inputs) :
  R.v40733 (state s) (inputs i) = Zmod.unsigned (N.v40733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40733 s i)) at 1.
  unfold R.v40733, N.v40733.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40734 (s : N.State) (i : N.Inputs) :
  R.v40734 (state s) (inputs i) = Zmod.unsigned (N.v40734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40734 s i)) at 1.
  unfold R.v40734, N.v40734.
  rewrite ?node_8231.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40735 (s : N.State) (i : N.Inputs) :
  R.v40735 (state s) (inputs i) = Zmod.unsigned (N.v40735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40735 s i)) at 1.
  unfold R.v40735, N.v40735.
  rewrite ?node_8227.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40736 (s : N.State) (i : N.Inputs) :
  R.v40736 (state s) (inputs i) = Zmod.unsigned (N.v40736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40736 s i)) at 1.
  unfold R.v40736, N.v40736.
  rewrite ?node_8223.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40737 (s : N.State) (i : N.Inputs) :
  R.v40737 (state s) (inputs i) = Zmod.unsigned (N.v40737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40737 s i)) at 1.
  unfold R.v40737, N.v40737.
  unfold R.v6, N.v6.
  rewrite ?node_8221.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40738 (s : N.State) (i : N.Inputs) :
  R.v40738 (state s) (inputs i) = Zmod.unsigned (N.v40738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40738 s i)) at 1.
  unfold R.v40738, N.v40738.
  unfold R.v6, N.v6.
  rewrite ?node_8214.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40739 (s : N.State) (i : N.Inputs) :
  R.v40739 (state s) (inputs i) = Zmod.unsigned (N.v40739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40739 s i)) at 1.
  unfold R.v40739, N.v40739.
  rewrite ?node_40737.
  rewrite ?node_40738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40740 (s : N.State) (i : N.Inputs) :
  R.v40740 (state s) (inputs i) = Zmod.unsigned (N.v40740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40740 s i)) at 1.
  unfold R.v40740, N.v40740.
  unfold R.v16484, N.v16484.
  rewrite ?node_40739.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40741 (s : N.State) (i : N.Inputs) :
  R.v40741 (state s) (inputs i) = Zmod.unsigned (N.v40741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40741 s i)) at 1.
  unfold R.v40741, N.v40741.
  rewrite ?node_40734.
  rewrite ?node_40735.
  rewrite ?node_40736.
  rewrite ?node_40740.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40742 (s : N.State) (i : N.Inputs) :
  R.v40742 (state s) (inputs i) = Zmod.unsigned (N.v40742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40742 s i)) at 1.
  unfold R.v40742, N.v40742.
  unfold R.v6, N.v6.
  rewrite ?node_40741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40743 (s : N.State) (i : N.Inputs) :
  R.v40743 (state s) (inputs i) = Zmod.unsigned (N.v40743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40743 s i)) at 1.
  unfold R.v40743, N.v40743.
  rewrite ?node_8232.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40744 (s : N.State) (i : N.Inputs) :
  R.v40744 (state s) (inputs i) = Zmod.unsigned (N.v40744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40744 s i)) at 1.
  unfold R.v40744, N.v40744.
  unfold R.v6, N.v6.
  rewrite ?node_8354.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40745 (s : N.State) (i : N.Inputs) :
  R.v40745 (state s) (inputs i) = Zmod.unsigned (N.v40745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40745 s i)) at 1.
  unfold R.v40745, N.v40745.
  unfold R.v6, N.v6.
  rewrite ?node_8392.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40746 (s : N.State) (i : N.Inputs) :
  R.v40746 (state s) (inputs i) = Zmod.unsigned (N.v40746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40746 s i)) at 1.
  unfold R.v40746, N.v40746.
  rewrite ?node_40743.
  rewrite ?node_40744.
  rewrite ?node_40745.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40747 (s : N.State) (i : N.Inputs) :
  R.v40747 (state s) (inputs i) = Zmod.unsigned (N.v40747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40747 s i)) at 1.
  unfold R.v40747, N.v40747.
  rewrite ?node_40742.
  rewrite ?node_40746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40748 (s : N.State) (i : N.Inputs) :
  R.v40748 (state s) (inputs i) = Zmod.unsigned (N.v40748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40748 s i)) at 1.
  unfold R.v40748, N.v40748.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40749 (s : N.State) (i : N.Inputs) :
  R.v40749 (state s) (inputs i) = Zmod.unsigned (N.v40749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40749 s i)) at 1.
  unfold R.v40749, N.v40749.
  rewrite ?node_8223.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40750 (s : N.State) (i : N.Inputs) :
  R.v40750 (state s) (inputs i) = Zmod.unsigned (N.v40750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40750 s i)) at 1.
  unfold R.v40750, N.v40750.
  unfold R.v6, N.v6.
  rewrite ?node_8221.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40751 (s : N.State) (i : N.Inputs) :
  R.v40751 (state s) (inputs i) = Zmod.unsigned (N.v40751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40751 s i)) at 1.
  unfold R.v40751, N.v40751.
  unfold R.v6, N.v6.
  rewrite ?node_8214.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40752 (s : N.State) (i : N.Inputs) :
  R.v40752 (state s) (inputs i) = Zmod.unsigned (N.v40752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40752 s i)) at 1.
  unfold R.v40752, N.v40752.
  rewrite ?node_40750.
  rewrite ?node_40751.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40753 (s : N.State) (i : N.Inputs) :
  R.v40753 (state s) (inputs i) = Zmod.unsigned (N.v40753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40753 s i)) at 1.
  unfold R.v40753, N.v40753.
  unfold R.v16484, N.v16484.
  rewrite ?node_40752.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40754 (s : N.State) (i : N.Inputs) :
  R.v40754 (state s) (inputs i) = Zmod.unsigned (N.v40754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40754 s i)) at 1.
  unfold R.v40754, N.v40754.
  rewrite ?node_40749.
  rewrite ?node_40753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40755 (s : N.State) (i : N.Inputs) :
  R.v40755 (state s) (inputs i) = Zmod.unsigned (N.v40755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40755 s i)) at 1.
  unfold R.v40755, N.v40755.
  unfold R.v6, N.v6.
  rewrite ?node_40754.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40756 (s : N.State) (i : N.Inputs) :
  R.v40756 (state s) (inputs i) = Zmod.unsigned (N.v40756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40756 s i)) at 1.
  unfold R.v40756, N.v40756.
  rewrite ?node_8224.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40757 (s : N.State) (i : N.Inputs) :
  R.v40757 (state s) (inputs i) = Zmod.unsigned (N.v40757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40757 s i)) at 1.
  unfold R.v40757, N.v40757.
  unfold R.v6, N.v6.
  rewrite ?node_8354.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40758 (s : N.State) (i : N.Inputs) :
  R.v40758 (state s) (inputs i) = Zmod.unsigned (N.v40758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40758 s i)) at 1.
  unfold R.v40758, N.v40758.
  rewrite ?node_40756.
  rewrite ?node_40757.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40759 (s : N.State) (i : N.Inputs) :
  R.v40759 (state s) (inputs i) = Zmod.unsigned (N.v40759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40759 s i)) at 1.
  unfold R.v40759, N.v40759.
  rewrite ?node_40755.
  rewrite ?node_40758.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40760 (s : N.State) (i : N.Inputs) :
  R.v40760 (state s) (inputs i) = Zmod.unsigned (N.v40760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40760 s i)) at 1.
  unfold R.v40760, N.v40760.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40761 (s : N.State) (i : N.Inputs) :
  R.v40761 (state s) (inputs i) = Zmod.unsigned (N.v40761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40761 s i)) at 1.
  unfold R.v40761, N.v40761.
  rewrite ?node_8231.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40762 (s : N.State) (i : N.Inputs) :
  R.v40762 (state s) (inputs i) = Zmod.unsigned (N.v40762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40762 s i)) at 1.
  unfold R.v40762, N.v40762.
  unfold R.v6, N.v6.
  rewrite ?node_8227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40763 (s : N.State) (i : N.Inputs) :
  R.v40763 (state s) (inputs i) = Zmod.unsigned (N.v40763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40763 s i)) at 1.
  unfold R.v40763, N.v40763.
  unfold R.v6, N.v6.
  rewrite ?node_8224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40764 (s : N.State) (i : N.Inputs) :
  R.v40764 (state s) (inputs i) = Zmod.unsigned (N.v40764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40764 s i)) at 1.
  unfold R.v40764, N.v40764.
  rewrite ?node_40762.
  rewrite ?node_40763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40765 (s : N.State) (i : N.Inputs) :
  R.v40765 (state s) (inputs i) = Zmod.unsigned (N.v40765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40765 s i)) at 1.
  unfold R.v40765, N.v40765.
  unfold R.v16484, N.v16484.
  rewrite ?node_40764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40766 (s : N.State) (i : N.Inputs) :
  R.v40766 (state s) (inputs i) = Zmod.unsigned (N.v40766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40766 s i)) at 1.
  unfold R.v40766, N.v40766.
  rewrite ?node_40761.
  rewrite ?node_40765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40767 (s : N.State) (i : N.Inputs) :
  R.v40767 (state s) (inputs i) = Zmod.unsigned (N.v40767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40767 s i)) at 1.
  unfold R.v40767, N.v40767.
  unfold R.v6, N.v6.
  rewrite ?node_40766.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40768 (s : N.State) (i : N.Inputs) :
  R.v40768 (state s) (inputs i) = Zmod.unsigned (N.v40768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40768 s i)) at 1.
  unfold R.v40768, N.v40768.
  rewrite ?node_8232.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40769 (s : N.State) (i : N.Inputs) :
  R.v40769 (state s) (inputs i) = Zmod.unsigned (N.v40769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40769 s i)) at 1.
  unfold R.v40769, N.v40769.
  unfold R.v6, N.v6.
  rewrite ?node_8392.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40770 (s : N.State) (i : N.Inputs) :
  R.v40770 (state s) (inputs i) = Zmod.unsigned (N.v40770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40770 s i)) at 1.
  unfold R.v40770, N.v40770.
  rewrite ?node_40768.
  rewrite ?node_40769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40771 (s : N.State) (i : N.Inputs) :
  R.v40771 (state s) (inputs i) = Zmod.unsigned (N.v40771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40771 s i)) at 1.
  unfold R.v40771, N.v40771.
  rewrite ?node_40767.
  rewrite ?node_40770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40772 (s : N.State) (i : N.Inputs) :
  R.v40772 (state s) (inputs i) = Zmod.unsigned (N.v40772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40772 s i)) at 1.
  unfold R.v40772, N.v40772.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40773 (s : N.State) (i : N.Inputs) :
  R.v40773 (state s) (inputs i) = Zmod.unsigned (N.v40773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40773 s i)) at 1.
  unfold R.v40773, N.v40773.
  rewrite ?node_8251.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40774 (s : N.State) (i : N.Inputs) :
  R.v40774 (state s) (inputs i) = Zmod.unsigned (N.v40774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40774 s i)) at 1.
  unfold R.v40774, N.v40774.
  rewrite ?node_8247.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40775 (s : N.State) (i : N.Inputs) :
  R.v40775 (state s) (inputs i) = Zmod.unsigned (N.v40775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40775 s i)) at 1.
  unfold R.v40775, N.v40775.
  rewrite ?node_8243.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40776 (s : N.State) (i : N.Inputs) :
  R.v40776 (state s) (inputs i) = Zmod.unsigned (N.v40776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40776 s i)) at 1.
  unfold R.v40776, N.v40776.
  unfold R.v6, N.v6.
  rewrite ?node_8239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40777 (s : N.State) (i : N.Inputs) :
  R.v40777 (state s) (inputs i) = Zmod.unsigned (N.v40777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40777 s i)) at 1.
  unfold R.v40777, N.v40777.
  unfold R.v6, N.v6.
  rewrite ?node_8236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40778 (s : N.State) (i : N.Inputs) :
  R.v40778 (state s) (inputs i) = Zmod.unsigned (N.v40778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40778 s i)) at 1.
  unfold R.v40778, N.v40778.
  rewrite ?node_40776.
  rewrite ?node_40777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40779 (s : N.State) (i : N.Inputs) :
  R.v40779 (state s) (inputs i) = Zmod.unsigned (N.v40779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40779 s i)) at 1.
  unfold R.v40779, N.v40779.
  unfold R.v16484, N.v16484.
  rewrite ?node_40778.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40780 (s : N.State) (i : N.Inputs) :
  R.v40780 (state s) (inputs i) = Zmod.unsigned (N.v40780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40780 s i)) at 1.
  unfold R.v40780, N.v40780.
  rewrite ?node_40773.
  rewrite ?node_40774.
  rewrite ?node_40775.
  rewrite ?node_40779.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40781 (s : N.State) (i : N.Inputs) :
  R.v40781 (state s) (inputs i) = Zmod.unsigned (N.v40781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40781 s i)) at 1.
  unfold R.v40781, N.v40781.
  unfold R.v6, N.v6.
  rewrite ?node_40780.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40782 (s : N.State) (i : N.Inputs) :
  R.v40782 (state s) (inputs i) = Zmod.unsigned (N.v40782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40782 s i)) at 1.
  unfold R.v40782, N.v40782.
  rewrite ?node_8252.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40783 (s : N.State) (i : N.Inputs) :
  R.v40783 (state s) (inputs i) = Zmod.unsigned (N.v40783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40783 s i)) at 1.
  unfold R.v40783, N.v40783.
  unfold R.v6, N.v6.
  rewrite ?node_8374.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40784 (s : N.State) (i : N.Inputs) :
  R.v40784 (state s) (inputs i) = Zmod.unsigned (N.v40784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40784 s i)) at 1.
  unfold R.v40784, N.v40784.
  unfold R.v6, N.v6.
  rewrite ?node_8396.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40785 (s : N.State) (i : N.Inputs) :
  R.v40785 (state s) (inputs i) = Zmod.unsigned (N.v40785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40785 s i)) at 1.
  unfold R.v40785, N.v40785.
  rewrite ?node_40782.
  rewrite ?node_40783.
  rewrite ?node_40784.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40786 (s : N.State) (i : N.Inputs) :
  R.v40786 (state s) (inputs i) = Zmod.unsigned (N.v40786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40786 s i)) at 1.
  unfold R.v40786, N.v40786.
  rewrite ?node_40781.
  rewrite ?node_40785.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40787 (s : N.State) (i : N.Inputs) :
  R.v40787 (state s) (inputs i) = Zmod.unsigned (N.v40787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40787 s i)) at 1.
  unfold R.v40787, N.v40787.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40788 (s : N.State) (i : N.Inputs) :
  R.v40788 (state s) (inputs i) = Zmod.unsigned (N.v40788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40788 s i)) at 1.
  unfold R.v40788, N.v40788.
  rewrite ?node_8243.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40789 (s : N.State) (i : N.Inputs) :
  R.v40789 (state s) (inputs i) = Zmod.unsigned (N.v40789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40789 s i)) at 1.
  unfold R.v40789, N.v40789.
  unfold R.v6, N.v6.
  rewrite ?node_8239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40790 (s : N.State) (i : N.Inputs) :
  R.v40790 (state s) (inputs i) = Zmod.unsigned (N.v40790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40790 s i)) at 1.
  unfold R.v40790, N.v40790.
  unfold R.v6, N.v6.
  rewrite ?node_8236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40791 (s : N.State) (i : N.Inputs) :
  R.v40791 (state s) (inputs i) = Zmod.unsigned (N.v40791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40791 s i)) at 1.
  unfold R.v40791, N.v40791.
  rewrite ?node_40789.
  rewrite ?node_40790.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40792 (s : N.State) (i : N.Inputs) :
  R.v40792 (state s) (inputs i) = Zmod.unsigned (N.v40792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40792 s i)) at 1.
  unfold R.v40792, N.v40792.
  unfold R.v16484, N.v16484.
  rewrite ?node_40791.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40793 (s : N.State) (i : N.Inputs) :
  R.v40793 (state s) (inputs i) = Zmod.unsigned (N.v40793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40793 s i)) at 1.
  unfold R.v40793, N.v40793.
  rewrite ?node_40788.
  rewrite ?node_40792.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40794 (s : N.State) (i : N.Inputs) :
  R.v40794 (state s) (inputs i) = Zmod.unsigned (N.v40794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40794 s i)) at 1.
  unfold R.v40794, N.v40794.
  unfold R.v6, N.v6.
  rewrite ?node_40793.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40795 (s : N.State) (i : N.Inputs) :
  R.v40795 (state s) (inputs i) = Zmod.unsigned (N.v40795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40795 s i)) at 1.
  unfold R.v40795, N.v40795.
  rewrite ?node_8244.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40796 (s : N.State) (i : N.Inputs) :
  R.v40796 (state s) (inputs i) = Zmod.unsigned (N.v40796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40796 s i)) at 1.
  unfold R.v40796, N.v40796.
  unfold R.v6, N.v6.
  rewrite ?node_8374.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40797 (s : N.State) (i : N.Inputs) :
  R.v40797 (state s) (inputs i) = Zmod.unsigned (N.v40797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40797 s i)) at 1.
  unfold R.v40797, N.v40797.
  rewrite ?node_40795.
  rewrite ?node_40796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40798 (s : N.State) (i : N.Inputs) :
  R.v40798 (state s) (inputs i) = Zmod.unsigned (N.v40798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40798 s i)) at 1.
  unfold R.v40798, N.v40798.
  rewrite ?node_40794.
  rewrite ?node_40797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40799 (s : N.State) (i : N.Inputs) :
  R.v40799 (state s) (inputs i) = Zmod.unsigned (N.v40799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40799 s i)) at 1.
  unfold R.v40799, N.v40799.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40800 (s : N.State) (i : N.Inputs) :
  R.v40800 (state s) (inputs i) = Zmod.unsigned (N.v40800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40800 s i)) at 1.
  unfold R.v40800, N.v40800.
  rewrite ?node_8251.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40801 (s : N.State) (i : N.Inputs) :
  R.v40801 (state s) (inputs i) = Zmod.unsigned (N.v40801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40801 s i)) at 1.
  unfold R.v40801, N.v40801.
  unfold R.v6, N.v6.
  rewrite ?node_8247.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40802 (s : N.State) (i : N.Inputs) :
  R.v40802 (state s) (inputs i) = Zmod.unsigned (N.v40802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40802 s i)) at 1.
  unfold R.v40802, N.v40802.
  unfold R.v6, N.v6.
  rewrite ?node_8244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40803 (s : N.State) (i : N.Inputs) :
  R.v40803 (state s) (inputs i) = Zmod.unsigned (N.v40803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40803 s i)) at 1.
  unfold R.v40803, N.v40803.
  rewrite ?node_40801.
  rewrite ?node_40802.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40804 (s : N.State) (i : N.Inputs) :
  R.v40804 (state s) (inputs i) = Zmod.unsigned (N.v40804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40804 s i)) at 1.
  unfold R.v40804, N.v40804.
  unfold R.v16484, N.v16484.
  rewrite ?node_40803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40805 (s : N.State) (i : N.Inputs) :
  R.v40805 (state s) (inputs i) = Zmod.unsigned (N.v40805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40805 s i)) at 1.
  unfold R.v40805, N.v40805.
  rewrite ?node_40800.
  rewrite ?node_40804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40806 (s : N.State) (i : N.Inputs) :
  R.v40806 (state s) (inputs i) = Zmod.unsigned (N.v40806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40806 s i)) at 1.
  unfold R.v40806, N.v40806.
  unfold R.v6, N.v6.
  rewrite ?node_40805.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40807 (s : N.State) (i : N.Inputs) :
  R.v40807 (state s) (inputs i) = Zmod.unsigned (N.v40807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40807 s i)) at 1.
  unfold R.v40807, N.v40807.
  rewrite ?node_8252.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40808 (s : N.State) (i : N.Inputs) :
  R.v40808 (state s) (inputs i) = Zmod.unsigned (N.v40808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40808 s i)) at 1.
  unfold R.v40808, N.v40808.
  unfold R.v6, N.v6.
  rewrite ?node_8396.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40809 (s : N.State) (i : N.Inputs) :
  R.v40809 (state s) (inputs i) = Zmod.unsigned (N.v40809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40809 s i)) at 1.
  unfold R.v40809, N.v40809.
  rewrite ?node_40807.
  rewrite ?node_40808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40810 (s : N.State) (i : N.Inputs) :
  R.v40810 (state s) (inputs i) = Zmod.unsigned (N.v40810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40810 s i)) at 1.
  unfold R.v40810, N.v40810.
  rewrite ?node_40806.
  rewrite ?node_40809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40811 (s : N.State) (i : N.Inputs) :
  R.v40811 (state s) (inputs i) = Zmod.unsigned (N.v40811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40811 s i)) at 1.
  unfold R.v40811, N.v40811.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40812 (s : N.State) (i : N.Inputs) :
  R.v40812 (state s) (inputs i) = Zmod.unsigned (N.v40812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40812 s i)) at 1.
  unfold R.v40812, N.v40812.
  unfold R.v6, N.v6.
  rewrite ?node_8257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40813 (s : N.State) (i : N.Inputs) :
  R.v40813 (state s) (inputs i) = Zmod.unsigned (N.v40813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40813 s i)) at 1.
  unfold R.v40813, N.v40813.
  unfold R.v6, N.v6.
  rewrite ?node_8256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40814 (s : N.State) (i : N.Inputs) :
  R.v40814 (state s) (inputs i) = Zmod.unsigned (N.v40814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40814 s i)) at 1.
  unfold R.v40814, N.v40814.
  rewrite ?node_40812.
  rewrite ?node_40813.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40815 (s : N.State) (i : N.Inputs) :
  R.v40815 (state s) (inputs i) = Zmod.unsigned (N.v40815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40815 s i)) at 1.
  unfold R.v40815, N.v40815.
  unfold R.v16463, N.v16463.
  rewrite ?node_40814.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40816 (s : N.State) (i : N.Inputs) :
  R.v40816 (state s) (inputs i) = Zmod.unsigned (N.v40816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40816 s i)) at 1.
  unfold R.v40816, N.v40816.
  rewrite ?node_8258.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40817 (s : N.State) (i : N.Inputs) :
  R.v40817 (state s) (inputs i) = Zmod.unsigned (N.v40817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40817 s i)) at 1.
  unfold R.v40817, N.v40817.
  unfold R.v6, N.v6.
  rewrite ?node_8398.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40818 (s : N.State) (i : N.Inputs) :
  R.v40818 (state s) (inputs i) = Zmod.unsigned (N.v40818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40818 s i)) at 1.
  unfold R.v40818, N.v40818.
  rewrite ?node_40816.
  rewrite ?node_40817.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40819 (s : N.State) (i : N.Inputs) :
  R.v40819 (state s) (inputs i) = Zmod.unsigned (N.v40819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40819 s i)) at 1.
  unfold R.v40819, N.v40819.
  rewrite ?node_40815.
  rewrite ?node_40818.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40820 (s : N.State) (i : N.Inputs) :
  R.v40820 (state s) (inputs i) = Zmod.unsigned (N.v40820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40820 s i)) at 1.
  unfold R.v40820, N.v40820.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40821 (s : N.State) (i : N.Inputs) :
  R.v40821 (state s) (inputs i) = Zmod.unsigned (N.v40821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40821 s i)) at 1.
  unfold R.v40821, N.v40821.
  rewrite ?node_8328.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40822 (s : N.State) (i : N.Inputs) :
  R.v40822 (state s) (inputs i) = Zmod.unsigned (N.v40822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40822 s i)) at 1.
  unfold R.v40822, N.v40822.
  rewrite ?node_8324.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40823 (s : N.State) (i : N.Inputs) :
  R.v40823 (state s) (inputs i) = Zmod.unsigned (N.v40823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40823 s i)) at 1.
  unfold R.v40823, N.v40823.
  rewrite ?node_8316.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40824 (s : N.State) (i : N.Inputs) :
  R.v40824 (state s) (inputs i) = Zmod.unsigned (N.v40824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40824 s i)) at 1.
  unfold R.v40824, N.v40824.
  unfold R.v6, N.v6.
  rewrite ?node_8308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40825 (s : N.State) (i : N.Inputs) :
  R.v40825 (state s) (inputs i) = Zmod.unsigned (N.v40825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40825 s i)) at 1.
  unfold R.v40825, N.v40825.
  unfold R.v6, N.v6.
  rewrite ?node_8301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40826 (s : N.State) (i : N.Inputs) :
  R.v40826 (state s) (inputs i) = Zmod.unsigned (N.v40826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40826 s i)) at 1.
  unfold R.v40826, N.v40826.
  rewrite ?node_40824.
  rewrite ?node_40825.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40827 (s : N.State) (i : N.Inputs) :
  R.v40827 (state s) (inputs i) = Zmod.unsigned (N.v40827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40827 s i)) at 1.
  unfold R.v40827, N.v40827.
  unfold R.v16484, N.v16484.
  rewrite ?node_40826.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40828 (s : N.State) (i : N.Inputs) :
  R.v40828 (state s) (inputs i) = Zmod.unsigned (N.v40828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40828 s i)) at 1.
  unfold R.v40828, N.v40828.
  rewrite ?node_40821.
  rewrite ?node_40822.
  rewrite ?node_40823.
  rewrite ?node_40827.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40829 (s : N.State) (i : N.Inputs) :
  R.v40829 (state s) (inputs i) = Zmod.unsigned (N.v40829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40829 s i)) at 1.
  unfold R.v40829, N.v40829.
  unfold R.v6, N.v6.
  rewrite ?node_40828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40830 (s : N.State) (i : N.Inputs) :
  R.v40830 (state s) (inputs i) = Zmod.unsigned (N.v40830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40830 s i)) at 1.
  unfold R.v40830, N.v40830.
  rewrite ?node_8329.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40831 (s : N.State) (i : N.Inputs) :
  R.v40831 (state s) (inputs i) = Zmod.unsigned (N.v40831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40831 s i)) at 1.
  unfold R.v40831, N.v40831.
  unfold R.v6, N.v6.
  rewrite ?node_8453.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40832 (s : N.State) (i : N.Inputs) :
  R.v40832 (state s) (inputs i) = Zmod.unsigned (N.v40832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40832 s i)) at 1.
  unfold R.v40832, N.v40832.
  unfold R.v6, N.v6.
  rewrite ?node_8516.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40833 (s : N.State) (i : N.Inputs) :
  R.v40833 (state s) (inputs i) = Zmod.unsigned (N.v40833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40833 s i)) at 1.
  unfold R.v40833, N.v40833.
  rewrite ?node_40830.
  rewrite ?node_40831.
  rewrite ?node_40832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40834 (s : N.State) (i : N.Inputs) :
  R.v40834 (state s) (inputs i) = Zmod.unsigned (N.v40834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40834 s i)) at 1.
  unfold R.v40834, N.v40834.
  rewrite ?node_40829.
  rewrite ?node_40833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40835 (s : N.State) (i : N.Inputs) :
  R.v40835 (state s) (inputs i) = Zmod.unsigned (N.v40835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40835 s i)) at 1.
  unfold R.v40835, N.v40835.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40836 (s : N.State) (i : N.Inputs) :
  R.v40836 (state s) (inputs i) = Zmod.unsigned (N.v40836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40836 s i)) at 1.
  unfold R.v40836, N.v40836.
  rewrite ?node_8316.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40837 (s : N.State) (i : N.Inputs) :
  R.v40837 (state s) (inputs i) = Zmod.unsigned (N.v40837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40837 s i)) at 1.
  unfold R.v40837, N.v40837.
  unfold R.v6, N.v6.
  rewrite ?node_8308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40838 (s : N.State) (i : N.Inputs) :
  R.v40838 (state s) (inputs i) = Zmod.unsigned (N.v40838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40838 s i)) at 1.
  unfold R.v40838, N.v40838.
  unfold R.v6, N.v6.
  rewrite ?node_8301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40839 (s : N.State) (i : N.Inputs) :
  R.v40839 (state s) (inputs i) = Zmod.unsigned (N.v40839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40839 s i)) at 1.
  unfold R.v40839, N.v40839.
  rewrite ?node_40837.
  rewrite ?node_40838.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40840 (s : N.State) (i : N.Inputs) :
  R.v40840 (state s) (inputs i) = Zmod.unsigned (N.v40840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40840 s i)) at 1.
  unfold R.v40840, N.v40840.
  unfold R.v16484, N.v16484.
  rewrite ?node_40839.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40841 (s : N.State) (i : N.Inputs) :
  R.v40841 (state s) (inputs i) = Zmod.unsigned (N.v40841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40841 s i)) at 1.
  unfold R.v40841, N.v40841.
  rewrite ?node_40836.
  rewrite ?node_40840.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40842 (s : N.State) (i : N.Inputs) :
  R.v40842 (state s) (inputs i) = Zmod.unsigned (N.v40842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40842 s i)) at 1.
  unfold R.v40842, N.v40842.
  unfold R.v6, N.v6.
  rewrite ?node_40841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40843 (s : N.State) (i : N.Inputs) :
  R.v40843 (state s) (inputs i) = Zmod.unsigned (N.v40843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40843 s i)) at 1.
  unfold R.v40843, N.v40843.
  rewrite ?node_8317.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40844 (s : N.State) (i : N.Inputs) :
  R.v40844 (state s) (inputs i) = Zmod.unsigned (N.v40844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40844 s i)) at 1.
  unfold R.v40844, N.v40844.
  unfold R.v6, N.v6.
  rewrite ?node_8453.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40845 (s : N.State) (i : N.Inputs) :
  R.v40845 (state s) (inputs i) = Zmod.unsigned (N.v40845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40845 s i)) at 1.
  unfold R.v40845, N.v40845.
  rewrite ?node_40843.
  rewrite ?node_40844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40846 (s : N.State) (i : N.Inputs) :
  R.v40846 (state s) (inputs i) = Zmod.unsigned (N.v40846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40846 s i)) at 1.
  unfold R.v40846, N.v40846.
  rewrite ?node_40842.
  rewrite ?node_40845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40847 (s : N.State) (i : N.Inputs) :
  R.v40847 (state s) (inputs i) = Zmod.unsigned (N.v40847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40847 s i)) at 1.
  unfold R.v40847, N.v40847.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40848 (s : N.State) (i : N.Inputs) :
  R.v40848 (state s) (inputs i) = Zmod.unsigned (N.v40848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40848 s i)) at 1.
  unfold R.v40848, N.v40848.
  rewrite ?node_8328.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40849 (s : N.State) (i : N.Inputs) :
  R.v40849 (state s) (inputs i) = Zmod.unsigned (N.v40849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40849 s i)) at 1.
  unfold R.v40849, N.v40849.
  unfold R.v6, N.v6.
  rewrite ?node_8324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40850 (s : N.State) (i : N.Inputs) :
  R.v40850 (state s) (inputs i) = Zmod.unsigned (N.v40850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40850 s i)) at 1.
  unfold R.v40850, N.v40850.
  unfold R.v6, N.v6.
  rewrite ?node_8317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40851 (s : N.State) (i : N.Inputs) :
  R.v40851 (state s) (inputs i) = Zmod.unsigned (N.v40851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40851 s i)) at 1.
  unfold R.v40851, N.v40851.
  rewrite ?node_40849.
  rewrite ?node_40850.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40852 (s : N.State) (i : N.Inputs) :
  R.v40852 (state s) (inputs i) = Zmod.unsigned (N.v40852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40852 s i)) at 1.
  unfold R.v40852, N.v40852.
  unfold R.v16484, N.v16484.
  rewrite ?node_40851.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40853 (s : N.State) (i : N.Inputs) :
  R.v40853 (state s) (inputs i) = Zmod.unsigned (N.v40853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40853 s i)) at 1.
  unfold R.v40853, N.v40853.
  rewrite ?node_40848.
  rewrite ?node_40852.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40854 (s : N.State) (i : N.Inputs) :
  R.v40854 (state s) (inputs i) = Zmod.unsigned (N.v40854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40854 s i)) at 1.
  unfold R.v40854, N.v40854.
  unfold R.v6, N.v6.
  rewrite ?node_40853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40855 (s : N.State) (i : N.Inputs) :
  R.v40855 (state s) (inputs i) = Zmod.unsigned (N.v40855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40855 s i)) at 1.
  unfold R.v40855, N.v40855.
  rewrite ?node_8329.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40856 (s : N.State) (i : N.Inputs) :
  R.v40856 (state s) (inputs i) = Zmod.unsigned (N.v40856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40856 s i)) at 1.
  unfold R.v40856, N.v40856.
  unfold R.v6, N.v6.
  rewrite ?node_8516.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40857 (s : N.State) (i : N.Inputs) :
  R.v40857 (state s) (inputs i) = Zmod.unsigned (N.v40857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40857 s i)) at 1.
  unfold R.v40857, N.v40857.
  rewrite ?node_40855.
  rewrite ?node_40856.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40858 (s : N.State) (i : N.Inputs) :
  R.v40858 (state s) (inputs i) = Zmod.unsigned (N.v40858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40858 s i)) at 1.
  unfold R.v40858, N.v40858.
  rewrite ?node_40854.
  rewrite ?node_40857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40859 (s : N.State) (i : N.Inputs) :
  R.v40859 (state s) (inputs i) = Zmod.unsigned (N.v40859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40859 s i)) at 1.
  unfold R.v40859, N.v40859.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40860 (s : N.State) (i : N.Inputs) :
  R.v40860 (state s) (inputs i) = Zmod.unsigned (N.v40860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40860 s i)) at 1.
  unfold R.v40860, N.v40860.
  rewrite ?node_8354.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40861 (s : N.State) (i : N.Inputs) :
  R.v40861 (state s) (inputs i) = Zmod.unsigned (N.v40861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40861 s i)) at 1.
  unfold R.v40861, N.v40861.
  rewrite ?node_8350.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40862 (s : N.State) (i : N.Inputs) :
  R.v40862 (state s) (inputs i) = Zmod.unsigned (N.v40862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40862 s i)) at 1.
  unfold R.v40862, N.v40862.
  rewrite ?node_8346.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40863 (s : N.State) (i : N.Inputs) :
  R.v40863 (state s) (inputs i) = Zmod.unsigned (N.v40863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40863 s i)) at 1.
  unfold R.v40863, N.v40863.
  unfold R.v6, N.v6.
  rewrite ?node_8343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40864 (s : N.State) (i : N.Inputs) :
  R.v40864 (state s) (inputs i) = Zmod.unsigned (N.v40864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40864 s i)) at 1.
  unfold R.v40864, N.v40864.
  unfold R.v6, N.v6.
  rewrite ?node_8336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40865 (s : N.State) (i : N.Inputs) :
  R.v40865 (state s) (inputs i) = Zmod.unsigned (N.v40865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40865 s i)) at 1.
  unfold R.v40865, N.v40865.
  rewrite ?node_40863.
  rewrite ?node_40864.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40866 (s : N.State) (i : N.Inputs) :
  R.v40866 (state s) (inputs i) = Zmod.unsigned (N.v40866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40866 s i)) at 1.
  unfold R.v40866, N.v40866.
  unfold R.v16484, N.v16484.
  rewrite ?node_40865.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40867 (s : N.State) (i : N.Inputs) :
  R.v40867 (state s) (inputs i) = Zmod.unsigned (N.v40867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40867 s i)) at 1.
  unfold R.v40867, N.v40867.
  rewrite ?node_40860.
  rewrite ?node_40861.
  rewrite ?node_40862.
  rewrite ?node_40866.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40868 (s : N.State) (i : N.Inputs) :
  R.v40868 (state s) (inputs i) = Zmod.unsigned (N.v40868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40868 s i)) at 1.
  unfold R.v40868, N.v40868.
  unfold R.v6, N.v6.
  rewrite ?node_40867.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40869 (s : N.State) (i : N.Inputs) :
  R.v40869 (state s) (inputs i) = Zmod.unsigned (N.v40869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40869 s i)) at 1.
  unfold R.v40869, N.v40869.
  rewrite ?node_8355.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40870 (s : N.State) (i : N.Inputs) :
  R.v40870 (state s) (inputs i) = Zmod.unsigned (N.v40870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40870 s i)) at 1.
  unfold R.v40870, N.v40870.
  unfold R.v6, N.v6.
  rewrite ?node_8479.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40871 (s : N.State) (i : N.Inputs) :
  R.v40871 (state s) (inputs i) = Zmod.unsigned (N.v40871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40871 s i)) at 1.
  unfold R.v40871, N.v40871.
  unfold R.v6, N.v6.
  rewrite ?node_8519.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40872 (s : N.State) (i : N.Inputs) :
  R.v40872 (state s) (inputs i) = Zmod.unsigned (N.v40872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40872 s i)) at 1.
  unfold R.v40872, N.v40872.
  rewrite ?node_40869.
  rewrite ?node_40870.
  rewrite ?node_40871.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40873 (s : N.State) (i : N.Inputs) :
  R.v40873 (state s) (inputs i) = Zmod.unsigned (N.v40873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40873 s i)) at 1.
  unfold R.v40873, N.v40873.
  rewrite ?node_40868.
  rewrite ?node_40872.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40874 (s : N.State) (i : N.Inputs) :
  R.v40874 (state s) (inputs i) = Zmod.unsigned (N.v40874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40874 s i)) at 1.
  unfold R.v40874, N.v40874.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40875 (s : N.State) (i : N.Inputs) :
  R.v40875 (state s) (inputs i) = Zmod.unsigned (N.v40875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40875 s i)) at 1.
  unfold R.v40875, N.v40875.
  rewrite ?node_8346.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40876 (s : N.State) (i : N.Inputs) :
  R.v40876 (state s) (inputs i) = Zmod.unsigned (N.v40876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40876 s i)) at 1.
  unfold R.v40876, N.v40876.
  unfold R.v6, N.v6.
  rewrite ?node_8343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40877 (s : N.State) (i : N.Inputs) :
  R.v40877 (state s) (inputs i) = Zmod.unsigned (N.v40877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40877 s i)) at 1.
  unfold R.v40877, N.v40877.
  unfold R.v6, N.v6.
  rewrite ?node_8336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40878 (s : N.State) (i : N.Inputs) :
  R.v40878 (state s) (inputs i) = Zmod.unsigned (N.v40878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40878 s i)) at 1.
  unfold R.v40878, N.v40878.
  rewrite ?node_40876.
  rewrite ?node_40877.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40879 (s : N.State) (i : N.Inputs) :
  R.v40879 (state s) (inputs i) = Zmod.unsigned (N.v40879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40879 s i)) at 1.
  unfold R.v40879, N.v40879.
  unfold R.v16484, N.v16484.
  rewrite ?node_40878.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40880 (s : N.State) (i : N.Inputs) :
  R.v40880 (state s) (inputs i) = Zmod.unsigned (N.v40880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40880 s i)) at 1.
  unfold R.v40880, N.v40880.
  rewrite ?node_40875.
  rewrite ?node_40879.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40881 (s : N.State) (i : N.Inputs) :
  R.v40881 (state s) (inputs i) = Zmod.unsigned (N.v40881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40881 s i)) at 1.
  unfold R.v40881, N.v40881.
  unfold R.v6, N.v6.
  rewrite ?node_40880.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40882 (s : N.State) (i : N.Inputs) :
  R.v40882 (state s) (inputs i) = Zmod.unsigned (N.v40882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40882 s i)) at 1.
  unfold R.v40882, N.v40882.
  rewrite ?node_8347.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40883 (s : N.State) (i : N.Inputs) :
  R.v40883 (state s) (inputs i) = Zmod.unsigned (N.v40883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40883 s i)) at 1.
  unfold R.v40883, N.v40883.
  unfold R.v6, N.v6.
  rewrite ?node_8479.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40884 (s : N.State) (i : N.Inputs) :
  R.v40884 (state s) (inputs i) = Zmod.unsigned (N.v40884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40884 s i)) at 1.
  unfold R.v40884, N.v40884.
  rewrite ?node_40882.
  rewrite ?node_40883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40885 (s : N.State) (i : N.Inputs) :
  R.v40885 (state s) (inputs i) = Zmod.unsigned (N.v40885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40885 s i)) at 1.
  unfold R.v40885, N.v40885.
  rewrite ?node_40881.
  rewrite ?node_40884.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40886 (s : N.State) (i : N.Inputs) :
  R.v40886 (state s) (inputs i) = Zmod.unsigned (N.v40886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40886 s i)) at 1.
  unfold R.v40886, N.v40886.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40887 (s : N.State) (i : N.Inputs) :
  R.v40887 (state s) (inputs i) = Zmod.unsigned (N.v40887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40887 s i)) at 1.
  unfold R.v40887, N.v40887.
  rewrite ?node_8354.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40888 (s : N.State) (i : N.Inputs) :
  R.v40888 (state s) (inputs i) = Zmod.unsigned (N.v40888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40888 s i)) at 1.
  unfold R.v40888, N.v40888.
  unfold R.v6, N.v6.
  rewrite ?node_8350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40889 (s : N.State) (i : N.Inputs) :
  R.v40889 (state s) (inputs i) = Zmod.unsigned (N.v40889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40889 s i)) at 1.
  unfold R.v40889, N.v40889.
  unfold R.v6, N.v6.
  rewrite ?node_8347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40890 (s : N.State) (i : N.Inputs) :
  R.v40890 (state s) (inputs i) = Zmod.unsigned (N.v40890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40890 s i)) at 1.
  unfold R.v40890, N.v40890.
  rewrite ?node_40888.
  rewrite ?node_40889.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40891 (s : N.State) (i : N.Inputs) :
  R.v40891 (state s) (inputs i) = Zmod.unsigned (N.v40891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40891 s i)) at 1.
  unfold R.v40891, N.v40891.
  unfold R.v16484, N.v16484.
  rewrite ?node_40890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40892 (s : N.State) (i : N.Inputs) :
  R.v40892 (state s) (inputs i) = Zmod.unsigned (N.v40892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40892 s i)) at 1.
  unfold R.v40892, N.v40892.
  rewrite ?node_40887.
  rewrite ?node_40891.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40893 (s : N.State) (i : N.Inputs) :
  R.v40893 (state s) (inputs i) = Zmod.unsigned (N.v40893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40893 s i)) at 1.
  unfold R.v40893, N.v40893.
  unfold R.v6, N.v6.
  rewrite ?node_40892.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40894 (s : N.State) (i : N.Inputs) :
  R.v40894 (state s) (inputs i) = Zmod.unsigned (N.v40894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40894 s i)) at 1.
  unfold R.v40894, N.v40894.
  rewrite ?node_8355.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40895 (s : N.State) (i : N.Inputs) :
  R.v40895 (state s) (inputs i) = Zmod.unsigned (N.v40895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40895 s i)) at 1.
  unfold R.v40895, N.v40895.
  unfold R.v6, N.v6.
  rewrite ?node_8519.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40896 (s : N.State) (i : N.Inputs) :
  R.v40896 (state s) (inputs i) = Zmod.unsigned (N.v40896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40896 s i)) at 1.
  unfold R.v40896, N.v40896.
  rewrite ?node_40894.
  rewrite ?node_40895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40897 (s : N.State) (i : N.Inputs) :
  R.v40897 (state s) (inputs i) = Zmod.unsigned (N.v40897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40897 s i)) at 1.
  unfold R.v40897, N.v40897.
  rewrite ?node_40893.
  rewrite ?node_40896.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40898 (s : N.State) (i : N.Inputs) :
  R.v40898 (state s) (inputs i) = Zmod.unsigned (N.v40898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40898 s i)) at 1.
  unfold R.v40898, N.v40898.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40899 (s : N.State) (i : N.Inputs) :
  R.v40899 (state s) (inputs i) = Zmod.unsigned (N.v40899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40899 s i)) at 1.
  unfold R.v40899, N.v40899.
  rewrite ?node_8374.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40900 (s : N.State) (i : N.Inputs) :
  R.v40900 (state s) (inputs i) = Zmod.unsigned (N.v40900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40900 s i)) at 1.
  unfold R.v40900, N.v40900.
  rewrite ?node_8370.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40901 (s : N.State) (i : N.Inputs) :
  R.v40901 (state s) (inputs i) = Zmod.unsigned (N.v40901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40901 s i)) at 1.
  unfold R.v40901, N.v40901.
  rewrite ?node_8366.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40902 (s : N.State) (i : N.Inputs) :
  R.v40902 (state s) (inputs i) = Zmod.unsigned (N.v40902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40902 s i)) at 1.
  unfold R.v40902, N.v40902.
  unfold R.v6, N.v6.
  rewrite ?node_8362.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40903 (s : N.State) (i : N.Inputs) :
  R.v40903 (state s) (inputs i) = Zmod.unsigned (N.v40903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40903 s i)) at 1.
  unfold R.v40903, N.v40903.
  unfold R.v6, N.v6.
  rewrite ?node_8359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40904 (s : N.State) (i : N.Inputs) :
  R.v40904 (state s) (inputs i) = Zmod.unsigned (N.v40904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40904 s i)) at 1.
  unfold R.v40904, N.v40904.
  rewrite ?node_40902.
  rewrite ?node_40903.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40905 (s : N.State) (i : N.Inputs) :
  R.v40905 (state s) (inputs i) = Zmod.unsigned (N.v40905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40905 s i)) at 1.
  unfold R.v40905, N.v40905.
  unfold R.v16484, N.v16484.
  rewrite ?node_40904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40906 (s : N.State) (i : N.Inputs) :
  R.v40906 (state s) (inputs i) = Zmod.unsigned (N.v40906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40906 s i)) at 1.
  unfold R.v40906, N.v40906.
  rewrite ?node_40899.
  rewrite ?node_40900.
  rewrite ?node_40901.
  rewrite ?node_40905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40907 (s : N.State) (i : N.Inputs) :
  R.v40907 (state s) (inputs i) = Zmod.unsigned (N.v40907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40907 s i)) at 1.
  unfold R.v40907, N.v40907.
  unfold R.v6, N.v6.
  rewrite ?node_40906.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40908 (s : N.State) (i : N.Inputs) :
  R.v40908 (state s) (inputs i) = Zmod.unsigned (N.v40908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40908 s i)) at 1.
  unfold R.v40908, N.v40908.
  rewrite ?node_8375.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40909 (s : N.State) (i : N.Inputs) :
  R.v40909 (state s) (inputs i) = Zmod.unsigned (N.v40909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40909 s i)) at 1.
  unfold R.v40909, N.v40909.
  unfold R.v6, N.v6.
  rewrite ?node_8499.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40910 (s : N.State) (i : N.Inputs) :
  R.v40910 (state s) (inputs i) = Zmod.unsigned (N.v40910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40910 s i)) at 1.
  unfold R.v40910, N.v40910.
  unfold R.v6, N.v6.
  rewrite ?node_8523.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40911 (s : N.State) (i : N.Inputs) :
  R.v40911 (state s) (inputs i) = Zmod.unsigned (N.v40911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40911 s i)) at 1.
  unfold R.v40911, N.v40911.
  rewrite ?node_40908.
  rewrite ?node_40909.
  rewrite ?node_40910.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40912 (s : N.State) (i : N.Inputs) :
  R.v40912 (state s) (inputs i) = Zmod.unsigned (N.v40912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40912 s i)) at 1.
  unfold R.v40912, N.v40912.
  rewrite ?node_40907.
  rewrite ?node_40911.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40913 (s : N.State) (i : N.Inputs) :
  R.v40913 (state s) (inputs i) = Zmod.unsigned (N.v40913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40913 s i)) at 1.
  unfold R.v40913, N.v40913.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40914 (s : N.State) (i : N.Inputs) :
  R.v40914 (state s) (inputs i) = Zmod.unsigned (N.v40914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40914 s i)) at 1.
  unfold R.v40914, N.v40914.
  rewrite ?node_8366.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40915 (s : N.State) (i : N.Inputs) :
  R.v40915 (state s) (inputs i) = Zmod.unsigned (N.v40915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40915 s i)) at 1.
  unfold R.v40915, N.v40915.
  unfold R.v6, N.v6.
  rewrite ?node_8362.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40916 (s : N.State) (i : N.Inputs) :
  R.v40916 (state s) (inputs i) = Zmod.unsigned (N.v40916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40916 s i)) at 1.
  unfold R.v40916, N.v40916.
  unfold R.v6, N.v6.
  rewrite ?node_8359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40917 (s : N.State) (i : N.Inputs) :
  R.v40917 (state s) (inputs i) = Zmod.unsigned (N.v40917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40917 s i)) at 1.
  unfold R.v40917, N.v40917.
  rewrite ?node_40915.
  rewrite ?node_40916.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40918 (s : N.State) (i : N.Inputs) :
  R.v40918 (state s) (inputs i) = Zmod.unsigned (N.v40918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40918 s i)) at 1.
  unfold R.v40918, N.v40918.
  unfold R.v16484, N.v16484.
  rewrite ?node_40917.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40919 (s : N.State) (i : N.Inputs) :
  R.v40919 (state s) (inputs i) = Zmod.unsigned (N.v40919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40919 s i)) at 1.
  unfold R.v40919, N.v40919.
  rewrite ?node_40914.
  rewrite ?node_40918.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40920 (s : N.State) (i : N.Inputs) :
  R.v40920 (state s) (inputs i) = Zmod.unsigned (N.v40920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40920 s i)) at 1.
  unfold R.v40920, N.v40920.
  unfold R.v6, N.v6.
  rewrite ?node_40919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40921 (s : N.State) (i : N.Inputs) :
  R.v40921 (state s) (inputs i) = Zmod.unsigned (N.v40921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40921 s i)) at 1.
  unfold R.v40921, N.v40921.
  rewrite ?node_8367.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40922 (s : N.State) (i : N.Inputs) :
  R.v40922 (state s) (inputs i) = Zmod.unsigned (N.v40922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40922 s i)) at 1.
  unfold R.v40922, N.v40922.
  unfold R.v6, N.v6.
  rewrite ?node_8499.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40923 (s : N.State) (i : N.Inputs) :
  R.v40923 (state s) (inputs i) = Zmod.unsigned (N.v40923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40923 s i)) at 1.
  unfold R.v40923, N.v40923.
  rewrite ?node_40921.
  rewrite ?node_40922.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40924 (s : N.State) (i : N.Inputs) :
  R.v40924 (state s) (inputs i) = Zmod.unsigned (N.v40924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40924 s i)) at 1.
  unfold R.v40924, N.v40924.
  rewrite ?node_40920.
  rewrite ?node_40923.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40925 (s : N.State) (i : N.Inputs) :
  R.v40925 (state s) (inputs i) = Zmod.unsigned (N.v40925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40925 s i)) at 1.
  unfold R.v40925, N.v40925.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40926 (s : N.State) (i : N.Inputs) :
  R.v40926 (state s) (inputs i) = Zmod.unsigned (N.v40926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40926 s i)) at 1.
  unfold R.v40926, N.v40926.
  rewrite ?node_8374.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40927 (s : N.State) (i : N.Inputs) :
  R.v40927 (state s) (inputs i) = Zmod.unsigned (N.v40927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40927 s i)) at 1.
  unfold R.v40927, N.v40927.
  unfold R.v6, N.v6.
  rewrite ?node_8370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40928 (s : N.State) (i : N.Inputs) :
  R.v40928 (state s) (inputs i) = Zmod.unsigned (N.v40928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40928 s i)) at 1.
  unfold R.v40928, N.v40928.
  unfold R.v6, N.v6.
  rewrite ?node_8367.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40929 (s : N.State) (i : N.Inputs) :
  R.v40929 (state s) (inputs i) = Zmod.unsigned (N.v40929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40929 s i)) at 1.
  unfold R.v40929, N.v40929.
  rewrite ?node_40927.
  rewrite ?node_40928.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40930 (s : N.State) (i : N.Inputs) :
  R.v40930 (state s) (inputs i) = Zmod.unsigned (N.v40930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40930 s i)) at 1.
  unfold R.v40930, N.v40930.
  unfold R.v16484, N.v16484.
  rewrite ?node_40929.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40931 (s : N.State) (i : N.Inputs) :
  R.v40931 (state s) (inputs i) = Zmod.unsigned (N.v40931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40931 s i)) at 1.
  unfold R.v40931, N.v40931.
  rewrite ?node_40926.
  rewrite ?node_40930.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40932 (s : N.State) (i : N.Inputs) :
  R.v40932 (state s) (inputs i) = Zmod.unsigned (N.v40932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40932 s i)) at 1.
  unfold R.v40932, N.v40932.
  unfold R.v6, N.v6.
  rewrite ?node_40931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40933 (s : N.State) (i : N.Inputs) :
  R.v40933 (state s) (inputs i) = Zmod.unsigned (N.v40933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40933 s i)) at 1.
  unfold R.v40933, N.v40933.
  rewrite ?node_8375.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40934 (s : N.State) (i : N.Inputs) :
  R.v40934 (state s) (inputs i) = Zmod.unsigned (N.v40934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40934 s i)) at 1.
  unfold R.v40934, N.v40934.
  unfold R.v6, N.v6.
  rewrite ?node_8523.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40935 (s : N.State) (i : N.Inputs) :
  R.v40935 (state s) (inputs i) = Zmod.unsigned (N.v40935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40935 s i)) at 1.
  unfold R.v40935, N.v40935.
  rewrite ?node_40933.
  rewrite ?node_40934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40936 (s : N.State) (i : N.Inputs) :
  R.v40936 (state s) (inputs i) = Zmod.unsigned (N.v40936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40936 s i)) at 1.
  unfold R.v40936, N.v40936.
  rewrite ?node_40932.
  rewrite ?node_40935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40937 (s : N.State) (i : N.Inputs) :
  R.v40937 (state s) (inputs i) = Zmod.unsigned (N.v40937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40937 s i)) at 1.
  unfold R.v40937, N.v40937.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40938 (s : N.State) (i : N.Inputs) :
  R.v40938 (state s) (inputs i) = Zmod.unsigned (N.v40938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40938 s i)) at 1.
  unfold R.v40938, N.v40938.
  unfold R.v6, N.v6.
  rewrite ?node_8380.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40939 (s : N.State) (i : N.Inputs) :
  R.v40939 (state s) (inputs i) = Zmod.unsigned (N.v40939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40939 s i)) at 1.
  unfold R.v40939, N.v40939.
  unfold R.v6, N.v6.
  rewrite ?node_8379.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40940 (s : N.State) (i : N.Inputs) :
  R.v40940 (state s) (inputs i) = Zmod.unsigned (N.v40940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40940 s i)) at 1.
  unfold R.v40940, N.v40940.
  rewrite ?node_40938.
  rewrite ?node_40939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40941 (s : N.State) (i : N.Inputs) :
  R.v40941 (state s) (inputs i) = Zmod.unsigned (N.v40941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40941 s i)) at 1.
  unfold R.v40941, N.v40941.
  unfold R.v16463, N.v16463.
  rewrite ?node_40940.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40942 (s : N.State) (i : N.Inputs) :
  R.v40942 (state s) (inputs i) = Zmod.unsigned (N.v40942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40942 s i)) at 1.
  unfold R.v40942, N.v40942.
  rewrite ?node_8381.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40943 (s : N.State) (i : N.Inputs) :
  R.v40943 (state s) (inputs i) = Zmod.unsigned (N.v40943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40943 s i)) at 1.
  unfold R.v40943, N.v40943.
  unfold R.v6, N.v6.
  rewrite ?node_8525.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40944 (s : N.State) (i : N.Inputs) :
  R.v40944 (state s) (inputs i) = Zmod.unsigned (N.v40944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40944 s i)) at 1.
  unfold R.v40944, N.v40944.
  rewrite ?node_40942.
  rewrite ?node_40943.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40945 (s : N.State) (i : N.Inputs) :
  R.v40945 (state s) (inputs i) = Zmod.unsigned (N.v40945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40945 s i)) at 1.
  unfold R.v40945, N.v40945.
  rewrite ?node_40941.
  rewrite ?node_40944.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40946 (s : N.State) (i : N.Inputs) :
  R.v40946 (state s) (inputs i) = Zmod.unsigned (N.v40946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40946 s i)) at 1.
  unfold R.v40946, N.v40946.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40947 (s : N.State) (i : N.Inputs) :
  R.v40947 (state s) (inputs i) = Zmod.unsigned (N.v40947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40947 s i)) at 1.
  unfold R.v40947, N.v40947.
  rewrite ?node_8453.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40948 (s : N.State) (i : N.Inputs) :
  R.v40948 (state s) (inputs i) = Zmod.unsigned (N.v40948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40948 s i)) at 1.
  unfold R.v40948, N.v40948.
  rewrite ?node_8449.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40949 (s : N.State) (i : N.Inputs) :
  R.v40949 (state s) (inputs i) = Zmod.unsigned (N.v40949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40949 s i)) at 1.
  unfold R.v40949, N.v40949.
  rewrite ?node_8441.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40950 (s : N.State) (i : N.Inputs) :
  R.v40950 (state s) (inputs i) = Zmod.unsigned (N.v40950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40950 s i)) at 1.
  unfold R.v40950, N.v40950.
  unfold R.v6, N.v6.
  rewrite ?node_8433.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40951 (s : N.State) (i : N.Inputs) :
  R.v40951 (state s) (inputs i) = Zmod.unsigned (N.v40951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40951 s i)) at 1.
  unfold R.v40951, N.v40951.
  unfold R.v6, N.v6.
  rewrite ?node_8426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40952 (s : N.State) (i : N.Inputs) :
  R.v40952 (state s) (inputs i) = Zmod.unsigned (N.v40952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40952 s i)) at 1.
  unfold R.v40952, N.v40952.
  rewrite ?node_40950.
  rewrite ?node_40951.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40953 (s : N.State) (i : N.Inputs) :
  R.v40953 (state s) (inputs i) = Zmod.unsigned (N.v40953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40953 s i)) at 1.
  unfold R.v40953, N.v40953.
  unfold R.v16484, N.v16484.
  rewrite ?node_40952.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40954 (s : N.State) (i : N.Inputs) :
  R.v40954 (state s) (inputs i) = Zmod.unsigned (N.v40954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40954 s i)) at 1.
  unfold R.v40954, N.v40954.
  rewrite ?node_40947.
  rewrite ?node_40948.
  rewrite ?node_40949.
  rewrite ?node_40953.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40955 (s : N.State) (i : N.Inputs) :
  R.v40955 (state s) (inputs i) = Zmod.unsigned (N.v40955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40955 s i)) at 1.
  unfold R.v40955, N.v40955.
  unfold R.v6, N.v6.
  rewrite ?node_40954.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40956 (s : N.State) (i : N.Inputs) :
  R.v40956 (state s) (inputs i) = Zmod.unsigned (N.v40956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40956 s i)) at 1.
  unfold R.v40956, N.v40956.
  rewrite ?node_8454.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40957 (s : N.State) (i : N.Inputs) :
  R.v40957 (state s) (inputs i) = Zmod.unsigned (N.v40957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40957 s i)) at 1.
  unfold R.v40957, N.v40957.
  unfold R.v6, N.v6.
  rewrite ?node_8582.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40958 (s : N.State) (i : N.Inputs) :
  R.v40958 (state s) (inputs i) = Zmod.unsigned (N.v40958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40958 s i)) at 1.
  unfold R.v40958, N.v40958.
  unfold R.v6, N.v6.
  rewrite ?node_8646.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40959 (s : N.State) (i : N.Inputs) :
  R.v40959 (state s) (inputs i) = Zmod.unsigned (N.v40959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40959 s i)) at 1.
  unfold R.v40959, N.v40959.
  rewrite ?node_40956.
  rewrite ?node_40957.
  rewrite ?node_40958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40960 (s : N.State) (i : N.Inputs) :
  R.v40960 (state s) (inputs i) = Zmod.unsigned (N.v40960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40960 s i)) at 1.
  unfold R.v40960, N.v40960.
  rewrite ?node_40955.
  rewrite ?node_40959.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40961 (s : N.State) (i : N.Inputs) :
  R.v40961 (state s) (inputs i) = Zmod.unsigned (N.v40961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40961 s i)) at 1.
  unfold R.v40961, N.v40961.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40962 (s : N.State) (i : N.Inputs) :
  R.v40962 (state s) (inputs i) = Zmod.unsigned (N.v40962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40962 s i)) at 1.
  unfold R.v40962, N.v40962.
  rewrite ?node_8441.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40963 (s : N.State) (i : N.Inputs) :
  R.v40963 (state s) (inputs i) = Zmod.unsigned (N.v40963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40963 s i)) at 1.
  unfold R.v40963, N.v40963.
  unfold R.v6, N.v6.
  rewrite ?node_8433.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40964 (s : N.State) (i : N.Inputs) :
  R.v40964 (state s) (inputs i) = Zmod.unsigned (N.v40964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40964 s i)) at 1.
  unfold R.v40964, N.v40964.
  unfold R.v6, N.v6.
  rewrite ?node_8426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40965 (s : N.State) (i : N.Inputs) :
  R.v40965 (state s) (inputs i) = Zmod.unsigned (N.v40965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40965 s i)) at 1.
  unfold R.v40965, N.v40965.
  rewrite ?node_40963.
  rewrite ?node_40964.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40966 (s : N.State) (i : N.Inputs) :
  R.v40966 (state s) (inputs i) = Zmod.unsigned (N.v40966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40966 s i)) at 1.
  unfold R.v40966, N.v40966.
  unfold R.v16484, N.v16484.
  rewrite ?node_40965.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40967 (s : N.State) (i : N.Inputs) :
  R.v40967 (state s) (inputs i) = Zmod.unsigned (N.v40967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40967 s i)) at 1.
  unfold R.v40967, N.v40967.
  rewrite ?node_40962.
  rewrite ?node_40966.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40968 (s : N.State) (i : N.Inputs) :
  R.v40968 (state s) (inputs i) = Zmod.unsigned (N.v40968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40968 s i)) at 1.
  unfold R.v40968, N.v40968.
  unfold R.v6, N.v6.
  rewrite ?node_40967.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40969 (s : N.State) (i : N.Inputs) :
  R.v40969 (state s) (inputs i) = Zmod.unsigned (N.v40969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40969 s i)) at 1.
  unfold R.v40969, N.v40969.
  rewrite ?node_8442.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40970 (s : N.State) (i : N.Inputs) :
  R.v40970 (state s) (inputs i) = Zmod.unsigned (N.v40970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40970 s i)) at 1.
  unfold R.v40970, N.v40970.
  unfold R.v6, N.v6.
  rewrite ?node_8582.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40971 (s : N.State) (i : N.Inputs) :
  R.v40971 (state s) (inputs i) = Zmod.unsigned (N.v40971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40971 s i)) at 1.
  unfold R.v40971, N.v40971.
  rewrite ?node_40969.
  rewrite ?node_40970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40972 (s : N.State) (i : N.Inputs) :
  R.v40972 (state s) (inputs i) = Zmod.unsigned (N.v40972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40972 s i)) at 1.
  unfold R.v40972, N.v40972.
  rewrite ?node_40968.
  rewrite ?node_40971.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40973 (s : N.State) (i : N.Inputs) :
  R.v40973 (state s) (inputs i) = Zmod.unsigned (N.v40973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40973 s i)) at 1.
  unfold R.v40973, N.v40973.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40974 (s : N.State) (i : N.Inputs) :
  R.v40974 (state s) (inputs i) = Zmod.unsigned (N.v40974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40974 s i)) at 1.
  unfold R.v40974, N.v40974.
  rewrite ?node_8453.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40975 (s : N.State) (i : N.Inputs) :
  R.v40975 (state s) (inputs i) = Zmod.unsigned (N.v40975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40975 s i)) at 1.
  unfold R.v40975, N.v40975.
  unfold R.v6, N.v6.
  rewrite ?node_8449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40976 (s : N.State) (i : N.Inputs) :
  R.v40976 (state s) (inputs i) = Zmod.unsigned (N.v40976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40976 s i)) at 1.
  unfold R.v40976, N.v40976.
  unfold R.v6, N.v6.
  rewrite ?node_8442.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40977 (s : N.State) (i : N.Inputs) :
  R.v40977 (state s) (inputs i) = Zmod.unsigned (N.v40977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40977 s i)) at 1.
  unfold R.v40977, N.v40977.
  rewrite ?node_40975.
  rewrite ?node_40976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40978 (s : N.State) (i : N.Inputs) :
  R.v40978 (state s) (inputs i) = Zmod.unsigned (N.v40978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40978 s i)) at 1.
  unfold R.v40978, N.v40978.
  unfold R.v16484, N.v16484.
  rewrite ?node_40977.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40979 (s : N.State) (i : N.Inputs) :
  R.v40979 (state s) (inputs i) = Zmod.unsigned (N.v40979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40979 s i)) at 1.
  unfold R.v40979, N.v40979.
  rewrite ?node_40974.
  rewrite ?node_40978.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40980 (s : N.State) (i : N.Inputs) :
  R.v40980 (state s) (inputs i) = Zmod.unsigned (N.v40980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40980 s i)) at 1.
  unfold R.v40980, N.v40980.
  unfold R.v6, N.v6.
  rewrite ?node_40979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40981 (s : N.State) (i : N.Inputs) :
  R.v40981 (state s) (inputs i) = Zmod.unsigned (N.v40981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40981 s i)) at 1.
  unfold R.v40981, N.v40981.
  rewrite ?node_8454.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40982 (s : N.State) (i : N.Inputs) :
  R.v40982 (state s) (inputs i) = Zmod.unsigned (N.v40982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40982 s i)) at 1.
  unfold R.v40982, N.v40982.
  unfold R.v6, N.v6.
  rewrite ?node_8646.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40983 (s : N.State) (i : N.Inputs) :
  R.v40983 (state s) (inputs i) = Zmod.unsigned (N.v40983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40983 s i)) at 1.
  unfold R.v40983, N.v40983.
  rewrite ?node_40981.
  rewrite ?node_40982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40984 (s : N.State) (i : N.Inputs) :
  R.v40984 (state s) (inputs i) = Zmod.unsigned (N.v40984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40984 s i)) at 1.
  unfold R.v40984, N.v40984.
  rewrite ?node_40980.
  rewrite ?node_40983.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40985 (s : N.State) (i : N.Inputs) :
  R.v40985 (state s) (inputs i) = Zmod.unsigned (N.v40985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40985 s i)) at 1.
  unfold R.v40985, N.v40985.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40986 (s : N.State) (i : N.Inputs) :
  R.v40986 (state s) (inputs i) = Zmod.unsigned (N.v40986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40986 s i)) at 1.
  unfold R.v40986, N.v40986.
  rewrite ?node_8479.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40987 (s : N.State) (i : N.Inputs) :
  R.v40987 (state s) (inputs i) = Zmod.unsigned (N.v40987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40987 s i)) at 1.
  unfold R.v40987, N.v40987.
  rewrite ?node_8475.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40988 (s : N.State) (i : N.Inputs) :
  R.v40988 (state s) (inputs i) = Zmod.unsigned (N.v40988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40988 s i)) at 1.
  unfold R.v40988, N.v40988.
  rewrite ?node_8471.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40989 (s : N.State) (i : N.Inputs) :
  R.v40989 (state s) (inputs i) = Zmod.unsigned (N.v40989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40989 s i)) at 1.
  unfold R.v40989, N.v40989.
  unfold R.v6, N.v6.
  rewrite ?node_8468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40990 (s : N.State) (i : N.Inputs) :
  R.v40990 (state s) (inputs i) = Zmod.unsigned (N.v40990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40990 s i)) at 1.
  unfold R.v40990, N.v40990.
  unfold R.v6, N.v6.
  rewrite ?node_8461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40991 (s : N.State) (i : N.Inputs) :
  R.v40991 (state s) (inputs i) = Zmod.unsigned (N.v40991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40991 s i)) at 1.
  unfold R.v40991, N.v40991.
  rewrite ?node_40989.
  rewrite ?node_40990.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40992 (s : N.State) (i : N.Inputs) :
  R.v40992 (state s) (inputs i) = Zmod.unsigned (N.v40992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40992 s i)) at 1.
  unfold R.v40992, N.v40992.
  unfold R.v16484, N.v16484.
  rewrite ?node_40991.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40993 (s : N.State) (i : N.Inputs) :
  R.v40993 (state s) (inputs i) = Zmod.unsigned (N.v40993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40993 s i)) at 1.
  unfold R.v40993, N.v40993.
  rewrite ?node_40986.
  rewrite ?node_40987.
  rewrite ?node_40988.
  rewrite ?node_40992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40994 (s : N.State) (i : N.Inputs) :
  R.v40994 (state s) (inputs i) = Zmod.unsigned (N.v40994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40994 s i)) at 1.
  unfold R.v40994, N.v40994.
  unfold R.v6, N.v6.
  rewrite ?node_40993.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40995 (s : N.State) (i : N.Inputs) :
  R.v40995 (state s) (inputs i) = Zmod.unsigned (N.v40995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40995 s i)) at 1.
  unfold R.v40995, N.v40995.
  rewrite ?node_8480.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40996 (s : N.State) (i : N.Inputs) :
  R.v40996 (state s) (inputs i) = Zmod.unsigned (N.v40996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40996 s i)) at 1.
  unfold R.v40996, N.v40996.
  unfold R.v6, N.v6.
  rewrite ?node_8609.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40997 (s : N.State) (i : N.Inputs) :
  R.v40997 (state s) (inputs i) = Zmod.unsigned (N.v40997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40997 s i)) at 1.
  unfold R.v40997, N.v40997.
  unfold R.v6, N.v6.
  rewrite ?node_8649.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40998 (s : N.State) (i : N.Inputs) :
  R.v40998 (state s) (inputs i) = Zmod.unsigned (N.v40998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40998 s i)) at 1.
  unfold R.v40998, N.v40998.
  rewrite ?node_40995.
  rewrite ?node_40996.
  rewrite ?node_40997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40999 (s : N.State) (i : N.Inputs) :
  R.v40999 (state s) (inputs i) = Zmod.unsigned (N.v40999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40999 s i)) at 1.
  unfold R.v40999, N.v40999.
  rewrite ?node_40994.
  rewrite ?node_40998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
