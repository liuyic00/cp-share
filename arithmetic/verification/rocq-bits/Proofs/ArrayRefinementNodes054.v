(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes053.
Lemma node_54000 (s : N.State) (i : N.Inputs) :
  R.v54000 (state s) (inputs i) = Zmod.unsigned (N.v54000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54000 s i)) at 1.
  unfold R.v54000, N.v54000.
  rewrite ?node_53995.
  rewrite ?node_53999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54001 (s : N.State) (i : N.Inputs) :
  R.v54001 (state s) (inputs i) = Zmod.unsigned (N.v54001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54001 s i)) at 1.
  unfold R.v54001, N.v54001.
  unfold R.v6, N.v6.
  rewrite ?node_54000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54002 (s : N.State) (i : N.Inputs) :
  R.v54002 (state s) (inputs i) = Zmod.unsigned (N.v54002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54002 s i)) at 1.
  unfold R.v54002, N.v54002.
  rewrite ?node_15560.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54003 (s : N.State) (i : N.Inputs) :
  R.v54003 (state s) (inputs i) = Zmod.unsigned (N.v54003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54003 s i)) at 1.
  unfold R.v54003, N.v54003.
  unfold R.v6, N.v6.
  rewrite ?node_15618.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54004 (s : N.State) (i : N.Inputs) :
  R.v54004 (state s) (inputs i) = Zmod.unsigned (N.v54004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54004 s i)) at 1.
  unfold R.v54004, N.v54004.
  rewrite ?node_54002.
  rewrite ?node_54003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54005 (s : N.State) (i : N.Inputs) :
  R.v54005 (state s) (inputs i) = Zmod.unsigned (N.v54005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54005 s i)) at 1.
  unfold R.v54005, N.v54005.
  rewrite ?node_54001.
  rewrite ?node_54004.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54006 (s : N.State) (i : N.Inputs) :
  R.v54006 (state s) (inputs i) = Zmod.unsigned (N.v54006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54006 s i)) at 1.
  unfold R.v54006, N.v54006.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54007 (s : N.State) (i : N.Inputs) :
  R.v54007 (state s) (inputs i) = Zmod.unsigned (N.v54007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54007 s i)) at 1.
  unfold R.v54007, N.v54007.
  rewrite ?node_15614.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54008 (s : N.State) (i : N.Inputs) :
  R.v54008 (state s) (inputs i) = Zmod.unsigned (N.v54008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54008 s i)) at 1.
  unfold R.v54008, N.v54008.
  rewrite ?node_15610.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54009 (s : N.State) (i : N.Inputs) :
  R.v54009 (state s) (inputs i) = Zmod.unsigned (N.v54009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54009 s i)) at 1.
  unfold R.v54009, N.v54009.
  rewrite ?node_15606.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54010 (s : N.State) (i : N.Inputs) :
  R.v54010 (state s) (inputs i) = Zmod.unsigned (N.v54010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54010 s i)) at 1.
  unfold R.v54010, N.v54010.
  unfold R.v6, N.v6.
  rewrite ?node_15602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54011 (s : N.State) (i : N.Inputs) :
  R.v54011 (state s) (inputs i) = Zmod.unsigned (N.v54011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54011 s i)) at 1.
  unfold R.v54011, N.v54011.
  unfold R.v6, N.v6.
  rewrite ?node_15595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54012 (s : N.State) (i : N.Inputs) :
  R.v54012 (state s) (inputs i) = Zmod.unsigned (N.v54012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54012 s i)) at 1.
  unfold R.v54012, N.v54012.
  rewrite ?node_54010.
  rewrite ?node_54011.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54013 (s : N.State) (i : N.Inputs) :
  R.v54013 (state s) (inputs i) = Zmod.unsigned (N.v54013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54013 s i)) at 1.
  unfold R.v54013, N.v54013.
  unfold R.v16484, N.v16484.
  rewrite ?node_54012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54014 (s : N.State) (i : N.Inputs) :
  R.v54014 (state s) (inputs i) = Zmod.unsigned (N.v54014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54014 s i)) at 1.
  unfold R.v54014, N.v54014.
  rewrite ?node_54007.
  rewrite ?node_54008.
  rewrite ?node_54009.
  rewrite ?node_54013.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54015 (s : N.State) (i : N.Inputs) :
  R.v54015 (state s) (inputs i) = Zmod.unsigned (N.v54015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54015 s i)) at 1.
  unfold R.v54015, N.v54015.
  unfold R.v6, N.v6.
  rewrite ?node_54014.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54016 (s : N.State) (i : N.Inputs) :
  R.v54016 (state s) (inputs i) = Zmod.unsigned (N.v54016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54016 s i)) at 1.
  unfold R.v54016, N.v54016.
  rewrite ?node_15615.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54017 (s : N.State) (i : N.Inputs) :
  R.v54017 (state s) (inputs i) = Zmod.unsigned (N.v54017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54017 s i)) at 1.
  unfold R.v54017, N.v54017.
  unfold R.v6, N.v6.
  rewrite ?node_15665.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54018 (s : N.State) (i : N.Inputs) :
  R.v54018 (state s) (inputs i) = Zmod.unsigned (N.v54018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54018 s i)) at 1.
  unfold R.v54018, N.v54018.
  unfold R.v6, N.v6.
  rewrite ?node_15669.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54019 (s : N.State) (i : N.Inputs) :
  R.v54019 (state s) (inputs i) = Zmod.unsigned (N.v54019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54019 s i)) at 1.
  unfold R.v54019, N.v54019.
  rewrite ?node_54016.
  rewrite ?node_54017.
  rewrite ?node_54018.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54020 (s : N.State) (i : N.Inputs) :
  R.v54020 (state s) (inputs i) = Zmod.unsigned (N.v54020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54020 s i)) at 1.
  unfold R.v54020, N.v54020.
  rewrite ?node_54015.
  rewrite ?node_54019.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54021 (s : N.State) (i : N.Inputs) :
  R.v54021 (state s) (inputs i) = Zmod.unsigned (N.v54021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54021 s i)) at 1.
  unfold R.v54021, N.v54021.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54022 (s : N.State) (i : N.Inputs) :
  R.v54022 (state s) (inputs i) = Zmod.unsigned (N.v54022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54022 s i)) at 1.
  unfold R.v54022, N.v54022.
  rewrite ?node_15606.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54023 (s : N.State) (i : N.Inputs) :
  R.v54023 (state s) (inputs i) = Zmod.unsigned (N.v54023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54023 s i)) at 1.
  unfold R.v54023, N.v54023.
  unfold R.v6, N.v6.
  rewrite ?node_15602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54024 (s : N.State) (i : N.Inputs) :
  R.v54024 (state s) (inputs i) = Zmod.unsigned (N.v54024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54024 s i)) at 1.
  unfold R.v54024, N.v54024.
  unfold R.v6, N.v6.
  rewrite ?node_15595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54025 (s : N.State) (i : N.Inputs) :
  R.v54025 (state s) (inputs i) = Zmod.unsigned (N.v54025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54025 s i)) at 1.
  unfold R.v54025, N.v54025.
  rewrite ?node_54023.
  rewrite ?node_54024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54026 (s : N.State) (i : N.Inputs) :
  R.v54026 (state s) (inputs i) = Zmod.unsigned (N.v54026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54026 s i)) at 1.
  unfold R.v54026, N.v54026.
  unfold R.v16484, N.v16484.
  rewrite ?node_54025.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54027 (s : N.State) (i : N.Inputs) :
  R.v54027 (state s) (inputs i) = Zmod.unsigned (N.v54027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54027 s i)) at 1.
  unfold R.v54027, N.v54027.
  rewrite ?node_54022.
  rewrite ?node_54026.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54028 (s : N.State) (i : N.Inputs) :
  R.v54028 (state s) (inputs i) = Zmod.unsigned (N.v54028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54028 s i)) at 1.
  unfold R.v54028, N.v54028.
  unfold R.v6, N.v6.
  rewrite ?node_54027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54029 (s : N.State) (i : N.Inputs) :
  R.v54029 (state s) (inputs i) = Zmod.unsigned (N.v54029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54029 s i)) at 1.
  unfold R.v54029, N.v54029.
  rewrite ?node_15607.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54030 (s : N.State) (i : N.Inputs) :
  R.v54030 (state s) (inputs i) = Zmod.unsigned (N.v54030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54030 s i)) at 1.
  unfold R.v54030, N.v54030.
  unfold R.v6, N.v6.
  rewrite ?node_15665.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54031 (s : N.State) (i : N.Inputs) :
  R.v54031 (state s) (inputs i) = Zmod.unsigned (N.v54031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54031 s i)) at 1.
  unfold R.v54031, N.v54031.
  rewrite ?node_54029.
  rewrite ?node_54030.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54032 (s : N.State) (i : N.Inputs) :
  R.v54032 (state s) (inputs i) = Zmod.unsigned (N.v54032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54032 s i)) at 1.
  unfold R.v54032, N.v54032.
  rewrite ?node_54028.
  rewrite ?node_54031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54033 (s : N.State) (i : N.Inputs) :
  R.v54033 (state s) (inputs i) = Zmod.unsigned (N.v54033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54033 s i)) at 1.
  unfold R.v54033, N.v54033.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54034 (s : N.State) (i : N.Inputs) :
  R.v54034 (state s) (inputs i) = Zmod.unsigned (N.v54034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54034 s i)) at 1.
  unfold R.v54034, N.v54034.
  rewrite ?node_15614.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54035 (s : N.State) (i : N.Inputs) :
  R.v54035 (state s) (inputs i) = Zmod.unsigned (N.v54035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54035 s i)) at 1.
  unfold R.v54035, N.v54035.
  unfold R.v6, N.v6.
  rewrite ?node_15610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54036 (s : N.State) (i : N.Inputs) :
  R.v54036 (state s) (inputs i) = Zmod.unsigned (N.v54036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54036 s i)) at 1.
  unfold R.v54036, N.v54036.
  unfold R.v6, N.v6.
  rewrite ?node_15607.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54037 (s : N.State) (i : N.Inputs) :
  R.v54037 (state s) (inputs i) = Zmod.unsigned (N.v54037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54037 s i)) at 1.
  unfold R.v54037, N.v54037.
  rewrite ?node_54035.
  rewrite ?node_54036.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54038 (s : N.State) (i : N.Inputs) :
  R.v54038 (state s) (inputs i) = Zmod.unsigned (N.v54038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54038 s i)) at 1.
  unfold R.v54038, N.v54038.
  unfold R.v16484, N.v16484.
  rewrite ?node_54037.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54039 (s : N.State) (i : N.Inputs) :
  R.v54039 (state s) (inputs i) = Zmod.unsigned (N.v54039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54039 s i)) at 1.
  unfold R.v54039, N.v54039.
  rewrite ?node_54034.
  rewrite ?node_54038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54040 (s : N.State) (i : N.Inputs) :
  R.v54040 (state s) (inputs i) = Zmod.unsigned (N.v54040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54040 s i)) at 1.
  unfold R.v54040, N.v54040.
  unfold R.v6, N.v6.
  rewrite ?node_54039.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54041 (s : N.State) (i : N.Inputs) :
  R.v54041 (state s) (inputs i) = Zmod.unsigned (N.v54041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54041 s i)) at 1.
  unfold R.v54041, N.v54041.
  rewrite ?node_15615.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54042 (s : N.State) (i : N.Inputs) :
  R.v54042 (state s) (inputs i) = Zmod.unsigned (N.v54042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54042 s i)) at 1.
  unfold R.v54042, N.v54042.
  unfold R.v6, N.v6.
  rewrite ?node_15669.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54043 (s : N.State) (i : N.Inputs) :
  R.v54043 (state s) (inputs i) = Zmod.unsigned (N.v54043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54043 s i)) at 1.
  unfold R.v54043, N.v54043.
  rewrite ?node_54041.
  rewrite ?node_54042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54044 (s : N.State) (i : N.Inputs) :
  R.v54044 (state s) (inputs i) = Zmod.unsigned (N.v54044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54044 s i)) at 1.
  unfold R.v54044, N.v54044.
  rewrite ?node_54040.
  rewrite ?node_54043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54045 (s : N.State) (i : N.Inputs) :
  R.v54045 (state s) (inputs i) = Zmod.unsigned (N.v54045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54045 s i)) at 1.
  unfold R.v54045, N.v54045.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54046 (s : N.State) (i : N.Inputs) :
  R.v54046 (state s) (inputs i) = Zmod.unsigned (N.v54046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54046 s i)) at 1.
  unfold R.v54046, N.v54046.
  rewrite ?node_15665.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54047 (s : N.State) (i : N.Inputs) :
  R.v54047 (state s) (inputs i) = Zmod.unsigned (N.v54047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54047 s i)) at 1.
  unfold R.v54047, N.v54047.
  rewrite ?node_15661.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54048 (s : N.State) (i : N.Inputs) :
  R.v54048 (state s) (inputs i) = Zmod.unsigned (N.v54048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54048 s i)) at 1.
  unfold R.v54048, N.v54048.
  rewrite ?node_15659.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54049 (s : N.State) (i : N.Inputs) :
  R.v54049 (state s) (inputs i) = Zmod.unsigned (N.v54049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54049 s i)) at 1.
  unfold R.v54049, N.v54049.
  unfold R.v6, N.v6.
  rewrite ?node_15655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54050 (s : N.State) (i : N.Inputs) :
  R.v54050 (state s) (inputs i) = Zmod.unsigned (N.v54050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54050 s i)) at 1.
  unfold R.v54050, N.v54050.
  unfold R.v6, N.v6.
  rewrite ?node_15648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54051 (s : N.State) (i : N.Inputs) :
  R.v54051 (state s) (inputs i) = Zmod.unsigned (N.v54051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54051 s i)) at 1.
  unfold R.v54051, N.v54051.
  rewrite ?node_54049.
  rewrite ?node_54050.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54052 (s : N.State) (i : N.Inputs) :
  R.v54052 (state s) (inputs i) = Zmod.unsigned (N.v54052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54052 s i)) at 1.
  unfold R.v54052, N.v54052.
  unfold R.v16484, N.v16484.
  rewrite ?node_54051.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54053 (s : N.State) (i : N.Inputs) :
  R.v54053 (state s) (inputs i) = Zmod.unsigned (N.v54053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54053 s i)) at 1.
  unfold R.v54053, N.v54053.
  rewrite ?node_54046.
  rewrite ?node_54047.
  rewrite ?node_54048.
  rewrite ?node_54052.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54054 (s : N.State) (i : N.Inputs) :
  R.v54054 (state s) (inputs i) = Zmod.unsigned (N.v54054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54054 s i)) at 1.
  unfold R.v54054, N.v54054.
  unfold R.v6, N.v6.
  rewrite ?node_54053.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54055 (s : N.State) (i : N.Inputs) :
  R.v54055 (state s) (inputs i) = Zmod.unsigned (N.v54055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54055 s i)) at 1.
  unfold R.v54055, N.v54055.
  rewrite ?node_15666.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54056 (s : N.State) (i : N.Inputs) :
  R.v54056 (state s) (inputs i) = Zmod.unsigned (N.v54056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54056 s i)) at 1.
  unfold R.v54056, N.v54056.
  unfold R.v6, N.v6.
  rewrite ?node_15715.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54057 (s : N.State) (i : N.Inputs) :
  R.v54057 (state s) (inputs i) = Zmod.unsigned (N.v54057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54057 s i)) at 1.
  unfold R.v54057, N.v54057.
  unfold R.v6, N.v6.
  rewrite ?node_15719.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54058 (s : N.State) (i : N.Inputs) :
  R.v54058 (state s) (inputs i) = Zmod.unsigned (N.v54058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54058 s i)) at 1.
  unfold R.v54058, N.v54058.
  rewrite ?node_54055.
  rewrite ?node_54056.
  rewrite ?node_54057.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54059 (s : N.State) (i : N.Inputs) :
  R.v54059 (state s) (inputs i) = Zmod.unsigned (N.v54059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54059 s i)) at 1.
  unfold R.v54059, N.v54059.
  rewrite ?node_54054.
  rewrite ?node_54058.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54060 (s : N.State) (i : N.Inputs) :
  R.v54060 (state s) (inputs i) = Zmod.unsigned (N.v54060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54060 s i)) at 1.
  unfold R.v54060, N.v54060.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54061 (s : N.State) (i : N.Inputs) :
  R.v54061 (state s) (inputs i) = Zmod.unsigned (N.v54061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54061 s i)) at 1.
  unfold R.v54061, N.v54061.
  rewrite ?node_15659.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54062 (s : N.State) (i : N.Inputs) :
  R.v54062 (state s) (inputs i) = Zmod.unsigned (N.v54062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54062 s i)) at 1.
  unfold R.v54062, N.v54062.
  unfold R.v6, N.v6.
  rewrite ?node_15655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54063 (s : N.State) (i : N.Inputs) :
  R.v54063 (state s) (inputs i) = Zmod.unsigned (N.v54063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54063 s i)) at 1.
  unfold R.v54063, N.v54063.
  unfold R.v6, N.v6.
  rewrite ?node_15648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54064 (s : N.State) (i : N.Inputs) :
  R.v54064 (state s) (inputs i) = Zmod.unsigned (N.v54064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54064 s i)) at 1.
  unfold R.v54064, N.v54064.
  rewrite ?node_54062.
  rewrite ?node_54063.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54065 (s : N.State) (i : N.Inputs) :
  R.v54065 (state s) (inputs i) = Zmod.unsigned (N.v54065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54065 s i)) at 1.
  unfold R.v54065, N.v54065.
  unfold R.v16484, N.v16484.
  rewrite ?node_54064.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54066 (s : N.State) (i : N.Inputs) :
  R.v54066 (state s) (inputs i) = Zmod.unsigned (N.v54066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54066 s i)) at 1.
  unfold R.v54066, N.v54066.
  rewrite ?node_54061.
  rewrite ?node_54065.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54067 (s : N.State) (i : N.Inputs) :
  R.v54067 (state s) (inputs i) = Zmod.unsigned (N.v54067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54067 s i)) at 1.
  unfold R.v54067, N.v54067.
  unfold R.v6, N.v6.
  rewrite ?node_54066.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54068 (s : N.State) (i : N.Inputs) :
  R.v54068 (state s) (inputs i) = Zmod.unsigned (N.v54068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54068 s i)) at 1.
  unfold R.v54068, N.v54068.
  rewrite ?node_15660.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54069 (s : N.State) (i : N.Inputs) :
  R.v54069 (state s) (inputs i) = Zmod.unsigned (N.v54069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54069 s i)) at 1.
  unfold R.v54069, N.v54069.
  unfold R.v6, N.v6.
  rewrite ?node_15715.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54070 (s : N.State) (i : N.Inputs) :
  R.v54070 (state s) (inputs i) = Zmod.unsigned (N.v54070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54070 s i)) at 1.
  unfold R.v54070, N.v54070.
  rewrite ?node_54068.
  rewrite ?node_54069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54071 (s : N.State) (i : N.Inputs) :
  R.v54071 (state s) (inputs i) = Zmod.unsigned (N.v54071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54071 s i)) at 1.
  unfold R.v54071, N.v54071.
  rewrite ?node_54067.
  rewrite ?node_54070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54072 (s : N.State) (i : N.Inputs) :
  R.v54072 (state s) (inputs i) = Zmod.unsigned (N.v54072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54072 s i)) at 1.
  unfold R.v54072, N.v54072.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54073 (s : N.State) (i : N.Inputs) :
  R.v54073 (state s) (inputs i) = Zmod.unsigned (N.v54073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54073 s i)) at 1.
  unfold R.v54073, N.v54073.
  rewrite ?node_15665.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54074 (s : N.State) (i : N.Inputs) :
  R.v54074 (state s) (inputs i) = Zmod.unsigned (N.v54074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54074 s i)) at 1.
  unfold R.v54074, N.v54074.
  unfold R.v6, N.v6.
  rewrite ?node_15661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54075 (s : N.State) (i : N.Inputs) :
  R.v54075 (state s) (inputs i) = Zmod.unsigned (N.v54075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54075 s i)) at 1.
  unfold R.v54075, N.v54075.
  unfold R.v6, N.v6.
  rewrite ?node_15660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54076 (s : N.State) (i : N.Inputs) :
  R.v54076 (state s) (inputs i) = Zmod.unsigned (N.v54076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54076 s i)) at 1.
  unfold R.v54076, N.v54076.
  rewrite ?node_54074.
  rewrite ?node_54075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54077 (s : N.State) (i : N.Inputs) :
  R.v54077 (state s) (inputs i) = Zmod.unsigned (N.v54077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54077 s i)) at 1.
  unfold R.v54077, N.v54077.
  unfold R.v16484, N.v16484.
  rewrite ?node_54076.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54078 (s : N.State) (i : N.Inputs) :
  R.v54078 (state s) (inputs i) = Zmod.unsigned (N.v54078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54078 s i)) at 1.
  unfold R.v54078, N.v54078.
  rewrite ?node_54073.
  rewrite ?node_54077.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54079 (s : N.State) (i : N.Inputs) :
  R.v54079 (state s) (inputs i) = Zmod.unsigned (N.v54079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54079 s i)) at 1.
  unfold R.v54079, N.v54079.
  unfold R.v6, N.v6.
  rewrite ?node_54078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54080 (s : N.State) (i : N.Inputs) :
  R.v54080 (state s) (inputs i) = Zmod.unsigned (N.v54080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54080 s i)) at 1.
  unfold R.v54080, N.v54080.
  rewrite ?node_15666.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54081 (s : N.State) (i : N.Inputs) :
  R.v54081 (state s) (inputs i) = Zmod.unsigned (N.v54081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54081 s i)) at 1.
  unfold R.v54081, N.v54081.
  unfold R.v6, N.v6.
  rewrite ?node_15719.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54082 (s : N.State) (i : N.Inputs) :
  R.v54082 (state s) (inputs i) = Zmod.unsigned (N.v54082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54082 s i)) at 1.
  unfold R.v54082, N.v54082.
  rewrite ?node_54080.
  rewrite ?node_54081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54083 (s : N.State) (i : N.Inputs) :
  R.v54083 (state s) (inputs i) = Zmod.unsigned (N.v54083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54083 s i)) at 1.
  unfold R.v54083, N.v54083.
  rewrite ?node_54079.
  rewrite ?node_54082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54084 (s : N.State) (i : N.Inputs) :
  R.v54084 (state s) (inputs i) = Zmod.unsigned (N.v54084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54084 s i)) at 1.
  unfold R.v54084, N.v54084.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54085 (s : N.State) (i : N.Inputs) :
  R.v54085 (state s) (inputs i) = Zmod.unsigned (N.v54085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54085 s i)) at 1.
  unfold R.v54085, N.v54085.
  rewrite ?node_15715.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54086 (s : N.State) (i : N.Inputs) :
  R.v54086 (state s) (inputs i) = Zmod.unsigned (N.v54086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54086 s i)) at 1.
  unfold R.v54086, N.v54086.
  rewrite ?node_15711.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54087 (s : N.State) (i : N.Inputs) :
  R.v54087 (state s) (inputs i) = Zmod.unsigned (N.v54087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54087 s i)) at 1.
  unfold R.v54087, N.v54087.
  rewrite ?node_15709.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54088 (s : N.State) (i : N.Inputs) :
  R.v54088 (state s) (inputs i) = Zmod.unsigned (N.v54088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54088 s i)) at 1.
  unfold R.v54088, N.v54088.
  unfold R.v6, N.v6.
  rewrite ?node_15705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54089 (s : N.State) (i : N.Inputs) :
  R.v54089 (state s) (inputs i) = Zmod.unsigned (N.v54089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54089 s i)) at 1.
  unfold R.v54089, N.v54089.
  unfold R.v6, N.v6.
  rewrite ?node_15700.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54090 (s : N.State) (i : N.Inputs) :
  R.v54090 (state s) (inputs i) = Zmod.unsigned (N.v54090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54090 s i)) at 1.
  unfold R.v54090, N.v54090.
  rewrite ?node_54088.
  rewrite ?node_54089.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54091 (s : N.State) (i : N.Inputs) :
  R.v54091 (state s) (inputs i) = Zmod.unsigned (N.v54091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54091 s i)) at 1.
  unfold R.v54091, N.v54091.
  unfold R.v16484, N.v16484.
  rewrite ?node_54090.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54092 (s : N.State) (i : N.Inputs) :
  R.v54092 (state s) (inputs i) = Zmod.unsigned (N.v54092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54092 s i)) at 1.
  unfold R.v54092, N.v54092.
  rewrite ?node_54085.
  rewrite ?node_54086.
  rewrite ?node_54087.
  rewrite ?node_54091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54093 (s : N.State) (i : N.Inputs) :
  R.v54093 (state s) (inputs i) = Zmod.unsigned (N.v54093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54093 s i)) at 1.
  unfold R.v54093, N.v54093.
  unfold R.v6, N.v6.
  rewrite ?node_54092.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54094 (s : N.State) (i : N.Inputs) :
  R.v54094 (state s) (inputs i) = Zmod.unsigned (N.v54094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54094 s i)) at 1.
  unfold R.v54094, N.v54094.
  rewrite ?node_15716.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54095 (s : N.State) (i : N.Inputs) :
  R.v54095 (state s) (inputs i) = Zmod.unsigned (N.v54095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54095 s i)) at 1.
  unfold R.v54095, N.v54095.
  unfold R.v6, N.v6.
  rewrite ?node_15763.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54096 (s : N.State) (i : N.Inputs) :
  R.v54096 (state s) (inputs i) = Zmod.unsigned (N.v54096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54096 s i)) at 1.
  unfold R.v54096, N.v54096.
  unfold R.v6, N.v6.
  rewrite ?node_15767.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54097 (s : N.State) (i : N.Inputs) :
  R.v54097 (state s) (inputs i) = Zmod.unsigned (N.v54097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54097 s i)) at 1.
  unfold R.v54097, N.v54097.
  rewrite ?node_54094.
  rewrite ?node_54095.
  rewrite ?node_54096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54098 (s : N.State) (i : N.Inputs) :
  R.v54098 (state s) (inputs i) = Zmod.unsigned (N.v54098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54098 s i)) at 1.
  unfold R.v54098, N.v54098.
  rewrite ?node_54093.
  rewrite ?node_54097.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54099 (s : N.State) (i : N.Inputs) :
  R.v54099 (state s) (inputs i) = Zmod.unsigned (N.v54099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54099 s i)) at 1.
  unfold R.v54099, N.v54099.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54100 (s : N.State) (i : N.Inputs) :
  R.v54100 (state s) (inputs i) = Zmod.unsigned (N.v54100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54100 s i)) at 1.
  unfold R.v54100, N.v54100.
  rewrite ?node_15709.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54101 (s : N.State) (i : N.Inputs) :
  R.v54101 (state s) (inputs i) = Zmod.unsigned (N.v54101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54101 s i)) at 1.
  unfold R.v54101, N.v54101.
  unfold R.v6, N.v6.
  rewrite ?node_15705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54102 (s : N.State) (i : N.Inputs) :
  R.v54102 (state s) (inputs i) = Zmod.unsigned (N.v54102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54102 s i)) at 1.
  unfold R.v54102, N.v54102.
  unfold R.v6, N.v6.
  rewrite ?node_15700.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54103 (s : N.State) (i : N.Inputs) :
  R.v54103 (state s) (inputs i) = Zmod.unsigned (N.v54103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54103 s i)) at 1.
  unfold R.v54103, N.v54103.
  rewrite ?node_54101.
  rewrite ?node_54102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54104 (s : N.State) (i : N.Inputs) :
  R.v54104 (state s) (inputs i) = Zmod.unsigned (N.v54104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54104 s i)) at 1.
  unfold R.v54104, N.v54104.
  unfold R.v16484, N.v16484.
  rewrite ?node_54103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54105 (s : N.State) (i : N.Inputs) :
  R.v54105 (state s) (inputs i) = Zmod.unsigned (N.v54105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54105 s i)) at 1.
  unfold R.v54105, N.v54105.
  rewrite ?node_54100.
  rewrite ?node_54104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54106 (s : N.State) (i : N.Inputs) :
  R.v54106 (state s) (inputs i) = Zmod.unsigned (N.v54106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54106 s i)) at 1.
  unfold R.v54106, N.v54106.
  unfold R.v6, N.v6.
  rewrite ?node_54105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54107 (s : N.State) (i : N.Inputs) :
  R.v54107 (state s) (inputs i) = Zmod.unsigned (N.v54107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54107 s i)) at 1.
  unfold R.v54107, N.v54107.
  rewrite ?node_15710.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54108 (s : N.State) (i : N.Inputs) :
  R.v54108 (state s) (inputs i) = Zmod.unsigned (N.v54108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54108 s i)) at 1.
  unfold R.v54108, N.v54108.
  unfold R.v6, N.v6.
  rewrite ?node_15763.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54109 (s : N.State) (i : N.Inputs) :
  R.v54109 (state s) (inputs i) = Zmod.unsigned (N.v54109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54109 s i)) at 1.
  unfold R.v54109, N.v54109.
  rewrite ?node_54107.
  rewrite ?node_54108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54110 (s : N.State) (i : N.Inputs) :
  R.v54110 (state s) (inputs i) = Zmod.unsigned (N.v54110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54110 s i)) at 1.
  unfold R.v54110, N.v54110.
  rewrite ?node_54106.
  rewrite ?node_54109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54111 (s : N.State) (i : N.Inputs) :
  R.v54111 (state s) (inputs i) = Zmod.unsigned (N.v54111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54111 s i)) at 1.
  unfold R.v54111, N.v54111.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54112 (s : N.State) (i : N.Inputs) :
  R.v54112 (state s) (inputs i) = Zmod.unsigned (N.v54112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54112 s i)) at 1.
  unfold R.v54112, N.v54112.
  rewrite ?node_15715.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54113 (s : N.State) (i : N.Inputs) :
  R.v54113 (state s) (inputs i) = Zmod.unsigned (N.v54113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54113 s i)) at 1.
  unfold R.v54113, N.v54113.
  unfold R.v6, N.v6.
  rewrite ?node_15711.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54114 (s : N.State) (i : N.Inputs) :
  R.v54114 (state s) (inputs i) = Zmod.unsigned (N.v54114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54114 s i)) at 1.
  unfold R.v54114, N.v54114.
  unfold R.v6, N.v6.
  rewrite ?node_15710.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54115 (s : N.State) (i : N.Inputs) :
  R.v54115 (state s) (inputs i) = Zmod.unsigned (N.v54115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54115 s i)) at 1.
  unfold R.v54115, N.v54115.
  rewrite ?node_54113.
  rewrite ?node_54114.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54116 (s : N.State) (i : N.Inputs) :
  R.v54116 (state s) (inputs i) = Zmod.unsigned (N.v54116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54116 s i)) at 1.
  unfold R.v54116, N.v54116.
  unfold R.v16484, N.v16484.
  rewrite ?node_54115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54117 (s : N.State) (i : N.Inputs) :
  R.v54117 (state s) (inputs i) = Zmod.unsigned (N.v54117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54117 s i)) at 1.
  unfold R.v54117, N.v54117.
  rewrite ?node_54112.
  rewrite ?node_54116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54118 (s : N.State) (i : N.Inputs) :
  R.v54118 (state s) (inputs i) = Zmod.unsigned (N.v54118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54118 s i)) at 1.
  unfold R.v54118, N.v54118.
  unfold R.v6, N.v6.
  rewrite ?node_54117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54119 (s : N.State) (i : N.Inputs) :
  R.v54119 (state s) (inputs i) = Zmod.unsigned (N.v54119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54119 s i)) at 1.
  unfold R.v54119, N.v54119.
  rewrite ?node_15716.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54120 (s : N.State) (i : N.Inputs) :
  R.v54120 (state s) (inputs i) = Zmod.unsigned (N.v54120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54120 s i)) at 1.
  unfold R.v54120, N.v54120.
  unfold R.v6, N.v6.
  rewrite ?node_15767.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54121 (s : N.State) (i : N.Inputs) :
  R.v54121 (state s) (inputs i) = Zmod.unsigned (N.v54121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54121 s i)) at 1.
  unfold R.v54121, N.v54121.
  rewrite ?node_54119.
  rewrite ?node_54120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54122 (s : N.State) (i : N.Inputs) :
  R.v54122 (state s) (inputs i) = Zmod.unsigned (N.v54122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54122 s i)) at 1.
  unfold R.v54122, N.v54122.
  rewrite ?node_54118.
  rewrite ?node_54121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54123 (s : N.State) (i : N.Inputs) :
  R.v54123 (state s) (inputs i) = Zmod.unsigned (N.v54123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54123 s i)) at 1.
  unfold R.v54123, N.v54123.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54124 (s : N.State) (i : N.Inputs) :
  R.v54124 (state s) (inputs i) = Zmod.unsigned (N.v54124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54124 s i)) at 1.
  unfold R.v54124, N.v54124.
  rewrite ?node_15763.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54125 (s : N.State) (i : N.Inputs) :
  R.v54125 (state s) (inputs i) = Zmod.unsigned (N.v54125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54125 s i)) at 1.
  unfold R.v54125, N.v54125.
  rewrite ?node_15759.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54126 (s : N.State) (i : N.Inputs) :
  R.v54126 (state s) (inputs i) = Zmod.unsigned (N.v54126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54126 s i)) at 1.
  unfold R.v54126, N.v54126.
  rewrite ?node_15757.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54127 (s : N.State) (i : N.Inputs) :
  R.v54127 (state s) (inputs i) = Zmod.unsigned (N.v54127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54127 s i)) at 1.
  unfold R.v54127, N.v54127.
  unfold R.v6, N.v6.
  rewrite ?node_15753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54128 (s : N.State) (i : N.Inputs) :
  R.v54128 (state s) (inputs i) = Zmod.unsigned (N.v54128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54128 s i)) at 1.
  unfold R.v54128, N.v54128.
  unfold R.v6, N.v6.
  rewrite ?node_15748.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54129 (s : N.State) (i : N.Inputs) :
  R.v54129 (state s) (inputs i) = Zmod.unsigned (N.v54129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54129 s i)) at 1.
  unfold R.v54129, N.v54129.
  rewrite ?node_54127.
  rewrite ?node_54128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54130 (s : N.State) (i : N.Inputs) :
  R.v54130 (state s) (inputs i) = Zmod.unsigned (N.v54130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54130 s i)) at 1.
  unfold R.v54130, N.v54130.
  unfold R.v16484, N.v16484.
  rewrite ?node_54129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54131 (s : N.State) (i : N.Inputs) :
  R.v54131 (state s) (inputs i) = Zmod.unsigned (N.v54131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54131 s i)) at 1.
  unfold R.v54131, N.v54131.
  rewrite ?node_54124.
  rewrite ?node_54125.
  rewrite ?node_54126.
  rewrite ?node_54130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54132 (s : N.State) (i : N.Inputs) :
  R.v54132 (state s) (inputs i) = Zmod.unsigned (N.v54132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54132 s i)) at 1.
  unfold R.v54132, N.v54132.
  unfold R.v6, N.v6.
  rewrite ?node_54131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54133 (s : N.State) (i : N.Inputs) :
  R.v54133 (state s) (inputs i) = Zmod.unsigned (N.v54133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54133 s i)) at 1.
  unfold R.v54133, N.v54133.
  rewrite ?node_15764.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54134 (s : N.State) (i : N.Inputs) :
  R.v54134 (state s) (inputs i) = Zmod.unsigned (N.v54134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54134 s i)) at 1.
  unfold R.v54134, N.v54134.
  unfold R.v6, N.v6.
  rewrite ?node_15810.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54135 (s : N.State) (i : N.Inputs) :
  R.v54135 (state s) (inputs i) = Zmod.unsigned (N.v54135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54135 s i)) at 1.
  unfold R.v54135, N.v54135.
  unfold R.v6, N.v6.
  rewrite ?node_15814.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54136 (s : N.State) (i : N.Inputs) :
  R.v54136 (state s) (inputs i) = Zmod.unsigned (N.v54136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54136 s i)) at 1.
  unfold R.v54136, N.v54136.
  rewrite ?node_54133.
  rewrite ?node_54134.
  rewrite ?node_54135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54137 (s : N.State) (i : N.Inputs) :
  R.v54137 (state s) (inputs i) = Zmod.unsigned (N.v54137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54137 s i)) at 1.
  unfold R.v54137, N.v54137.
  rewrite ?node_54132.
  rewrite ?node_54136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54138 (s : N.State) (i : N.Inputs) :
  R.v54138 (state s) (inputs i) = Zmod.unsigned (N.v54138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54138 s i)) at 1.
  unfold R.v54138, N.v54138.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54139 (s : N.State) (i : N.Inputs) :
  R.v54139 (state s) (inputs i) = Zmod.unsigned (N.v54139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54139 s i)) at 1.
  unfold R.v54139, N.v54139.
  rewrite ?node_15757.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54140 (s : N.State) (i : N.Inputs) :
  R.v54140 (state s) (inputs i) = Zmod.unsigned (N.v54140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54140 s i)) at 1.
  unfold R.v54140, N.v54140.
  unfold R.v6, N.v6.
  rewrite ?node_15753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54141 (s : N.State) (i : N.Inputs) :
  R.v54141 (state s) (inputs i) = Zmod.unsigned (N.v54141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54141 s i)) at 1.
  unfold R.v54141, N.v54141.
  unfold R.v6, N.v6.
  rewrite ?node_15748.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54142 (s : N.State) (i : N.Inputs) :
  R.v54142 (state s) (inputs i) = Zmod.unsigned (N.v54142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54142 s i)) at 1.
  unfold R.v54142, N.v54142.
  rewrite ?node_54140.
  rewrite ?node_54141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54143 (s : N.State) (i : N.Inputs) :
  R.v54143 (state s) (inputs i) = Zmod.unsigned (N.v54143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54143 s i)) at 1.
  unfold R.v54143, N.v54143.
  unfold R.v16484, N.v16484.
  rewrite ?node_54142.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54144 (s : N.State) (i : N.Inputs) :
  R.v54144 (state s) (inputs i) = Zmod.unsigned (N.v54144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54144 s i)) at 1.
  unfold R.v54144, N.v54144.
  rewrite ?node_54139.
  rewrite ?node_54143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54145 (s : N.State) (i : N.Inputs) :
  R.v54145 (state s) (inputs i) = Zmod.unsigned (N.v54145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54145 s i)) at 1.
  unfold R.v54145, N.v54145.
  unfold R.v6, N.v6.
  rewrite ?node_54144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54146 (s : N.State) (i : N.Inputs) :
  R.v54146 (state s) (inputs i) = Zmod.unsigned (N.v54146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54146 s i)) at 1.
  unfold R.v54146, N.v54146.
  rewrite ?node_15758.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54147 (s : N.State) (i : N.Inputs) :
  R.v54147 (state s) (inputs i) = Zmod.unsigned (N.v54147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54147 s i)) at 1.
  unfold R.v54147, N.v54147.
  unfold R.v6, N.v6.
  rewrite ?node_15810.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54148 (s : N.State) (i : N.Inputs) :
  R.v54148 (state s) (inputs i) = Zmod.unsigned (N.v54148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54148 s i)) at 1.
  unfold R.v54148, N.v54148.
  rewrite ?node_54146.
  rewrite ?node_54147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54149 (s : N.State) (i : N.Inputs) :
  R.v54149 (state s) (inputs i) = Zmod.unsigned (N.v54149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54149 s i)) at 1.
  unfold R.v54149, N.v54149.
  rewrite ?node_54145.
  rewrite ?node_54148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54150 (s : N.State) (i : N.Inputs) :
  R.v54150 (state s) (inputs i) = Zmod.unsigned (N.v54150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54150 s i)) at 1.
  unfold R.v54150, N.v54150.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54151 (s : N.State) (i : N.Inputs) :
  R.v54151 (state s) (inputs i) = Zmod.unsigned (N.v54151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54151 s i)) at 1.
  unfold R.v54151, N.v54151.
  rewrite ?node_15763.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54152 (s : N.State) (i : N.Inputs) :
  R.v54152 (state s) (inputs i) = Zmod.unsigned (N.v54152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54152 s i)) at 1.
  unfold R.v54152, N.v54152.
  unfold R.v6, N.v6.
  rewrite ?node_15759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54153 (s : N.State) (i : N.Inputs) :
  R.v54153 (state s) (inputs i) = Zmod.unsigned (N.v54153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54153 s i)) at 1.
  unfold R.v54153, N.v54153.
  unfold R.v6, N.v6.
  rewrite ?node_15758.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54154 (s : N.State) (i : N.Inputs) :
  R.v54154 (state s) (inputs i) = Zmod.unsigned (N.v54154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54154 s i)) at 1.
  unfold R.v54154, N.v54154.
  rewrite ?node_54152.
  rewrite ?node_54153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54155 (s : N.State) (i : N.Inputs) :
  R.v54155 (state s) (inputs i) = Zmod.unsigned (N.v54155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54155 s i)) at 1.
  unfold R.v54155, N.v54155.
  unfold R.v16484, N.v16484.
  rewrite ?node_54154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54156 (s : N.State) (i : N.Inputs) :
  R.v54156 (state s) (inputs i) = Zmod.unsigned (N.v54156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54156 s i)) at 1.
  unfold R.v54156, N.v54156.
  rewrite ?node_54151.
  rewrite ?node_54155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54157 (s : N.State) (i : N.Inputs) :
  R.v54157 (state s) (inputs i) = Zmod.unsigned (N.v54157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54157 s i)) at 1.
  unfold R.v54157, N.v54157.
  unfold R.v6, N.v6.
  rewrite ?node_54156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54158 (s : N.State) (i : N.Inputs) :
  R.v54158 (state s) (inputs i) = Zmod.unsigned (N.v54158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54158 s i)) at 1.
  unfold R.v54158, N.v54158.
  rewrite ?node_15764.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54159 (s : N.State) (i : N.Inputs) :
  R.v54159 (state s) (inputs i) = Zmod.unsigned (N.v54159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54159 s i)) at 1.
  unfold R.v54159, N.v54159.
  unfold R.v6, N.v6.
  rewrite ?node_15814.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54160 (s : N.State) (i : N.Inputs) :
  R.v54160 (state s) (inputs i) = Zmod.unsigned (N.v54160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54160 s i)) at 1.
  unfold R.v54160, N.v54160.
  rewrite ?node_54158.
  rewrite ?node_54159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54161 (s : N.State) (i : N.Inputs) :
  R.v54161 (state s) (inputs i) = Zmod.unsigned (N.v54161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54161 s i)) at 1.
  unfold R.v54161, N.v54161.
  rewrite ?node_54157.
  rewrite ?node_54160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54162 (s : N.State) (i : N.Inputs) :
  R.v54162 (state s) (inputs i) = Zmod.unsigned (N.v54162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54162 s i)) at 1.
  unfold R.v54162, N.v54162.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54163 (s : N.State) (i : N.Inputs) :
  R.v54163 (state s) (inputs i) = Zmod.unsigned (N.v54163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54163 s i)) at 1.
  unfold R.v54163, N.v54163.
  rewrite ?node_15810.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54164 (s : N.State) (i : N.Inputs) :
  R.v54164 (state s) (inputs i) = Zmod.unsigned (N.v54164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54164 s i)) at 1.
  unfold R.v54164, N.v54164.
  rewrite ?node_15806.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54165 (s : N.State) (i : N.Inputs) :
  R.v54165 (state s) (inputs i) = Zmod.unsigned (N.v54165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54165 s i)) at 1.
  unfold R.v54165, N.v54165.
  rewrite ?node_15804.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54166 (s : N.State) (i : N.Inputs) :
  R.v54166 (state s) (inputs i) = Zmod.unsigned (N.v54166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54166 s i)) at 1.
  unfold R.v54166, N.v54166.
  unfold R.v6, N.v6.
  rewrite ?node_15800.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54167 (s : N.State) (i : N.Inputs) :
  R.v54167 (state s) (inputs i) = Zmod.unsigned (N.v54167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54167 s i)) at 1.
  unfold R.v54167, N.v54167.
  unfold R.v6, N.v6.
  rewrite ?node_15797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54168 (s : N.State) (i : N.Inputs) :
  R.v54168 (state s) (inputs i) = Zmod.unsigned (N.v54168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54168 s i)) at 1.
  unfold R.v54168, N.v54168.
  rewrite ?node_54166.
  rewrite ?node_54167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54169 (s : N.State) (i : N.Inputs) :
  R.v54169 (state s) (inputs i) = Zmod.unsigned (N.v54169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54169 s i)) at 1.
  unfold R.v54169, N.v54169.
  unfold R.v16484, N.v16484.
  rewrite ?node_54168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54170 (s : N.State) (i : N.Inputs) :
  R.v54170 (state s) (inputs i) = Zmod.unsigned (N.v54170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54170 s i)) at 1.
  unfold R.v54170, N.v54170.
  rewrite ?node_54163.
  rewrite ?node_54164.
  rewrite ?node_54165.
  rewrite ?node_54169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54171 (s : N.State) (i : N.Inputs) :
  R.v54171 (state s) (inputs i) = Zmod.unsigned (N.v54171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54171 s i)) at 1.
  unfold R.v54171, N.v54171.
  unfold R.v6, N.v6.
  rewrite ?node_54170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54172 (s : N.State) (i : N.Inputs) :
  R.v54172 (state s) (inputs i) = Zmod.unsigned (N.v54172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54172 s i)) at 1.
  unfold R.v54172, N.v54172.
  rewrite ?node_15811.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54173 (s : N.State) (i : N.Inputs) :
  R.v54173 (state s) (inputs i) = Zmod.unsigned (N.v54173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54173 s i)) at 1.
  unfold R.v54173, N.v54173.
  unfold R.v6, N.v6.
  rewrite ?node_15853.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54174 (s : N.State) (i : N.Inputs) :
  R.v54174 (state s) (inputs i) = Zmod.unsigned (N.v54174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54174 s i)) at 1.
  unfold R.v54174, N.v54174.
  unfold R.v6, N.v6.
  rewrite ?node_15857.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54175 (s : N.State) (i : N.Inputs) :
  R.v54175 (state s) (inputs i) = Zmod.unsigned (N.v54175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54175 s i)) at 1.
  unfold R.v54175, N.v54175.
  rewrite ?node_54172.
  rewrite ?node_54173.
  rewrite ?node_54174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54176 (s : N.State) (i : N.Inputs) :
  R.v54176 (state s) (inputs i) = Zmod.unsigned (N.v54176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54176 s i)) at 1.
  unfold R.v54176, N.v54176.
  rewrite ?node_54171.
  rewrite ?node_54175.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54177 (s : N.State) (i : N.Inputs) :
  R.v54177 (state s) (inputs i) = Zmod.unsigned (N.v54177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54177 s i)) at 1.
  unfold R.v54177, N.v54177.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54178 (s : N.State) (i : N.Inputs) :
  R.v54178 (state s) (inputs i) = Zmod.unsigned (N.v54178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54178 s i)) at 1.
  unfold R.v54178, N.v54178.
  rewrite ?node_15804.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54179 (s : N.State) (i : N.Inputs) :
  R.v54179 (state s) (inputs i) = Zmod.unsigned (N.v54179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54179 s i)) at 1.
  unfold R.v54179, N.v54179.
  unfold R.v6, N.v6.
  rewrite ?node_15800.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54180 (s : N.State) (i : N.Inputs) :
  R.v54180 (state s) (inputs i) = Zmod.unsigned (N.v54180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54180 s i)) at 1.
  unfold R.v54180, N.v54180.
  unfold R.v6, N.v6.
  rewrite ?node_15797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54181 (s : N.State) (i : N.Inputs) :
  R.v54181 (state s) (inputs i) = Zmod.unsigned (N.v54181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54181 s i)) at 1.
  unfold R.v54181, N.v54181.
  rewrite ?node_54179.
  rewrite ?node_54180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54182 (s : N.State) (i : N.Inputs) :
  R.v54182 (state s) (inputs i) = Zmod.unsigned (N.v54182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54182 s i)) at 1.
  unfold R.v54182, N.v54182.
  unfold R.v16484, N.v16484.
  rewrite ?node_54181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54183 (s : N.State) (i : N.Inputs) :
  R.v54183 (state s) (inputs i) = Zmod.unsigned (N.v54183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54183 s i)) at 1.
  unfold R.v54183, N.v54183.
  rewrite ?node_54178.
  rewrite ?node_54182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54184 (s : N.State) (i : N.Inputs) :
  R.v54184 (state s) (inputs i) = Zmod.unsigned (N.v54184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54184 s i)) at 1.
  unfold R.v54184, N.v54184.
  unfold R.v6, N.v6.
  rewrite ?node_54183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54185 (s : N.State) (i : N.Inputs) :
  R.v54185 (state s) (inputs i) = Zmod.unsigned (N.v54185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54185 s i)) at 1.
  unfold R.v54185, N.v54185.
  rewrite ?node_15805.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54186 (s : N.State) (i : N.Inputs) :
  R.v54186 (state s) (inputs i) = Zmod.unsigned (N.v54186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54186 s i)) at 1.
  unfold R.v54186, N.v54186.
  unfold R.v6, N.v6.
  rewrite ?node_15853.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54187 (s : N.State) (i : N.Inputs) :
  R.v54187 (state s) (inputs i) = Zmod.unsigned (N.v54187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54187 s i)) at 1.
  unfold R.v54187, N.v54187.
  rewrite ?node_54185.
  rewrite ?node_54186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54188 (s : N.State) (i : N.Inputs) :
  R.v54188 (state s) (inputs i) = Zmod.unsigned (N.v54188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54188 s i)) at 1.
  unfold R.v54188, N.v54188.
  rewrite ?node_54184.
  rewrite ?node_54187.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54189 (s : N.State) (i : N.Inputs) :
  R.v54189 (state s) (inputs i) = Zmod.unsigned (N.v54189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54189 s i)) at 1.
  unfold R.v54189, N.v54189.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54190 (s : N.State) (i : N.Inputs) :
  R.v54190 (state s) (inputs i) = Zmod.unsigned (N.v54190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54190 s i)) at 1.
  unfold R.v54190, N.v54190.
  rewrite ?node_15810.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54191 (s : N.State) (i : N.Inputs) :
  R.v54191 (state s) (inputs i) = Zmod.unsigned (N.v54191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54191 s i)) at 1.
  unfold R.v54191, N.v54191.
  unfold R.v6, N.v6.
  rewrite ?node_15806.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54192 (s : N.State) (i : N.Inputs) :
  R.v54192 (state s) (inputs i) = Zmod.unsigned (N.v54192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54192 s i)) at 1.
  unfold R.v54192, N.v54192.
  unfold R.v6, N.v6.
  rewrite ?node_15805.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54193 (s : N.State) (i : N.Inputs) :
  R.v54193 (state s) (inputs i) = Zmod.unsigned (N.v54193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54193 s i)) at 1.
  unfold R.v54193, N.v54193.
  rewrite ?node_54191.
  rewrite ?node_54192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54194 (s : N.State) (i : N.Inputs) :
  R.v54194 (state s) (inputs i) = Zmod.unsigned (N.v54194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54194 s i)) at 1.
  unfold R.v54194, N.v54194.
  unfold R.v16484, N.v16484.
  rewrite ?node_54193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54195 (s : N.State) (i : N.Inputs) :
  R.v54195 (state s) (inputs i) = Zmod.unsigned (N.v54195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54195 s i)) at 1.
  unfold R.v54195, N.v54195.
  rewrite ?node_54190.
  rewrite ?node_54194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54196 (s : N.State) (i : N.Inputs) :
  R.v54196 (state s) (inputs i) = Zmod.unsigned (N.v54196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54196 s i)) at 1.
  unfold R.v54196, N.v54196.
  unfold R.v6, N.v6.
  rewrite ?node_54195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54197 (s : N.State) (i : N.Inputs) :
  R.v54197 (state s) (inputs i) = Zmod.unsigned (N.v54197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54197 s i)) at 1.
  unfold R.v54197, N.v54197.
  rewrite ?node_15811.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54198 (s : N.State) (i : N.Inputs) :
  R.v54198 (state s) (inputs i) = Zmod.unsigned (N.v54198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54198 s i)) at 1.
  unfold R.v54198, N.v54198.
  unfold R.v6, N.v6.
  rewrite ?node_15857.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54199 (s : N.State) (i : N.Inputs) :
  R.v54199 (state s) (inputs i) = Zmod.unsigned (N.v54199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54199 s i)) at 1.
  unfold R.v54199, N.v54199.
  rewrite ?node_54197.
  rewrite ?node_54198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54200 (s : N.State) (i : N.Inputs) :
  R.v54200 (state s) (inputs i) = Zmod.unsigned (N.v54200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54200 s i)) at 1.
  unfold R.v54200, N.v54200.
  rewrite ?node_54196.
  rewrite ?node_54199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54201 (s : N.State) (i : N.Inputs) :
  R.v54201 (state s) (inputs i) = Zmod.unsigned (N.v54201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54201 s i)) at 1.
  unfold R.v54201, N.v54201.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54202 (s : N.State) (i : N.Inputs) :
  R.v54202 (state s) (inputs i) = Zmod.unsigned (N.v54202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54202 s i)) at 1.
  unfold R.v54202, N.v54202.
  unfold R.v6, N.v6.
  rewrite ?node_15849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54203 (s : N.State) (i : N.Inputs) :
  R.v54203 (state s) (inputs i) = Zmod.unsigned (N.v54203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54203 s i)) at 1.
  unfold R.v54203, N.v54203.
  unfold R.v6, N.v6.
  rewrite ?node_15846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54204 (s : N.State) (i : N.Inputs) :
  R.v54204 (state s) (inputs i) = Zmod.unsigned (N.v54204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54204 s i)) at 1.
  unfold R.v54204, N.v54204.
  rewrite ?node_54202.
  rewrite ?node_54203.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54205 (s : N.State) (i : N.Inputs) :
  R.v54205 (state s) (inputs i) = Zmod.unsigned (N.v54205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54205 s i)) at 1.
  unfold R.v54205, N.v54205.
  unfold R.v16463, N.v16463.
  rewrite ?node_54204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54206 (s : N.State) (i : N.Inputs) :
  R.v54206 (state s) (inputs i) = Zmod.unsigned (N.v54206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54206 s i)) at 1.
  unfold R.v54206, N.v54206.
  rewrite ?node_15850.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54207 (s : N.State) (i : N.Inputs) :
  R.v54207 (state s) (inputs i) = Zmod.unsigned (N.v54207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54207 s i)) at 1.
  unfold R.v54207, N.v54207.
  unfold R.v6, N.v6.
  rewrite ?node_15895.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54208 (s : N.State) (i : N.Inputs) :
  R.v54208 (state s) (inputs i) = Zmod.unsigned (N.v54208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54208 s i)) at 1.
  unfold R.v54208, N.v54208.
  rewrite ?node_54206.
  rewrite ?node_54207.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54209 (s : N.State) (i : N.Inputs) :
  R.v54209 (state s) (inputs i) = Zmod.unsigned (N.v54209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54209 s i)) at 1.
  unfold R.v54209, N.v54209.
  rewrite ?node_54205.
  rewrite ?node_54208.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54210 (s : N.State) (i : N.Inputs) :
  R.v54210 (state s) (inputs i) = Zmod.unsigned (N.v54210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54210 s i)) at 1.
  unfold R.v54210, N.v54210.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54211 (s : N.State) (i : N.Inputs) :
  R.v54211 (state s) (inputs i) = Zmod.unsigned (N.v54211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54211 s i)) at 1.
  unfold R.v54211, N.v54211.
  unfold R.v6, N.v6.
  rewrite ?node_15893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54212 (s : N.State) (i : N.Inputs) :
  R.v54212 (state s) (inputs i) = Zmod.unsigned (N.v54212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54212 s i)) at 1.
  unfold R.v54212, N.v54212.
  unfold R.v6, N.v6.
  rewrite ?node_15890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54213 (s : N.State) (i : N.Inputs) :
  R.v54213 (state s) (inputs i) = Zmod.unsigned (N.v54213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54213 s i)) at 1.
  unfold R.v54213, N.v54213.
  rewrite ?node_54211.
  rewrite ?node_54212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54214 (s : N.State) (i : N.Inputs) :
  R.v54214 (state s) (inputs i) = Zmod.unsigned (N.v54214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54214 s i)) at 1.
  unfold R.v54214, N.v54214.
  unfold R.v16463, N.v16463.
  rewrite ?node_54213.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54215 (s : N.State) (i : N.Inputs) :
  R.v54215 (state s) (inputs i) = Zmod.unsigned (N.v54215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54215 s i)) at 1.
  unfold R.v54215, N.v54215.
  rewrite ?node_15894.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54216 (s : N.State) (i : N.Inputs) :
  R.v54216 (state s) (inputs i) = Zmod.unsigned (N.v54216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54216 s i)) at 1.
  unfold R.v54216, N.v54216.
  unfold R.v6, N.v6.
  rewrite ?node_15933.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54217 (s : N.State) (i : N.Inputs) :
  R.v54217 (state s) (inputs i) = Zmod.unsigned (N.v54217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54217 s i)) at 1.
  unfold R.v54217, N.v54217.
  rewrite ?node_54215.
  rewrite ?node_54216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54218 (s : N.State) (i : N.Inputs) :
  R.v54218 (state s) (inputs i) = Zmod.unsigned (N.v54218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54218 s i)) at 1.
  unfold R.v54218, N.v54218.
  rewrite ?node_54214.
  rewrite ?node_54217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54219 (s : N.State) (i : N.Inputs) :
  R.v54219 (state s) (inputs i) = Zmod.unsigned (N.v54219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54219 s i)) at 1.
  unfold R.v54219, N.v54219.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54220 (s : N.State) (i : N.Inputs) :
  R.v54220 (state s) (inputs i) = Zmod.unsigned (N.v54220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54220 s i)) at 1.
  unfold R.v54220, N.v54220.
  rewrite ?node_15931.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54221 (s : N.State) (i : N.Inputs) :
  R.v54221 (state s) (inputs i) = Zmod.unsigned (N.v54221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54221 s i)) at 1.
  unfold R.v54221, N.v54221.
  unfold R.v6, N.v6.
  rewrite ?node_15927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54222 (s : N.State) (i : N.Inputs) :
  R.v54222 (state s) (inputs i) = Zmod.unsigned (N.v54222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54222 s i)) at 1.
  unfold R.v54222, N.v54222.
  unfold R.v6, N.v6.
  rewrite ?node_15924.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54223 (s : N.State) (i : N.Inputs) :
  R.v54223 (state s) (inputs i) = Zmod.unsigned (N.v54223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54223 s i)) at 1.
  unfold R.v54223, N.v54223.
  rewrite ?node_54221.
  rewrite ?node_54222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54224 (s : N.State) (i : N.Inputs) :
  R.v54224 (state s) (inputs i) = Zmod.unsigned (N.v54224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54224 s i)) at 1.
  unfold R.v54224, N.v54224.
  unfold R.v16484, N.v16484.
  rewrite ?node_54223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54225 (s : N.State) (i : N.Inputs) :
  R.v54225 (state s) (inputs i) = Zmod.unsigned (N.v54225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54225 s i)) at 1.
  unfold R.v54225, N.v54225.
  rewrite ?node_54220.
  rewrite ?node_54224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54226 (s : N.State) (i : N.Inputs) :
  R.v54226 (state s) (inputs i) = Zmod.unsigned (N.v54226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54226 s i)) at 1.
  unfold R.v54226, N.v54226.
  unfold R.v6, N.v6.
  rewrite ?node_54225.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54227 (s : N.State) (i : N.Inputs) :
  R.v54227 (state s) (inputs i) = Zmod.unsigned (N.v54227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54227 s i)) at 1.
  unfold R.v54227, N.v54227.
  rewrite ?node_15932.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54228 (s : N.State) (i : N.Inputs) :
  R.v54228 (state s) (inputs i) = Zmod.unsigned (N.v54228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54228 s i)) at 1.
  unfold R.v54228, N.v54228.
  unfold R.v6, N.v6.
  rewrite ?node_15968.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54229 (s : N.State) (i : N.Inputs) :
  R.v54229 (state s) (inputs i) = Zmod.unsigned (N.v54229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54229 s i)) at 1.
  unfold R.v54229, N.v54229.
  rewrite ?node_54227.
  rewrite ?node_54228.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54230 (s : N.State) (i : N.Inputs) :
  R.v54230 (state s) (inputs i) = Zmod.unsigned (N.v54230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54230 s i)) at 1.
  unfold R.v54230, N.v54230.
  rewrite ?node_54226.
  rewrite ?node_54229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54231 (s : N.State) (i : N.Inputs) :
  R.v54231 (state s) (inputs i) = Zmod.unsigned (N.v54231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54231 s i)) at 1.
  unfold R.v54231, N.v54231.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54232 (s : N.State) (i : N.Inputs) :
  R.v54232 (state s) (inputs i) = Zmod.unsigned (N.v54232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54232 s i)) at 1.
  unfold R.v54232, N.v54232.
  unfold R.v6, N.v6.
  rewrite ?node_15964.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54233 (s : N.State) (i : N.Inputs) :
  R.v54233 (state s) (inputs i) = Zmod.unsigned (N.v54233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54233 s i)) at 1.
  unfold R.v54233, N.v54233.
  unfold R.v6, N.v6.
  rewrite ?node_15961.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54234 (s : N.State) (i : N.Inputs) :
  R.v54234 (state s) (inputs i) = Zmod.unsigned (N.v54234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54234 s i)) at 1.
  unfold R.v54234, N.v54234.
  rewrite ?node_54232.
  rewrite ?node_54233.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54235 (s : N.State) (i : N.Inputs) :
  R.v54235 (state s) (inputs i) = Zmod.unsigned (N.v54235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54235 s i)) at 1.
  unfold R.v54235, N.v54235.
  unfold R.v16463, N.v16463.
  rewrite ?node_54234.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54236 (s : N.State) (i : N.Inputs) :
  R.v54236 (state s) (inputs i) = Zmod.unsigned (N.v54236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54236 s i)) at 1.
  unfold R.v54236, N.v54236.
  rewrite ?node_15965.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54237 (s : N.State) (i : N.Inputs) :
  R.v54237 (state s) (inputs i) = Zmod.unsigned (N.v54237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54237 s i)) at 1.
  unfold R.v54237, N.v54237.
  unfold R.v6, N.v6.
  rewrite ?node_15999.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54238 (s : N.State) (i : N.Inputs) :
  R.v54238 (state s) (inputs i) = Zmod.unsigned (N.v54238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54238 s i)) at 1.
  unfold R.v54238, N.v54238.
  rewrite ?node_54236.
  rewrite ?node_54237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54239 (s : N.State) (i : N.Inputs) :
  R.v54239 (state s) (inputs i) = Zmod.unsigned (N.v54239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54239 s i)) at 1.
  unfold R.v54239, N.v54239.
  rewrite ?node_54235.
  rewrite ?node_54238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54240 (s : N.State) (i : N.Inputs) :
  R.v54240 (state s) (inputs i) = Zmod.unsigned (N.v54240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54240 s i)) at 1.
  unfold R.v54240, N.v54240.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54241 (s : N.State) (i : N.Inputs) :
  R.v54241 (state s) (inputs i) = Zmod.unsigned (N.v54241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54241 s i)) at 1.
  unfold R.v54241, N.v54241.
  unfold R.v6, N.v6.
  rewrite ?node_15997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54242 (s : N.State) (i : N.Inputs) :
  R.v54242 (state s) (inputs i) = Zmod.unsigned (N.v54242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54242 s i)) at 1.
  unfold R.v54242, N.v54242.
  unfold R.v6, N.v6.
  rewrite ?node_15994.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54243 (s : N.State) (i : N.Inputs) :
  R.v54243 (state s) (inputs i) = Zmod.unsigned (N.v54243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54243 s i)) at 1.
  unfold R.v54243, N.v54243.
  rewrite ?node_54241.
  rewrite ?node_54242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54244 (s : N.State) (i : N.Inputs) :
  R.v54244 (state s) (inputs i) = Zmod.unsigned (N.v54244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54244 s i)) at 1.
  unfold R.v54244, N.v54244.
  unfold R.v16463, N.v16463.
  rewrite ?node_54243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54245 (s : N.State) (i : N.Inputs) :
  R.v54245 (state s) (inputs i) = Zmod.unsigned (N.v54245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54245 s i)) at 1.
  unfold R.v54245, N.v54245.
  rewrite ?node_15998.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54246 (s : N.State) (i : N.Inputs) :
  R.v54246 (state s) (inputs i) = Zmod.unsigned (N.v54246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54246 s i)) at 1.
  unfold R.v54246, N.v54246.
  unfold R.v6, N.v6.
  rewrite ?node_16029.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54247 (s : N.State) (i : N.Inputs) :
  R.v54247 (state s) (inputs i) = Zmod.unsigned (N.v54247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54247 s i)) at 1.
  unfold R.v54247, N.v54247.
  rewrite ?node_54245.
  rewrite ?node_54246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54248 (s : N.State) (i : N.Inputs) :
  R.v54248 (state s) (inputs i) = Zmod.unsigned (N.v54248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54248 s i)) at 1.
  unfold R.v54248, N.v54248.
  rewrite ?node_54244.
  rewrite ?node_54247.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54249 (s : N.State) (i : N.Inputs) :
  R.v54249 (state s) (inputs i) = Zmod.unsigned (N.v54249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54249 s i)) at 1.
  unfold R.v54249, N.v54249.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54250 (s : N.State) (i : N.Inputs) :
  R.v54250 (state s) (inputs i) = Zmod.unsigned (N.v54250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54250 s i)) at 1.
  unfold R.v54250, N.v54250.
  unfold R.v6, N.v6.
  rewrite ?node_16027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54251 (s : N.State) (i : N.Inputs) :
  R.v54251 (state s) (inputs i) = Zmod.unsigned (N.v54251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54251 s i)) at 1.
  unfold R.v54251, N.v54251.
  unfold R.v6, N.v6.
  rewrite ?node_16024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54252 (s : N.State) (i : N.Inputs) :
  R.v54252 (state s) (inputs i) = Zmod.unsigned (N.v54252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54252 s i)) at 1.
  unfold R.v54252, N.v54252.
  rewrite ?node_54250.
  rewrite ?node_54251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54253 (s : N.State) (i : N.Inputs) :
  R.v54253 (state s) (inputs i) = Zmod.unsigned (N.v54253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54253 s i)) at 1.
  unfold R.v54253, N.v54253.
  unfold R.v16463, N.v16463.
  rewrite ?node_54252.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54254 (s : N.State) (i : N.Inputs) :
  R.v54254 (state s) (inputs i) = Zmod.unsigned (N.v54254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54254 s i)) at 1.
  unfold R.v54254, N.v54254.
  rewrite ?node_16028.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54255 (s : N.State) (i : N.Inputs) :
  R.v54255 (state s) (inputs i) = Zmod.unsigned (N.v54255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54255 s i)) at 1.
  unfold R.v54255, N.v54255.
  unfold R.v6, N.v6.
  rewrite ?node_16057.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54256 (s : N.State) (i : N.Inputs) :
  R.v54256 (state s) (inputs i) = Zmod.unsigned (N.v54256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54256 s i)) at 1.
  unfold R.v54256, N.v54256.
  rewrite ?node_54254.
  rewrite ?node_54255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54257 (s : N.State) (i : N.Inputs) :
  R.v54257 (state s) (inputs i) = Zmod.unsigned (N.v54257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54257 s i)) at 1.
  unfold R.v54257, N.v54257.
  rewrite ?node_54253.
  rewrite ?node_54256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54258 (s : N.State) (i : N.Inputs) :
  R.v54258 (state s) (inputs i) = Zmod.unsigned (N.v54258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54258 s i)) at 1.
  unfold R.v54258, N.v54258.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54259 (s : N.State) (i : N.Inputs) :
  R.v54259 (state s) (inputs i) = Zmod.unsigned (N.v54259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54259 s i)) at 1.
  unfold R.v54259, N.v54259.
  unfold R.v6, N.v6.
  rewrite ?node_16055.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54260 (s : N.State) (i : N.Inputs) :
  R.v54260 (state s) (inputs i) = Zmod.unsigned (N.v54260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54260 s i)) at 1.
  unfold R.v54260, N.v54260.
  unfold R.v6, N.v6.
  rewrite ?node_16052.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54261 (s : N.State) (i : N.Inputs) :
  R.v54261 (state s) (inputs i) = Zmod.unsigned (N.v54261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54261 s i)) at 1.
  unfold R.v54261, N.v54261.
  rewrite ?node_54259.
  rewrite ?node_54260.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54262 (s : N.State) (i : N.Inputs) :
  R.v54262 (state s) (inputs i) = Zmod.unsigned (N.v54262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54262 s i)) at 1.
  unfold R.v54262, N.v54262.
  unfold R.v16463, N.v16463.
  rewrite ?node_54261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54263 (s : N.State) (i : N.Inputs) :
  R.v54263 (state s) (inputs i) = Zmod.unsigned (N.v54263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54263 s i)) at 1.
  unfold R.v54263, N.v54263.
  rewrite ?node_16056.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54264 (s : N.State) (i : N.Inputs) :
  R.v54264 (state s) (inputs i) = Zmod.unsigned (N.v54264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54264 s i)) at 1.
  unfold R.v54264, N.v54264.
  unfold R.v6, N.v6.
  rewrite ?node_16084.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54265 (s : N.State) (i : N.Inputs) :
  R.v54265 (state s) (inputs i) = Zmod.unsigned (N.v54265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54265 s i)) at 1.
  unfold R.v54265, N.v54265.
  rewrite ?node_54263.
  rewrite ?node_54264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54266 (s : N.State) (i : N.Inputs) :
  R.v54266 (state s) (inputs i) = Zmod.unsigned (N.v54266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54266 s i)) at 1.
  unfold R.v54266, N.v54266.
  rewrite ?node_54262.
  rewrite ?node_54265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54267 (s : N.State) (i : N.Inputs) :
  R.v54267 (state s) (inputs i) = Zmod.unsigned (N.v54267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54267 s i)) at 1.
  unfold R.v54267, N.v54267.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54268 (s : N.State) (i : N.Inputs) :
  R.v54268 (state s) (inputs i) = Zmod.unsigned (N.v54268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54268 s i)) at 1.
  unfold R.v54268, N.v54268.
  rewrite ?node_16082.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54269 (s : N.State) (i : N.Inputs) :
  R.v54269 (state s) (inputs i) = Zmod.unsigned (N.v54269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54269 s i)) at 1.
  unfold R.v54269, N.v54269.
  unfold R.v6, N.v6.
  rewrite ?node_16078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54270 (s : N.State) (i : N.Inputs) :
  R.v54270 (state s) (inputs i) = Zmod.unsigned (N.v54270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54270 s i)) at 1.
  unfold R.v54270, N.v54270.
  unfold R.v6, N.v6.
  rewrite ?node_16075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54271 (s : N.State) (i : N.Inputs) :
  R.v54271 (state s) (inputs i) = Zmod.unsigned (N.v54271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54271 s i)) at 1.
  unfold R.v54271, N.v54271.
  rewrite ?node_54269.
  rewrite ?node_54270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54272 (s : N.State) (i : N.Inputs) :
  R.v54272 (state s) (inputs i) = Zmod.unsigned (N.v54272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54272 s i)) at 1.
  unfold R.v54272, N.v54272.
  unfold R.v16484, N.v16484.
  rewrite ?node_54271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54273 (s : N.State) (i : N.Inputs) :
  R.v54273 (state s) (inputs i) = Zmod.unsigned (N.v54273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54273 s i)) at 1.
  unfold R.v54273, N.v54273.
  rewrite ?node_54268.
  rewrite ?node_54272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54274 (s : N.State) (i : N.Inputs) :
  R.v54274 (state s) (inputs i) = Zmod.unsigned (N.v54274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54274 s i)) at 1.
  unfold R.v54274, N.v54274.
  unfold R.v6, N.v6.
  rewrite ?node_54273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54275 (s : N.State) (i : N.Inputs) :
  R.v54275 (state s) (inputs i) = Zmod.unsigned (N.v54275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54275 s i)) at 1.
  unfold R.v54275, N.v54275.
  rewrite ?node_16083.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54276 (s : N.State) (i : N.Inputs) :
  R.v54276 (state s) (inputs i) = Zmod.unsigned (N.v54276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54276 s i)) at 1.
  unfold R.v54276, N.v54276.
  unfold R.v6, N.v6.
  rewrite ?node_16107.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54277 (s : N.State) (i : N.Inputs) :
  R.v54277 (state s) (inputs i) = Zmod.unsigned (N.v54277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54277 s i)) at 1.
  unfold R.v54277, N.v54277.
  rewrite ?node_54275.
  rewrite ?node_54276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54278 (s : N.State) (i : N.Inputs) :
  R.v54278 (state s) (inputs i) = Zmod.unsigned (N.v54278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54278 s i)) at 1.
  unfold R.v54278, N.v54278.
  rewrite ?node_54274.
  rewrite ?node_54277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54279 (s : N.State) (i : N.Inputs) :
  R.v54279 (state s) (inputs i) = Zmod.unsigned (N.v54279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54279 s i)) at 1.
  unfold R.v54279, N.v54279.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54280 (s : N.State) (i : N.Inputs) :
  R.v54280 (state s) (inputs i) = Zmod.unsigned (N.v54280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54280 s i)) at 1.
  unfold R.v54280, N.v54280.
  unfold R.v6, N.v6.
  rewrite ?node_16103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54281 (s : N.State) (i : N.Inputs) :
  R.v54281 (state s) (inputs i) = Zmod.unsigned (N.v54281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54281 s i)) at 1.
  unfold R.v54281, N.v54281.
  unfold R.v6, N.v6.
  rewrite ?node_16100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54282 (s : N.State) (i : N.Inputs) :
  R.v54282 (state s) (inputs i) = Zmod.unsigned (N.v54282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54282 s i)) at 1.
  unfold R.v54282, N.v54282.
  rewrite ?node_54280.
  rewrite ?node_54281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54283 (s : N.State) (i : N.Inputs) :
  R.v54283 (state s) (inputs i) = Zmod.unsigned (N.v54283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54283 s i)) at 1.
  unfold R.v54283, N.v54283.
  unfold R.v16463, N.v16463.
  rewrite ?node_54282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54284 (s : N.State) (i : N.Inputs) :
  R.v54284 (state s) (inputs i) = Zmod.unsigned (N.v54284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54284 s i)) at 1.
  unfold R.v54284, N.v54284.
  rewrite ?node_16104.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54285 (s : N.State) (i : N.Inputs) :
  R.v54285 (state s) (inputs i) = Zmod.unsigned (N.v54285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54285 s i)) at 1.
  unfold R.v54285, N.v54285.
  unfold R.v6, N.v6.
  rewrite ?node_16127.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54286 (s : N.State) (i : N.Inputs) :
  R.v54286 (state s) (inputs i) = Zmod.unsigned (N.v54286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54286 s i)) at 1.
  unfold R.v54286, N.v54286.
  rewrite ?node_54284.
  rewrite ?node_54285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54287 (s : N.State) (i : N.Inputs) :
  R.v54287 (state s) (inputs i) = Zmod.unsigned (N.v54287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54287 s i)) at 1.
  unfold R.v54287, N.v54287.
  rewrite ?node_54283.
  rewrite ?node_54286.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54288 (s : N.State) (i : N.Inputs) :
  R.v54288 (state s) (inputs i) = Zmod.unsigned (N.v54288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54288 s i)) at 1.
  unfold R.v54288, N.v54288.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54289 (s : N.State) (i : N.Inputs) :
  R.v54289 (state s) (inputs i) = Zmod.unsigned (N.v54289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54289 s i)) at 1.
  unfold R.v54289, N.v54289.
  unfold R.v6, N.v6.
  rewrite ?node_16125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54290 (s : N.State) (i : N.Inputs) :
  R.v54290 (state s) (inputs i) = Zmod.unsigned (N.v54290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54290 s i)) at 1.
  unfold R.v54290, N.v54290.
  unfold R.v6, N.v6.
  rewrite ?node_16124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54291 (s : N.State) (i : N.Inputs) :
  R.v54291 (state s) (inputs i) = Zmod.unsigned (N.v54291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54291 s i)) at 1.
  unfold R.v54291, N.v54291.
  rewrite ?node_54289.
  rewrite ?node_54290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54292 (s : N.State) (i : N.Inputs) :
  R.v54292 (state s) (inputs i) = Zmod.unsigned (N.v54292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54292 s i)) at 1.
  unfold R.v54292, N.v54292.
  unfold R.v16463, N.v16463.
  rewrite ?node_54291.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54293 (s : N.State) (i : N.Inputs) :
  R.v54293 (state s) (inputs i) = Zmod.unsigned (N.v54293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54293 s i)) at 1.
  unfold R.v54293, N.v54293.
  rewrite ?node_16126.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54294 (s : N.State) (i : N.Inputs) :
  R.v54294 (state s) (inputs i) = Zmod.unsigned (N.v54294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54294 s i)) at 1.
  unfold R.v54294, N.v54294.
  unfold R.v6, N.v6.
  rewrite ?node_16145.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54295 (s : N.State) (i : N.Inputs) :
  R.v54295 (state s) (inputs i) = Zmod.unsigned (N.v54295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54295 s i)) at 1.
  unfold R.v54295, N.v54295.
  rewrite ?node_54293.
  rewrite ?node_54294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54296 (s : N.State) (i : N.Inputs) :
  R.v54296 (state s) (inputs i) = Zmod.unsigned (N.v54296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54296 s i)) at 1.
  unfold R.v54296, N.v54296.
  rewrite ?node_54292.
  rewrite ?node_54295.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54297 (s : N.State) (i : N.Inputs) :
  R.v54297 (state s) (inputs i) = Zmod.unsigned (N.v54297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54297 s i)) at 1.
  unfold R.v54297, N.v54297.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54298 (s : N.State) (i : N.Inputs) :
  R.v54298 (state s) (inputs i) = Zmod.unsigned (N.v54298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54298 s i)) at 1.
  unfold R.v54298, N.v54298.
  unfold R.v6, N.v6.
  rewrite ?node_16143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54299 (s : N.State) (i : N.Inputs) :
  R.v54299 (state s) (inputs i) = Zmod.unsigned (N.v54299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54299 s i)) at 1.
  unfold R.v54299, N.v54299.
  unfold R.v6, N.v6.
  rewrite ?node_16142.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54300 (s : N.State) (i : N.Inputs) :
  R.v54300 (state s) (inputs i) = Zmod.unsigned (N.v54300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54300 s i)) at 1.
  unfold R.v54300, N.v54300.
  rewrite ?node_54298.
  rewrite ?node_54299.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54301 (s : N.State) (i : N.Inputs) :
  R.v54301 (state s) (inputs i) = Zmod.unsigned (N.v54301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54301 s i)) at 1.
  unfold R.v54301, N.v54301.
  unfold R.v16463, N.v16463.
  rewrite ?node_54300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54302 (s : N.State) (i : N.Inputs) :
  R.v54302 (state s) (inputs i) = Zmod.unsigned (N.v54302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54302 s i)) at 1.
  unfold R.v54302, N.v54302.
  rewrite ?node_16144.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54303 (s : N.State) (i : N.Inputs) :
  R.v54303 (state s) (inputs i) = Zmod.unsigned (N.v54303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54303 s i)) at 1.
  unfold R.v54303, N.v54303.
  unfold R.v6, N.v6.
  rewrite ?node_16162.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54304 (s : N.State) (i : N.Inputs) :
  R.v54304 (state s) (inputs i) = Zmod.unsigned (N.v54304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54304 s i)) at 1.
  unfold R.v54304, N.v54304.
  rewrite ?node_54302.
  rewrite ?node_54303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54305 (s : N.State) (i : N.Inputs) :
  R.v54305 (state s) (inputs i) = Zmod.unsigned (N.v54305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54305 s i)) at 1.
  unfold R.v54305, N.v54305.
  rewrite ?node_54301.
  rewrite ?node_54304.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54306 (s : N.State) (i : N.Inputs) :
  R.v54306 (state s) (inputs i) = Zmod.unsigned (N.v54306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54306 s i)) at 1.
  unfold R.v54306, N.v54306.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54307 (s : N.State) (i : N.Inputs) :
  R.v54307 (state s) (inputs i) = Zmod.unsigned (N.v54307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54307 s i)) at 1.
  unfold R.v54307, N.v54307.
  unfold R.v6, N.v6.
  rewrite ?node_16160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54308 (s : N.State) (i : N.Inputs) :
  R.v54308 (state s) (inputs i) = Zmod.unsigned (N.v54308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54308 s i)) at 1.
  unfold R.v54308, N.v54308.
  unfold R.v6, N.v6.
  rewrite ?node_16157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54309 (s : N.State) (i : N.Inputs) :
  R.v54309 (state s) (inputs i) = Zmod.unsigned (N.v54309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54309 s i)) at 1.
  unfold R.v54309, N.v54309.
  rewrite ?node_54307.
  rewrite ?node_54308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54310 (s : N.State) (i : N.Inputs) :
  R.v54310 (state s) (inputs i) = Zmod.unsigned (N.v54310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54310 s i)) at 1.
  unfold R.v54310, N.v54310.
  unfold R.v16463, N.v16463.
  rewrite ?node_54309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54311 (s : N.State) (i : N.Inputs) :
  R.v54311 (state s) (inputs i) = Zmod.unsigned (N.v54311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54311 s i)) at 1.
  unfold R.v54311, N.v54311.
  rewrite ?node_16161.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54312 (s : N.State) (i : N.Inputs) :
  R.v54312 (state s) (inputs i) = Zmod.unsigned (N.v54312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54312 s i)) at 1.
  unfold R.v54312, N.v54312.
  unfold R.v6, N.v6.
  rewrite ?node_16175.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54313 (s : N.State) (i : N.Inputs) :
  R.v54313 (state s) (inputs i) = Zmod.unsigned (N.v54313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54313 s i)) at 1.
  unfold R.v54313, N.v54313.
  rewrite ?node_54311.
  rewrite ?node_54312.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54314 (s : N.State) (i : N.Inputs) :
  R.v54314 (state s) (inputs i) = Zmod.unsigned (N.v54314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54314 s i)) at 1.
  unfold R.v54314, N.v54314.
  rewrite ?node_54310.
  rewrite ?node_54313.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54315 (s : N.State) (i : N.Inputs) :
  R.v54315 (state s) (inputs i) = Zmod.unsigned (N.v54315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54315 s i)) at 1.
  unfold R.v54315, N.v54315.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54316 (s : N.State) (i : N.Inputs) :
  R.v54316 (state s) (inputs i) = Zmod.unsigned (N.v54316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54316 s i)) at 1.
  unfold R.v54316, N.v54316.
  unfold R.v6, N.v6.
  rewrite ?node_16173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54317 (s : N.State) (i : N.Inputs) :
  R.v54317 (state s) (inputs i) = Zmod.unsigned (N.v54317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54317 s i)) at 1.
  unfold R.v54317, N.v54317.
  unfold R.v6, N.v6.
  rewrite ?node_16172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54318 (s : N.State) (i : N.Inputs) :
  R.v54318 (state s) (inputs i) = Zmod.unsigned (N.v54318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54318 s i)) at 1.
  unfold R.v54318, N.v54318.
  rewrite ?node_54316.
  rewrite ?node_54317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54319 (s : N.State) (i : N.Inputs) :
  R.v54319 (state s) (inputs i) = Zmod.unsigned (N.v54319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54319 s i)) at 1.
  unfold R.v54319, N.v54319.
  unfold R.v16463, N.v16463.
  rewrite ?node_54318.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54320 (s : N.State) (i : N.Inputs) :
  R.v54320 (state s) (inputs i) = Zmod.unsigned (N.v54320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54320 s i)) at 1.
  unfold R.v54320, N.v54320.
  rewrite ?node_16174.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54321 (s : N.State) (i : N.Inputs) :
  R.v54321 (state s) (inputs i) = Zmod.unsigned (N.v54321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54321 s i)) at 1.
  unfold R.v54321, N.v54321.
  unfold R.v6, N.v6.
  rewrite ?node_16187.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54322 (s : N.State) (i : N.Inputs) :
  R.v54322 (state s) (inputs i) = Zmod.unsigned (N.v54322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54322 s i)) at 1.
  unfold R.v54322, N.v54322.
  rewrite ?node_54320.
  rewrite ?node_54321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54323 (s : N.State) (i : N.Inputs) :
  R.v54323 (state s) (inputs i) = Zmod.unsigned (N.v54323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54323 s i)) at 1.
  unfold R.v54323, N.v54323.
  rewrite ?node_54319.
  rewrite ?node_54322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54324 (s : N.State) (i : N.Inputs) :
  R.v54324 (state s) (inputs i) = Zmod.unsigned (N.v54324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54324 s i)) at 1.
  unfold R.v54324, N.v54324.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54325 (s : N.State) (i : N.Inputs) :
  R.v54325 (state s) (inputs i) = Zmod.unsigned (N.v54325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54325 s i)) at 1.
  unfold R.v54325, N.v54325.
  unfold R.v6, N.v6.
  rewrite ?node_16185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54326 (s : N.State) (i : N.Inputs) :
  R.v54326 (state s) (inputs i) = Zmod.unsigned (N.v54326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54326 s i)) at 1.
  unfold R.v54326, N.v54326.
  unfold R.v6, N.v6.
  rewrite ?node_16184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54327 (s : N.State) (i : N.Inputs) :
  R.v54327 (state s) (inputs i) = Zmod.unsigned (N.v54327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54327 s i)) at 1.
  unfold R.v54327, N.v54327.
  rewrite ?node_54325.
  rewrite ?node_54326.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54328 (s : N.State) (i : N.Inputs) :
  R.v54328 (state s) (inputs i) = Zmod.unsigned (N.v54328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54328 s i)) at 1.
  unfold R.v54328, N.v54328.
  unfold R.v16463, N.v16463.
  rewrite ?node_54327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54329 (s : N.State) (i : N.Inputs) :
  R.v54329 (state s) (inputs i) = Zmod.unsigned (N.v54329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54329 s i)) at 1.
  unfold R.v54329, N.v54329.
  rewrite ?node_16186.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54330 (s : N.State) (i : N.Inputs) :
  R.v54330 (state s) (inputs i) = Zmod.unsigned (N.v54330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54330 s i)) at 1.
  unfold R.v54330, N.v54330.
  rewrite ?node_16184.
  rewrite ?node_16185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54331 (s : N.State) (i : N.Inputs) :
  R.v54331 (state s) (inputs i) = Zmod.unsigned (N.v54331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54331 s i)) at 1.
  unfold R.v54331, N.v54331.
  unfold R.v6, N.v6.
  unfold R.v16463, N.v16463.
  rewrite ?node_54330.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54332 (s : N.State) (i : N.Inputs) :
  R.v54332 (state s) (inputs i) = Zmod.unsigned (N.v54332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54332 s i)) at 1.
  unfold R.v54332, N.v54332.
  rewrite ?node_54329.
  rewrite ?node_54331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54333 (s : N.State) (i : N.Inputs) :
  R.v54333 (state s) (inputs i) = Zmod.unsigned (N.v54333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54333 s i)) at 1.
  unfold R.v54333, N.v54333.
  rewrite ?node_54328.
  rewrite ?node_54332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54334 (s : N.State) (i : N.Inputs) :
  R.v54334 (state s) (inputs i) = Zmod.unsigned (N.v54334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54334 s i)) at 1.
  unfold R.v54334, N.v54334.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54335 (s : N.State) (i : N.Inputs) :
  R.v54335 (state s) (inputs i) = Zmod.unsigned (N.v54335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54335 s i)) at 1.
  unfold R.v54335, N.v54335.
  unfold R.v6, N.v6.
  rewrite ?node_5122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54336 (s : N.State) (i : N.Inputs) :
  R.v54336 (state s) (inputs i) = Zmod.unsigned (N.v54336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54336 s i)) at 1.
  unfold R.v54336, N.v54336.
  unfold R.v6, N.v6.
  rewrite ?node_5121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54337 (s : N.State) (i : N.Inputs) :
  R.v54337 (state s) (inputs i) = Zmod.unsigned (N.v54337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54337 s i)) at 1.
  unfold R.v54337, N.v54337.
  rewrite ?node_54335.
  rewrite ?node_54336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54338 (s : N.State) (i : N.Inputs) :
  R.v54338 (state s) (inputs i) = Zmod.unsigned (N.v54338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54338 s i)) at 1.
  unfold R.v54338, N.v54338.
  unfold R.v16463, N.v16463.
  rewrite ?node_54337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54339 (s : N.State) (i : N.Inputs) :
  R.v54339 (state s) (inputs i) = Zmod.unsigned (N.v54339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54339 s i)) at 1.
  unfold R.v54339, N.v54339.
  rewrite ?node_5123.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54340 (s : N.State) (i : N.Inputs) :
  R.v54340 (state s) (inputs i) = Zmod.unsigned (N.v54340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54340 s i)) at 1.
  unfold R.v54340, N.v54340.
  unfold R.v6, N.v6.
  rewrite ?node_5136.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54341 (s : N.State) (i : N.Inputs) :
  R.v54341 (state s) (inputs i) = Zmod.unsigned (N.v54341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54341 s i)) at 1.
  unfold R.v54341, N.v54341.
  rewrite ?node_54339.
  rewrite ?node_54340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54342 (s : N.State) (i : N.Inputs) :
  R.v54342 (state s) (inputs i) = Zmod.unsigned (N.v54342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54342 s i)) at 1.
  unfold R.v54342, N.v54342.
  rewrite ?node_54338.
  rewrite ?node_54341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54343 (s : N.State) (i : N.Inputs) :
  R.v54343 (state s) (inputs i) = Zmod.unsigned (N.v54343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54343 s i)) at 1.
  unfold R.v54343, N.v54343.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54344 (s : N.State) (i : N.Inputs) :
  R.v54344 (state s) (inputs i) = Zmod.unsigned (N.v54344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54344 s i)) at 1.
  unfold R.v54344, N.v54344.
  unfold R.v6, N.v6.
  rewrite ?node_5134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54345 (s : N.State) (i : N.Inputs) :
  R.v54345 (state s) (inputs i) = Zmod.unsigned (N.v54345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54345 s i)) at 1.
  unfold R.v54345, N.v54345.
  unfold R.v6, N.v6.
  rewrite ?node_5133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54346 (s : N.State) (i : N.Inputs) :
  R.v54346 (state s) (inputs i) = Zmod.unsigned (N.v54346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54346 s i)) at 1.
  unfold R.v54346, N.v54346.
  rewrite ?node_54344.
  rewrite ?node_54345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54347 (s : N.State) (i : N.Inputs) :
  R.v54347 (state s) (inputs i) = Zmod.unsigned (N.v54347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54347 s i)) at 1.
  unfold R.v54347, N.v54347.
  unfold R.v16463, N.v16463.
  rewrite ?node_54346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54348 (s : N.State) (i : N.Inputs) :
  R.v54348 (state s) (inputs i) = Zmod.unsigned (N.v54348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54348 s i)) at 1.
  unfold R.v54348, N.v54348.
  rewrite ?node_5135.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54349 (s : N.State) (i : N.Inputs) :
  R.v54349 (state s) (inputs i) = Zmod.unsigned (N.v54349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54349 s i)) at 1.
  unfold R.v54349, N.v54349.
  unfold R.v6, N.v6.
  rewrite ?node_5152.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54350 (s : N.State) (i : N.Inputs) :
  R.v54350 (state s) (inputs i) = Zmod.unsigned (N.v54350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54350 s i)) at 1.
  unfold R.v54350, N.v54350.
  rewrite ?node_54348.
  rewrite ?node_54349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54351 (s : N.State) (i : N.Inputs) :
  R.v54351 (state s) (inputs i) = Zmod.unsigned (N.v54351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54351 s i)) at 1.
  unfold R.v54351, N.v54351.
  rewrite ?node_54347.
  rewrite ?node_54350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54352 (s : N.State) (i : N.Inputs) :
  R.v54352 (state s) (inputs i) = Zmod.unsigned (N.v54352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54352 s i)) at 1.
  unfold R.v54352, N.v54352.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54353 (s : N.State) (i : N.Inputs) :
  R.v54353 (state s) (inputs i) = Zmod.unsigned (N.v54353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54353 s i)) at 1.
  unfold R.v54353, N.v54353.
  unfold R.v6, N.v6.
  rewrite ?node_5150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54354 (s : N.State) (i : N.Inputs) :
  R.v54354 (state s) (inputs i) = Zmod.unsigned (N.v54354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54354 s i)) at 1.
  unfold R.v54354, N.v54354.
  unfold R.v6, N.v6.
  rewrite ?node_5149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54355 (s : N.State) (i : N.Inputs) :
  R.v54355 (state s) (inputs i) = Zmod.unsigned (N.v54355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54355 s i)) at 1.
  unfold R.v54355, N.v54355.
  rewrite ?node_54353.
  rewrite ?node_54354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54356 (s : N.State) (i : N.Inputs) :
  R.v54356 (state s) (inputs i) = Zmod.unsigned (N.v54356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54356 s i)) at 1.
  unfold R.v54356, N.v54356.
  unfold R.v16463, N.v16463.
  rewrite ?node_54355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54357 (s : N.State) (i : N.Inputs) :
  R.v54357 (state s) (inputs i) = Zmod.unsigned (N.v54357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54357 s i)) at 1.
  unfold R.v54357, N.v54357.
  rewrite ?node_5151.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54358 (s : N.State) (i : N.Inputs) :
  R.v54358 (state s) (inputs i) = Zmod.unsigned (N.v54358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54358 s i)) at 1.
  unfold R.v54358, N.v54358.
  unfold R.v6, N.v6.
  rewrite ?node_5173.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54359 (s : N.State) (i : N.Inputs) :
  R.v54359 (state s) (inputs i) = Zmod.unsigned (N.v54359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54359 s i)) at 1.
  unfold R.v54359, N.v54359.
  rewrite ?node_54357.
  rewrite ?node_54358.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54360 (s : N.State) (i : N.Inputs) :
  R.v54360 (state s) (inputs i) = Zmod.unsigned (N.v54360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54360 s i)) at 1.
  unfold R.v54360, N.v54360.
  rewrite ?node_54356.
  rewrite ?node_54359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54361 (s : N.State) (i : N.Inputs) :
  R.v54361 (state s) (inputs i) = Zmod.unsigned (N.v54361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54361 s i)) at 1.
  unfold R.v54361, N.v54361.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54362 (s : N.State) (i : N.Inputs) :
  R.v54362 (state s) (inputs i) = Zmod.unsigned (N.v54362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54362 s i)) at 1.
  unfold R.v54362, N.v54362.
  unfold R.v6, N.v6.
  rewrite ?node_5171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54363 (s : N.State) (i : N.Inputs) :
  R.v54363 (state s) (inputs i) = Zmod.unsigned (N.v54363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54363 s i)) at 1.
  unfold R.v54363, N.v54363.
  unfold R.v6, N.v6.
  rewrite ?node_5170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54364 (s : N.State) (i : N.Inputs) :
  R.v54364 (state s) (inputs i) = Zmod.unsigned (N.v54364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54364 s i)) at 1.
  unfold R.v54364, N.v54364.
  rewrite ?node_54362.
  rewrite ?node_54363.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54365 (s : N.State) (i : N.Inputs) :
  R.v54365 (state s) (inputs i) = Zmod.unsigned (N.v54365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54365 s i)) at 1.
  unfold R.v54365, N.v54365.
  unfold R.v16463, N.v16463.
  rewrite ?node_54364.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54366 (s : N.State) (i : N.Inputs) :
  R.v54366 (state s) (inputs i) = Zmod.unsigned (N.v54366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54366 s i)) at 1.
  unfold R.v54366, N.v54366.
  rewrite ?node_5172.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54367 (s : N.State) (i : N.Inputs) :
  R.v54367 (state s) (inputs i) = Zmod.unsigned (N.v54367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54367 s i)) at 1.
  unfold R.v54367, N.v54367.
  unfold R.v6, N.v6.
  rewrite ?node_5196.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54368 (s : N.State) (i : N.Inputs) :
  R.v54368 (state s) (inputs i) = Zmod.unsigned (N.v54368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54368 s i)) at 1.
  unfold R.v54368, N.v54368.
  rewrite ?node_54366.
  rewrite ?node_54367.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54369 (s : N.State) (i : N.Inputs) :
  R.v54369 (state s) (inputs i) = Zmod.unsigned (N.v54369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54369 s i)) at 1.
  unfold R.v54369, N.v54369.
  rewrite ?node_54365.
  rewrite ?node_54368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54370 (s : N.State) (i : N.Inputs) :
  R.v54370 (state s) (inputs i) = Zmod.unsigned (N.v54370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54370 s i)) at 1.
  unfold R.v54370, N.v54370.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54371 (s : N.State) (i : N.Inputs) :
  R.v54371 (state s) (inputs i) = Zmod.unsigned (N.v54371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54371 s i)) at 1.
  unfold R.v54371, N.v54371.
  unfold R.v6, N.v6.
  rewrite ?node_5194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54372 (s : N.State) (i : N.Inputs) :
  R.v54372 (state s) (inputs i) = Zmod.unsigned (N.v54372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54372 s i)) at 1.
  unfold R.v54372, N.v54372.
  unfold R.v6, N.v6.
  rewrite ?node_5193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54373 (s : N.State) (i : N.Inputs) :
  R.v54373 (state s) (inputs i) = Zmod.unsigned (N.v54373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54373 s i)) at 1.
  unfold R.v54373, N.v54373.
  rewrite ?node_54371.
  rewrite ?node_54372.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54374 (s : N.State) (i : N.Inputs) :
  R.v54374 (state s) (inputs i) = Zmod.unsigned (N.v54374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54374 s i)) at 1.
  unfold R.v54374, N.v54374.
  unfold R.v16463, N.v16463.
  rewrite ?node_54373.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54375 (s : N.State) (i : N.Inputs) :
  R.v54375 (state s) (inputs i) = Zmod.unsigned (N.v54375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54375 s i)) at 1.
  unfold R.v54375, N.v54375.
  rewrite ?node_5195.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54376 (s : N.State) (i : N.Inputs) :
  R.v54376 (state s) (inputs i) = Zmod.unsigned (N.v54376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54376 s i)) at 1.
  unfold R.v54376, N.v54376.
  unfold R.v6, N.v6.
  rewrite ?node_5220.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54377 (s : N.State) (i : N.Inputs) :
  R.v54377 (state s) (inputs i) = Zmod.unsigned (N.v54377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54377 s i)) at 1.
  unfold R.v54377, N.v54377.
  rewrite ?node_54375.
  rewrite ?node_54376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54378 (s : N.State) (i : N.Inputs) :
  R.v54378 (state s) (inputs i) = Zmod.unsigned (N.v54378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54378 s i)) at 1.
  unfold R.v54378, N.v54378.
  rewrite ?node_54374.
  rewrite ?node_54377.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54379 (s : N.State) (i : N.Inputs) :
  R.v54379 (state s) (inputs i) = Zmod.unsigned (N.v54379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54379 s i)) at 1.
  unfold R.v54379, N.v54379.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54380 (s : N.State) (i : N.Inputs) :
  R.v54380 (state s) (inputs i) = Zmod.unsigned (N.v54380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54380 s i)) at 1.
  unfold R.v54380, N.v54380.
  unfold R.v6, N.v6.
  rewrite ?node_5218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54381 (s : N.State) (i : N.Inputs) :
  R.v54381 (state s) (inputs i) = Zmod.unsigned (N.v54381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54381 s i)) at 1.
  unfold R.v54381, N.v54381.
  unfold R.v6, N.v6.
  rewrite ?node_5217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54382 (s : N.State) (i : N.Inputs) :
  R.v54382 (state s) (inputs i) = Zmod.unsigned (N.v54382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54382 s i)) at 1.
  unfold R.v54382, N.v54382.
  rewrite ?node_54380.
  rewrite ?node_54381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54383 (s : N.State) (i : N.Inputs) :
  R.v54383 (state s) (inputs i) = Zmod.unsigned (N.v54383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54383 s i)) at 1.
  unfold R.v54383, N.v54383.
  unfold R.v16463, N.v16463.
  rewrite ?node_54382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54384 (s : N.State) (i : N.Inputs) :
  R.v54384 (state s) (inputs i) = Zmod.unsigned (N.v54384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54384 s i)) at 1.
  unfold R.v54384, N.v54384.
  rewrite ?node_5219.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54385 (s : N.State) (i : N.Inputs) :
  R.v54385 (state s) (inputs i) = Zmod.unsigned (N.v54385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54385 s i)) at 1.
  unfold R.v54385, N.v54385.
  unfold R.v6, N.v6.
  rewrite ?node_5246.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54386 (s : N.State) (i : N.Inputs) :
  R.v54386 (state s) (inputs i) = Zmod.unsigned (N.v54386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54386 s i)) at 1.
  unfold R.v54386, N.v54386.
  rewrite ?node_54384.
  rewrite ?node_54385.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54387 (s : N.State) (i : N.Inputs) :
  R.v54387 (state s) (inputs i) = Zmod.unsigned (N.v54387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54387 s i)) at 1.
  unfold R.v54387, N.v54387.
  rewrite ?node_54383.
  rewrite ?node_54386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54388 (s : N.State) (i : N.Inputs) :
  R.v54388 (state s) (inputs i) = Zmod.unsigned (N.v54388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54388 s i)) at 1.
  unfold R.v54388, N.v54388.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54389 (s : N.State) (i : N.Inputs) :
  R.v54389 (state s) (inputs i) = Zmod.unsigned (N.v54389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54389 s i)) at 1.
  unfold R.v54389, N.v54389.
  unfold R.v6, N.v6.
  rewrite ?node_5244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54390 (s : N.State) (i : N.Inputs) :
  R.v54390 (state s) (inputs i) = Zmod.unsigned (N.v54390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54390 s i)) at 1.
  unfold R.v54390, N.v54390.
  unfold R.v6, N.v6.
  rewrite ?node_5243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54391 (s : N.State) (i : N.Inputs) :
  R.v54391 (state s) (inputs i) = Zmod.unsigned (N.v54391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54391 s i)) at 1.
  unfold R.v54391, N.v54391.
  rewrite ?node_54389.
  rewrite ?node_54390.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54392 (s : N.State) (i : N.Inputs) :
  R.v54392 (state s) (inputs i) = Zmod.unsigned (N.v54392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54392 s i)) at 1.
  unfold R.v54392, N.v54392.
  unfold R.v16463, N.v16463.
  rewrite ?node_54391.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54393 (s : N.State) (i : N.Inputs) :
  R.v54393 (state s) (inputs i) = Zmod.unsigned (N.v54393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54393 s i)) at 1.
  unfold R.v54393, N.v54393.
  rewrite ?node_5245.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54394 (s : N.State) (i : N.Inputs) :
  R.v54394 (state s) (inputs i) = Zmod.unsigned (N.v54394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54394 s i)) at 1.
  unfold R.v54394, N.v54394.
  unfold R.v6, N.v6.
  rewrite ?node_5275.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54395 (s : N.State) (i : N.Inputs) :
  R.v54395 (state s) (inputs i) = Zmod.unsigned (N.v54395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54395 s i)) at 1.
  unfold R.v54395, N.v54395.
  rewrite ?node_54393.
  rewrite ?node_54394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54396 (s : N.State) (i : N.Inputs) :
  R.v54396 (state s) (inputs i) = Zmod.unsigned (N.v54396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54396 s i)) at 1.
  unfold R.v54396, N.v54396.
  rewrite ?node_54392.
  rewrite ?node_54395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54397 (s : N.State) (i : N.Inputs) :
  R.v54397 (state s) (inputs i) = Zmod.unsigned (N.v54397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54397 s i)) at 1.
  unfold R.v54397, N.v54397.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54398 (s : N.State) (i : N.Inputs) :
  R.v54398 (state s) (inputs i) = Zmod.unsigned (N.v54398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54398 s i)) at 1.
  unfold R.v54398, N.v54398.
  unfold R.v6, N.v6.
  rewrite ?node_5273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54399 (s : N.State) (i : N.Inputs) :
  R.v54399 (state s) (inputs i) = Zmod.unsigned (N.v54399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54399 s i)) at 1.
  unfold R.v54399, N.v54399.
  unfold R.v6, N.v6.
  rewrite ?node_5272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54400 (s : N.State) (i : N.Inputs) :
  R.v54400 (state s) (inputs i) = Zmod.unsigned (N.v54400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54400 s i)) at 1.
  unfold R.v54400, N.v54400.
  rewrite ?node_54398.
  rewrite ?node_54399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54401 (s : N.State) (i : N.Inputs) :
  R.v54401 (state s) (inputs i) = Zmod.unsigned (N.v54401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54401 s i)) at 1.
  unfold R.v54401, N.v54401.
  unfold R.v16463, N.v16463.
  rewrite ?node_54400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54402 (s : N.State) (i : N.Inputs) :
  R.v54402 (state s) (inputs i) = Zmod.unsigned (N.v54402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54402 s i)) at 1.
  unfold R.v54402, N.v54402.
  rewrite ?node_5274.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54403 (s : N.State) (i : N.Inputs) :
  R.v54403 (state s) (inputs i) = Zmod.unsigned (N.v54403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54403 s i)) at 1.
  unfold R.v54403, N.v54403.
  unfold R.v6, N.v6.
  rewrite ?node_5308.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54404 (s : N.State) (i : N.Inputs) :
  R.v54404 (state s) (inputs i) = Zmod.unsigned (N.v54404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54404 s i)) at 1.
  unfold R.v54404, N.v54404.
  rewrite ?node_54402.
  rewrite ?node_54403.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54405 (s : N.State) (i : N.Inputs) :
  R.v54405 (state s) (inputs i) = Zmod.unsigned (N.v54405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54405 s i)) at 1.
  unfold R.v54405, N.v54405.
  rewrite ?node_54401.
  rewrite ?node_54404.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54406 (s : N.State) (i : N.Inputs) :
  R.v54406 (state s) (inputs i) = Zmod.unsigned (N.v54406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54406 s i)) at 1.
  unfold R.v54406, N.v54406.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54407 (s : N.State) (i : N.Inputs) :
  R.v54407 (state s) (inputs i) = Zmod.unsigned (N.v54407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54407 s i)) at 1.
  unfold R.v54407, N.v54407.
  unfold R.v6, N.v6.
  rewrite ?node_5306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54408 (s : N.State) (i : N.Inputs) :
  R.v54408 (state s) (inputs i) = Zmod.unsigned (N.v54408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54408 s i)) at 1.
  unfold R.v54408, N.v54408.
  unfold R.v6, N.v6.
  rewrite ?node_5305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54409 (s : N.State) (i : N.Inputs) :
  R.v54409 (state s) (inputs i) = Zmod.unsigned (N.v54409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54409 s i)) at 1.
  unfold R.v54409, N.v54409.
  rewrite ?node_54407.
  rewrite ?node_54408.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54410 (s : N.State) (i : N.Inputs) :
  R.v54410 (state s) (inputs i) = Zmod.unsigned (N.v54410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54410 s i)) at 1.
  unfold R.v54410, N.v54410.
  unfold R.v16463, N.v16463.
  rewrite ?node_54409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54411 (s : N.State) (i : N.Inputs) :
  R.v54411 (state s) (inputs i) = Zmod.unsigned (N.v54411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54411 s i)) at 1.
  unfold R.v54411, N.v54411.
  rewrite ?node_5307.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54412 (s : N.State) (i : N.Inputs) :
  R.v54412 (state s) (inputs i) = Zmod.unsigned (N.v54412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54412 s i)) at 1.
  unfold R.v54412, N.v54412.
  unfold R.v6, N.v6.
  rewrite ?node_5342.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54413 (s : N.State) (i : N.Inputs) :
  R.v54413 (state s) (inputs i) = Zmod.unsigned (N.v54413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54413 s i)) at 1.
  unfold R.v54413, N.v54413.
  rewrite ?node_54411.
  rewrite ?node_54412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54414 (s : N.State) (i : N.Inputs) :
  R.v54414 (state s) (inputs i) = Zmod.unsigned (N.v54414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54414 s i)) at 1.
  unfold R.v54414, N.v54414.
  rewrite ?node_54410.
  rewrite ?node_54413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54415 (s : N.State) (i : N.Inputs) :
  R.v54415 (state s) (inputs i) = Zmod.unsigned (N.v54415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54415 s i)) at 1.
  unfold R.v54415, N.v54415.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54416 (s : N.State) (i : N.Inputs) :
  R.v54416 (state s) (inputs i) = Zmod.unsigned (N.v54416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54416 s i)) at 1.
  unfold R.v54416, N.v54416.
  unfold R.v6, N.v6.
  rewrite ?node_5340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54417 (s : N.State) (i : N.Inputs) :
  R.v54417 (state s) (inputs i) = Zmod.unsigned (N.v54417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54417 s i)) at 1.
  unfold R.v54417, N.v54417.
  unfold R.v6, N.v6.
  rewrite ?node_5339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54418 (s : N.State) (i : N.Inputs) :
  R.v54418 (state s) (inputs i) = Zmod.unsigned (N.v54418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54418 s i)) at 1.
  unfold R.v54418, N.v54418.
  rewrite ?node_54416.
  rewrite ?node_54417.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54419 (s : N.State) (i : N.Inputs) :
  R.v54419 (state s) (inputs i) = Zmod.unsigned (N.v54419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54419 s i)) at 1.
  unfold R.v54419, N.v54419.
  unfold R.v16463, N.v16463.
  rewrite ?node_54418.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54420 (s : N.State) (i : N.Inputs) :
  R.v54420 (state s) (inputs i) = Zmod.unsigned (N.v54420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54420 s i)) at 1.
  unfold R.v54420, N.v54420.
  rewrite ?node_5341.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54421 (s : N.State) (i : N.Inputs) :
  R.v54421 (state s) (inputs i) = Zmod.unsigned (N.v54421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54421 s i)) at 1.
  unfold R.v54421, N.v54421.
  unfold R.v6, N.v6.
  rewrite ?node_5378.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54422 (s : N.State) (i : N.Inputs) :
  R.v54422 (state s) (inputs i) = Zmod.unsigned (N.v54422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54422 s i)) at 1.
  unfold R.v54422, N.v54422.
  rewrite ?node_54420.
  rewrite ?node_54421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54423 (s : N.State) (i : N.Inputs) :
  R.v54423 (state s) (inputs i) = Zmod.unsigned (N.v54423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54423 s i)) at 1.
  unfold R.v54423, N.v54423.
  rewrite ?node_54419.
  rewrite ?node_54422.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54424 (s : N.State) (i : N.Inputs) :
  R.v54424 (state s) (inputs i) = Zmod.unsigned (N.v54424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54424 s i)) at 1.
  unfold R.v54424, N.v54424.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54425 (s : N.State) (i : N.Inputs) :
  R.v54425 (state s) (inputs i) = Zmod.unsigned (N.v54425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54425 s i)) at 1.
  unfold R.v54425, N.v54425.
  unfold R.v6, N.v6.
  rewrite ?node_5376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54426 (s : N.State) (i : N.Inputs) :
  R.v54426 (state s) (inputs i) = Zmod.unsigned (N.v54426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54426 s i)) at 1.
  unfold R.v54426, N.v54426.
  unfold R.v6, N.v6.
  rewrite ?node_5375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54427 (s : N.State) (i : N.Inputs) :
  R.v54427 (state s) (inputs i) = Zmod.unsigned (N.v54427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54427 s i)) at 1.
  unfold R.v54427, N.v54427.
  rewrite ?node_54425.
  rewrite ?node_54426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54428 (s : N.State) (i : N.Inputs) :
  R.v54428 (state s) (inputs i) = Zmod.unsigned (N.v54428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54428 s i)) at 1.
  unfold R.v54428, N.v54428.
  unfold R.v16463, N.v16463.
  rewrite ?node_54427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54429 (s : N.State) (i : N.Inputs) :
  R.v54429 (state s) (inputs i) = Zmod.unsigned (N.v54429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54429 s i)) at 1.
  unfold R.v54429, N.v54429.
  rewrite ?node_5377.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54430 (s : N.State) (i : N.Inputs) :
  R.v54430 (state s) (inputs i) = Zmod.unsigned (N.v54430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54430 s i)) at 1.
  unfold R.v54430, N.v54430.
  unfold R.v6, N.v6.
  rewrite ?node_5417.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54431 (s : N.State) (i : N.Inputs) :
  R.v54431 (state s) (inputs i) = Zmod.unsigned (N.v54431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54431 s i)) at 1.
  unfold R.v54431, N.v54431.
  rewrite ?node_54429.
  rewrite ?node_54430.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54432 (s : N.State) (i : N.Inputs) :
  R.v54432 (state s) (inputs i) = Zmod.unsigned (N.v54432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54432 s i)) at 1.
  unfold R.v54432, N.v54432.
  rewrite ?node_54428.
  rewrite ?node_54431.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54433 (s : N.State) (i : N.Inputs) :
  R.v54433 (state s) (inputs i) = Zmod.unsigned (N.v54433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54433 s i)) at 1.
  unfold R.v54433, N.v54433.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54434 (s : N.State) (i : N.Inputs) :
  R.v54434 (state s) (inputs i) = Zmod.unsigned (N.v54434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54434 s i)) at 1.
  unfold R.v54434, N.v54434.
  unfold R.v6, N.v6.
  rewrite ?node_5415.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54435 (s : N.State) (i : N.Inputs) :
  R.v54435 (state s) (inputs i) = Zmod.unsigned (N.v54435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54435 s i)) at 1.
  unfold R.v54435, N.v54435.
  unfold R.v6, N.v6.
  rewrite ?node_5414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54436 (s : N.State) (i : N.Inputs) :
  R.v54436 (state s) (inputs i) = Zmod.unsigned (N.v54436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54436 s i)) at 1.
  unfold R.v54436, N.v54436.
  rewrite ?node_54434.
  rewrite ?node_54435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54437 (s : N.State) (i : N.Inputs) :
  R.v54437 (state s) (inputs i) = Zmod.unsigned (N.v54437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54437 s i)) at 1.
  unfold R.v54437, N.v54437.
  unfold R.v16463, N.v16463.
  rewrite ?node_54436.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54438 (s : N.State) (i : N.Inputs) :
  R.v54438 (state s) (inputs i) = Zmod.unsigned (N.v54438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54438 s i)) at 1.
  unfold R.v54438, N.v54438.
  rewrite ?node_5416.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54439 (s : N.State) (i : N.Inputs) :
  R.v54439 (state s) (inputs i) = Zmod.unsigned (N.v54439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54439 s i)) at 1.
  unfold R.v54439, N.v54439.
  unfold R.v6, N.v6.
  rewrite ?node_5458.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54440 (s : N.State) (i : N.Inputs) :
  R.v54440 (state s) (inputs i) = Zmod.unsigned (N.v54440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54440 s i)) at 1.
  unfold R.v54440, N.v54440.
  rewrite ?node_54438.
  rewrite ?node_54439.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54441 (s : N.State) (i : N.Inputs) :
  R.v54441 (state s) (inputs i) = Zmod.unsigned (N.v54441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54441 s i)) at 1.
  unfold R.v54441, N.v54441.
  rewrite ?node_54437.
  rewrite ?node_54440.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54442 (s : N.State) (i : N.Inputs) :
  R.v54442 (state s) (inputs i) = Zmod.unsigned (N.v54442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54442 s i)) at 1.
  unfold R.v54442, N.v54442.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54443 (s : N.State) (i : N.Inputs) :
  R.v54443 (state s) (inputs i) = Zmod.unsigned (N.v54443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54443 s i)) at 1.
  unfold R.v54443, N.v54443.
  unfold R.v6, N.v6.
  rewrite ?node_5456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54444 (s : N.State) (i : N.Inputs) :
  R.v54444 (state s) (inputs i) = Zmod.unsigned (N.v54444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54444 s i)) at 1.
  unfold R.v54444, N.v54444.
  unfold R.v6, N.v6.
  rewrite ?node_5453.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54445 (s : N.State) (i : N.Inputs) :
  R.v54445 (state s) (inputs i) = Zmod.unsigned (N.v54445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54445 s i)) at 1.
  unfold R.v54445, N.v54445.
  rewrite ?node_54443.
  rewrite ?node_54444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54446 (s : N.State) (i : N.Inputs) :
  R.v54446 (state s) (inputs i) = Zmod.unsigned (N.v54446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54446 s i)) at 1.
  unfold R.v54446, N.v54446.
  unfold R.v16463, N.v16463.
  rewrite ?node_54445.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54447 (s : N.State) (i : N.Inputs) :
  R.v54447 (state s) (inputs i) = Zmod.unsigned (N.v54447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54447 s i)) at 1.
  unfold R.v54447, N.v54447.
  rewrite ?node_5457.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54448 (s : N.State) (i : N.Inputs) :
  R.v54448 (state s) (inputs i) = Zmod.unsigned (N.v54448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54448 s i)) at 1.
  unfold R.v54448, N.v54448.
  unfold R.v6, N.v6.
  rewrite ?node_5500.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54449 (s : N.State) (i : N.Inputs) :
  R.v54449 (state s) (inputs i) = Zmod.unsigned (N.v54449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54449 s i)) at 1.
  unfold R.v54449, N.v54449.
  rewrite ?node_54447.
  rewrite ?node_54448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54450 (s : N.State) (i : N.Inputs) :
  R.v54450 (state s) (inputs i) = Zmod.unsigned (N.v54450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54450 s i)) at 1.
  unfold R.v54450, N.v54450.
  rewrite ?node_54446.
  rewrite ?node_54449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54451 (s : N.State) (i : N.Inputs) :
  R.v54451 (state s) (inputs i) = Zmod.unsigned (N.v54451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54451 s i)) at 1.
  unfold R.v54451, N.v54451.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54452 (s : N.State) (i : N.Inputs) :
  R.v54452 (state s) (inputs i) = Zmod.unsigned (N.v54452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54452 s i)) at 1.
  unfold R.v54452, N.v54452.
  unfold R.v6, N.v6.
  rewrite ?node_5498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54453 (s : N.State) (i : N.Inputs) :
  R.v54453 (state s) (inputs i) = Zmod.unsigned (N.v54453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54453 s i)) at 1.
  unfold R.v54453, N.v54453.
  unfold R.v6, N.v6.
  rewrite ?node_5495.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54454 (s : N.State) (i : N.Inputs) :
  R.v54454 (state s) (inputs i) = Zmod.unsigned (N.v54454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54454 s i)) at 1.
  unfold R.v54454, N.v54454.
  rewrite ?node_54452.
  rewrite ?node_54453.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54455 (s : N.State) (i : N.Inputs) :
  R.v54455 (state s) (inputs i) = Zmod.unsigned (N.v54455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54455 s i)) at 1.
  unfold R.v54455, N.v54455.
  unfold R.v16463, N.v16463.
  rewrite ?node_54454.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54456 (s : N.State) (i : N.Inputs) :
  R.v54456 (state s) (inputs i) = Zmod.unsigned (N.v54456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54456 s i)) at 1.
  unfold R.v54456, N.v54456.
  rewrite ?node_5499.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54457 (s : N.State) (i : N.Inputs) :
  R.v54457 (state s) (inputs i) = Zmod.unsigned (N.v54457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54457 s i)) at 1.
  unfold R.v54457, N.v54457.
  unfold R.v6, N.v6.
  rewrite ?node_5544.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54458 (s : N.State) (i : N.Inputs) :
  R.v54458 (state s) (inputs i) = Zmod.unsigned (N.v54458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54458 s i)) at 1.
  unfold R.v54458, N.v54458.
  rewrite ?node_54456.
  rewrite ?node_54457.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54459 (s : N.State) (i : N.Inputs) :
  R.v54459 (state s) (inputs i) = Zmod.unsigned (N.v54459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54459 s i)) at 1.
  unfold R.v54459, N.v54459.
  rewrite ?node_54455.
  rewrite ?node_54458.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54460 (s : N.State) (i : N.Inputs) :
  R.v54460 (state s) (inputs i) = Zmod.unsigned (N.v54460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54460 s i)) at 1.
  unfold R.v54460, N.v54460.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54461 (s : N.State) (i : N.Inputs) :
  R.v54461 (state s) (inputs i) = Zmod.unsigned (N.v54461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54461 s i)) at 1.
  unfold R.v54461, N.v54461.
  unfold R.v6, N.v6.
  rewrite ?node_5542.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54462 (s : N.State) (i : N.Inputs) :
  R.v54462 (state s) (inputs i) = Zmod.unsigned (N.v54462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54462 s i)) at 1.
  unfold R.v54462, N.v54462.
  unfold R.v6, N.v6.
  rewrite ?node_5539.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54463 (s : N.State) (i : N.Inputs) :
  R.v54463 (state s) (inputs i) = Zmod.unsigned (N.v54463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54463 s i)) at 1.
  unfold R.v54463, N.v54463.
  rewrite ?node_54461.
  rewrite ?node_54462.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54464 (s : N.State) (i : N.Inputs) :
  R.v54464 (state s) (inputs i) = Zmod.unsigned (N.v54464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54464 s i)) at 1.
  unfold R.v54464, N.v54464.
  unfold R.v16463, N.v16463.
  rewrite ?node_54463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54465 (s : N.State) (i : N.Inputs) :
  R.v54465 (state s) (inputs i) = Zmod.unsigned (N.v54465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54465 s i)) at 1.
  unfold R.v54465, N.v54465.
  rewrite ?node_5543.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54466 (s : N.State) (i : N.Inputs) :
  R.v54466 (state s) (inputs i) = Zmod.unsigned (N.v54466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54466 s i)) at 1.
  unfold R.v54466, N.v54466.
  unfold R.v6, N.v6.
  rewrite ?node_5591.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54467 (s : N.State) (i : N.Inputs) :
  R.v54467 (state s) (inputs i) = Zmod.unsigned (N.v54467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54467 s i)) at 1.
  unfold R.v54467, N.v54467.
  rewrite ?node_54465.
  rewrite ?node_54466.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54468 (s : N.State) (i : N.Inputs) :
  R.v54468 (state s) (inputs i) = Zmod.unsigned (N.v54468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54468 s i)) at 1.
  unfold R.v54468, N.v54468.
  rewrite ?node_54464.
  rewrite ?node_54467.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54469 (s : N.State) (i : N.Inputs) :
  R.v54469 (state s) (inputs i) = Zmod.unsigned (N.v54469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54469 s i)) at 1.
  unfold R.v54469, N.v54469.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54470 (s : N.State) (i : N.Inputs) :
  R.v54470 (state s) (inputs i) = Zmod.unsigned (N.v54470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54470 s i)) at 1.
  unfold R.v54470, N.v54470.
  unfold R.v6, N.v6.
  rewrite ?node_5589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54471 (s : N.State) (i : N.Inputs) :
  R.v54471 (state s) (inputs i) = Zmod.unsigned (N.v54471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54471 s i)) at 1.
  unfold R.v54471, N.v54471.
  unfold R.v6, N.v6.
  rewrite ?node_5586.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54472 (s : N.State) (i : N.Inputs) :
  R.v54472 (state s) (inputs i) = Zmod.unsigned (N.v54472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54472 s i)) at 1.
  unfold R.v54472, N.v54472.
  rewrite ?node_54470.
  rewrite ?node_54471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54473 (s : N.State) (i : N.Inputs) :
  R.v54473 (state s) (inputs i) = Zmod.unsigned (N.v54473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54473 s i)) at 1.
  unfold R.v54473, N.v54473.
  unfold R.v16463, N.v16463.
  rewrite ?node_54472.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54474 (s : N.State) (i : N.Inputs) :
  R.v54474 (state s) (inputs i) = Zmod.unsigned (N.v54474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54474 s i)) at 1.
  unfold R.v54474, N.v54474.
  rewrite ?node_5590.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54475 (s : N.State) (i : N.Inputs) :
  R.v54475 (state s) (inputs i) = Zmod.unsigned (N.v54475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54475 s i)) at 1.
  unfold R.v54475, N.v54475.
  unfold R.v6, N.v6.
  rewrite ?node_5642.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54476 (s : N.State) (i : N.Inputs) :
  R.v54476 (state s) (inputs i) = Zmod.unsigned (N.v54476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54476 s i)) at 1.
  unfold R.v54476, N.v54476.
  rewrite ?node_54474.
  rewrite ?node_54475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54477 (s : N.State) (i : N.Inputs) :
  R.v54477 (state s) (inputs i) = Zmod.unsigned (N.v54477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54477 s i)) at 1.
  unfold R.v54477, N.v54477.
  rewrite ?node_54473.
  rewrite ?node_54476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54478 (s : N.State) (i : N.Inputs) :
  R.v54478 (state s) (inputs i) = Zmod.unsigned (N.v54478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54478 s i)) at 1.
  unfold R.v54478, N.v54478.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54479 (s : N.State) (i : N.Inputs) :
  R.v54479 (state s) (inputs i) = Zmod.unsigned (N.v54479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54479 s i)) at 1.
  unfold R.v54479, N.v54479.
  unfold R.v6, N.v6.
  rewrite ?node_5640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54480 (s : N.State) (i : N.Inputs) :
  R.v54480 (state s) (inputs i) = Zmod.unsigned (N.v54480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54480 s i)) at 1.
  unfold R.v54480, N.v54480.
  unfold R.v6, N.v6.
  rewrite ?node_5639.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54481 (s : N.State) (i : N.Inputs) :
  R.v54481 (state s) (inputs i) = Zmod.unsigned (N.v54481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54481 s i)) at 1.
  unfold R.v54481, N.v54481.
  rewrite ?node_54479.
  rewrite ?node_54480.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54482 (s : N.State) (i : N.Inputs) :
  R.v54482 (state s) (inputs i) = Zmod.unsigned (N.v54482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54482 s i)) at 1.
  unfold R.v54482, N.v54482.
  unfold R.v16463, N.v16463.
  rewrite ?node_54481.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54483 (s : N.State) (i : N.Inputs) :
  R.v54483 (state s) (inputs i) = Zmod.unsigned (N.v54483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54483 s i)) at 1.
  unfold R.v54483, N.v54483.
  rewrite ?node_5641.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54484 (s : N.State) (i : N.Inputs) :
  R.v54484 (state s) (inputs i) = Zmod.unsigned (N.v54484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54484 s i)) at 1.
  unfold R.v54484, N.v54484.
  unfold R.v6, N.v6.
  rewrite ?node_5696.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54485 (s : N.State) (i : N.Inputs) :
  R.v54485 (state s) (inputs i) = Zmod.unsigned (N.v54485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54485 s i)) at 1.
  unfold R.v54485, N.v54485.
  rewrite ?node_54483.
  rewrite ?node_54484.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54486 (s : N.State) (i : N.Inputs) :
  R.v54486 (state s) (inputs i) = Zmod.unsigned (N.v54486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54486 s i)) at 1.
  unfold R.v54486, N.v54486.
  rewrite ?node_54482.
  rewrite ?node_54485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54487 (s : N.State) (i : N.Inputs) :
  R.v54487 (state s) (inputs i) = Zmod.unsigned (N.v54487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54487 s i)) at 1.
  unfold R.v54487, N.v54487.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54488 (s : N.State) (i : N.Inputs) :
  R.v54488 (state s) (inputs i) = Zmod.unsigned (N.v54488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54488 s i)) at 1.
  unfold R.v54488, N.v54488.
  unfold R.v6, N.v6.
  rewrite ?node_5694.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54489 (s : N.State) (i : N.Inputs) :
  R.v54489 (state s) (inputs i) = Zmod.unsigned (N.v54489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54489 s i)) at 1.
  unfold R.v54489, N.v54489.
  unfold R.v6, N.v6.
  rewrite ?node_5691.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54490 (s : N.State) (i : N.Inputs) :
  R.v54490 (state s) (inputs i) = Zmod.unsigned (N.v54490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54490 s i)) at 1.
  unfold R.v54490, N.v54490.
  rewrite ?node_54488.
  rewrite ?node_54489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54491 (s : N.State) (i : N.Inputs) :
  R.v54491 (state s) (inputs i) = Zmod.unsigned (N.v54491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54491 s i)) at 1.
  unfold R.v54491, N.v54491.
  unfold R.v16463, N.v16463.
  rewrite ?node_54490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54492 (s : N.State) (i : N.Inputs) :
  R.v54492 (state s) (inputs i) = Zmod.unsigned (N.v54492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54492 s i)) at 1.
  unfold R.v54492, N.v54492.
  rewrite ?node_5695.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54493 (s : N.State) (i : N.Inputs) :
  R.v54493 (state s) (inputs i) = Zmod.unsigned (N.v54493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54493 s i)) at 1.
  unfold R.v54493, N.v54493.
  unfold R.v6, N.v6.
  rewrite ?node_5752.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54494 (s : N.State) (i : N.Inputs) :
  R.v54494 (state s) (inputs i) = Zmod.unsigned (N.v54494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54494 s i)) at 1.
  unfold R.v54494, N.v54494.
  rewrite ?node_54492.
  rewrite ?node_54493.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54495 (s : N.State) (i : N.Inputs) :
  R.v54495 (state s) (inputs i) = Zmod.unsigned (N.v54495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54495 s i)) at 1.
  unfold R.v54495, N.v54495.
  rewrite ?node_54491.
  rewrite ?node_54494.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54496 (s : N.State) (i : N.Inputs) :
  R.v54496 (state s) (inputs i) = Zmod.unsigned (N.v54496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54496 s i)) at 1.
  unfold R.v54496, N.v54496.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54497 (s : N.State) (i : N.Inputs) :
  R.v54497 (state s) (inputs i) = Zmod.unsigned (N.v54497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54497 s i)) at 1.
  unfold R.v54497, N.v54497.
  unfold R.v6, N.v6.
  rewrite ?node_5750.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54498 (s : N.State) (i : N.Inputs) :
  R.v54498 (state s) (inputs i) = Zmod.unsigned (N.v54498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54498 s i)) at 1.
  unfold R.v54498, N.v54498.
  unfold R.v6, N.v6.
  rewrite ?node_5747.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54499 (s : N.State) (i : N.Inputs) :
  R.v54499 (state s) (inputs i) = Zmod.unsigned (N.v54499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54499 s i)) at 1.
  unfold R.v54499, N.v54499.
  rewrite ?node_54497.
  rewrite ?node_54498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54500 (s : N.State) (i : N.Inputs) :
  R.v54500 (state s) (inputs i) = Zmod.unsigned (N.v54500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54500 s i)) at 1.
  unfold R.v54500, N.v54500.
  unfold R.v16463, N.v16463.
  rewrite ?node_54499.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54501 (s : N.State) (i : N.Inputs) :
  R.v54501 (state s) (inputs i) = Zmod.unsigned (N.v54501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54501 s i)) at 1.
  unfold R.v54501, N.v54501.
  rewrite ?node_5751.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54502 (s : N.State) (i : N.Inputs) :
  R.v54502 (state s) (inputs i) = Zmod.unsigned (N.v54502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54502 s i)) at 1.
  unfold R.v54502, N.v54502.
  unfold R.v6, N.v6.
  rewrite ?node_5811.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54503 (s : N.State) (i : N.Inputs) :
  R.v54503 (state s) (inputs i) = Zmod.unsigned (N.v54503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54503 s i)) at 1.
  unfold R.v54503, N.v54503.
  rewrite ?node_54501.
  rewrite ?node_54502.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54504 (s : N.State) (i : N.Inputs) :
  R.v54504 (state s) (inputs i) = Zmod.unsigned (N.v54504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54504 s i)) at 1.
  unfold R.v54504, N.v54504.
  rewrite ?node_54500.
  rewrite ?node_54503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54505 (s : N.State) (i : N.Inputs) :
  R.v54505 (state s) (inputs i) = Zmod.unsigned (N.v54505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54505 s i)) at 1.
  unfold R.v54505, N.v54505.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54506 (s : N.State) (i : N.Inputs) :
  R.v54506 (state s) (inputs i) = Zmod.unsigned (N.v54506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54506 s i)) at 1.
  unfold R.v54506, N.v54506.
  unfold R.v6, N.v6.
  rewrite ?node_5809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54507 (s : N.State) (i : N.Inputs) :
  R.v54507 (state s) (inputs i) = Zmod.unsigned (N.v54507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54507 s i)) at 1.
  unfold R.v54507, N.v54507.
  unfold R.v6, N.v6.
  rewrite ?node_5806.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54508 (s : N.State) (i : N.Inputs) :
  R.v54508 (state s) (inputs i) = Zmod.unsigned (N.v54508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54508 s i)) at 1.
  unfold R.v54508, N.v54508.
  rewrite ?node_54506.
  rewrite ?node_54507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54509 (s : N.State) (i : N.Inputs) :
  R.v54509 (state s) (inputs i) = Zmod.unsigned (N.v54509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54509 s i)) at 1.
  unfold R.v54509, N.v54509.
  unfold R.v16463, N.v16463.
  rewrite ?node_54508.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54510 (s : N.State) (i : N.Inputs) :
  R.v54510 (state s) (inputs i) = Zmod.unsigned (N.v54510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54510 s i)) at 1.
  unfold R.v54510, N.v54510.
  rewrite ?node_5810.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54511 (s : N.State) (i : N.Inputs) :
  R.v54511 (state s) (inputs i) = Zmod.unsigned (N.v54511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54511 s i)) at 1.
  unfold R.v54511, N.v54511.
  unfold R.v6, N.v6.
  rewrite ?node_5872.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54512 (s : N.State) (i : N.Inputs) :
  R.v54512 (state s) (inputs i) = Zmod.unsigned (N.v54512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54512 s i)) at 1.
  unfold R.v54512, N.v54512.
  rewrite ?node_54510.
  rewrite ?node_54511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54513 (s : N.State) (i : N.Inputs) :
  R.v54513 (state s) (inputs i) = Zmod.unsigned (N.v54513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54513 s i)) at 1.
  unfold R.v54513, N.v54513.
  rewrite ?node_54509.
  rewrite ?node_54512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54514 (s : N.State) (i : N.Inputs) :
  R.v54514 (state s) (inputs i) = Zmod.unsigned (N.v54514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54514 s i)) at 1.
  unfold R.v54514, N.v54514.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54515 (s : N.State) (i : N.Inputs) :
  R.v54515 (state s) (inputs i) = Zmod.unsigned (N.v54515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54515 s i)) at 1.
  unfold R.v54515, N.v54515.
  unfold R.v6, N.v6.
  rewrite ?node_5870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54516 (s : N.State) (i : N.Inputs) :
  R.v54516 (state s) (inputs i) = Zmod.unsigned (N.v54516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54516 s i)) at 1.
  unfold R.v54516, N.v54516.
  unfold R.v6, N.v6.
  rewrite ?node_5867.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54517 (s : N.State) (i : N.Inputs) :
  R.v54517 (state s) (inputs i) = Zmod.unsigned (N.v54517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54517 s i)) at 1.
  unfold R.v54517, N.v54517.
  rewrite ?node_54515.
  rewrite ?node_54516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54518 (s : N.State) (i : N.Inputs) :
  R.v54518 (state s) (inputs i) = Zmod.unsigned (N.v54518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54518 s i)) at 1.
  unfold R.v54518, N.v54518.
  unfold R.v16463, N.v16463.
  rewrite ?node_54517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54519 (s : N.State) (i : N.Inputs) :
  R.v54519 (state s) (inputs i) = Zmod.unsigned (N.v54519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54519 s i)) at 1.
  unfold R.v54519, N.v54519.
  rewrite ?node_5871.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54520 (s : N.State) (i : N.Inputs) :
  R.v54520 (state s) (inputs i) = Zmod.unsigned (N.v54520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54520 s i)) at 1.
  unfold R.v54520, N.v54520.
  unfold R.v6, N.v6.
  rewrite ?node_5934.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54521 (s : N.State) (i : N.Inputs) :
  R.v54521 (state s) (inputs i) = Zmod.unsigned (N.v54521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54521 s i)) at 1.
  unfold R.v54521, N.v54521.
  rewrite ?node_54519.
  rewrite ?node_54520.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54522 (s : N.State) (i : N.Inputs) :
  R.v54522 (state s) (inputs i) = Zmod.unsigned (N.v54522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54522 s i)) at 1.
  unfold R.v54522, N.v54522.
  rewrite ?node_54518.
  rewrite ?node_54521.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54523 (s : N.State) (i : N.Inputs) :
  R.v54523 (state s) (inputs i) = Zmod.unsigned (N.v54523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54523 s i)) at 1.
  unfold R.v54523, N.v54523.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54524 (s : N.State) (i : N.Inputs) :
  R.v54524 (state s) (inputs i) = Zmod.unsigned (N.v54524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54524 s i)) at 1.
  unfold R.v54524, N.v54524.
  unfold R.v6, N.v6.
  rewrite ?node_5932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54525 (s : N.State) (i : N.Inputs) :
  R.v54525 (state s) (inputs i) = Zmod.unsigned (N.v54525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54525 s i)) at 1.
  unfold R.v54525, N.v54525.
  unfold R.v6, N.v6.
  rewrite ?node_5929.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54526 (s : N.State) (i : N.Inputs) :
  R.v54526 (state s) (inputs i) = Zmod.unsigned (N.v54526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54526 s i)) at 1.
  unfold R.v54526, N.v54526.
  rewrite ?node_54524.
  rewrite ?node_54525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54527 (s : N.State) (i : N.Inputs) :
  R.v54527 (state s) (inputs i) = Zmod.unsigned (N.v54527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54527 s i)) at 1.
  unfold R.v54527, N.v54527.
  unfold R.v16463, N.v16463.
  rewrite ?node_54526.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54528 (s : N.State) (i : N.Inputs) :
  R.v54528 (state s) (inputs i) = Zmod.unsigned (N.v54528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54528 s i)) at 1.
  unfold R.v54528, N.v54528.
  rewrite ?node_5933.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54529 (s : N.State) (i : N.Inputs) :
  R.v54529 (state s) (inputs i) = Zmod.unsigned (N.v54529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54529 s i)) at 1.
  unfold R.v54529, N.v54529.
  unfold R.v6, N.v6.
  rewrite ?node_5998.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54530 (s : N.State) (i : N.Inputs) :
  R.v54530 (state s) (inputs i) = Zmod.unsigned (N.v54530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54530 s i)) at 1.
  unfold R.v54530, N.v54530.
  rewrite ?node_54528.
  rewrite ?node_54529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54531 (s : N.State) (i : N.Inputs) :
  R.v54531 (state s) (inputs i) = Zmod.unsigned (N.v54531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54531 s i)) at 1.
  unfold R.v54531, N.v54531.
  rewrite ?node_54527.
  rewrite ?node_54530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54532 (s : N.State) (i : N.Inputs) :
  R.v54532 (state s) (inputs i) = Zmod.unsigned (N.v54532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54532 s i)) at 1.
  unfold R.v54532, N.v54532.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54533 (s : N.State) (i : N.Inputs) :
  R.v54533 (state s) (inputs i) = Zmod.unsigned (N.v54533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54533 s i)) at 1.
  unfold R.v54533, N.v54533.
  unfold R.v6, N.v6.
  rewrite ?node_5996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54534 (s : N.State) (i : N.Inputs) :
  R.v54534 (state s) (inputs i) = Zmod.unsigned (N.v54534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54534 s i)) at 1.
  unfold R.v54534, N.v54534.
  unfold R.v6, N.v6.
  rewrite ?node_5993.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54535 (s : N.State) (i : N.Inputs) :
  R.v54535 (state s) (inputs i) = Zmod.unsigned (N.v54535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54535 s i)) at 1.
  unfold R.v54535, N.v54535.
  rewrite ?node_54533.
  rewrite ?node_54534.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54536 (s : N.State) (i : N.Inputs) :
  R.v54536 (state s) (inputs i) = Zmod.unsigned (N.v54536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54536 s i)) at 1.
  unfold R.v54536, N.v54536.
  unfold R.v16463, N.v16463.
  rewrite ?node_54535.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54537 (s : N.State) (i : N.Inputs) :
  R.v54537 (state s) (inputs i) = Zmod.unsigned (N.v54537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54537 s i)) at 1.
  unfold R.v54537, N.v54537.
  rewrite ?node_5997.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54538 (s : N.State) (i : N.Inputs) :
  R.v54538 (state s) (inputs i) = Zmod.unsigned (N.v54538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54538 s i)) at 1.
  unfold R.v54538, N.v54538.
  unfold R.v6, N.v6.
  rewrite ?node_6065.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54539 (s : N.State) (i : N.Inputs) :
  R.v54539 (state s) (inputs i) = Zmod.unsigned (N.v54539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54539 s i)) at 1.
  unfold R.v54539, N.v54539.
  rewrite ?node_54537.
  rewrite ?node_54538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54540 (s : N.State) (i : N.Inputs) :
  R.v54540 (state s) (inputs i) = Zmod.unsigned (N.v54540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54540 s i)) at 1.
  unfold R.v54540, N.v54540.
  rewrite ?node_54536.
  rewrite ?node_54539.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54541 (s : N.State) (i : N.Inputs) :
  R.v54541 (state s) (inputs i) = Zmod.unsigned (N.v54541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54541 s i)) at 1.
  unfold R.v54541, N.v54541.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54542 (s : N.State) (i : N.Inputs) :
  R.v54542 (state s) (inputs i) = Zmod.unsigned (N.v54542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54542 s i)) at 1.
  unfold R.v54542, N.v54542.
  unfold R.v6, N.v6.
  rewrite ?node_6063.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54543 (s : N.State) (i : N.Inputs) :
  R.v54543 (state s) (inputs i) = Zmod.unsigned (N.v54543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54543 s i)) at 1.
  unfold R.v54543, N.v54543.
  unfold R.v6, N.v6.
  rewrite ?node_6060.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54544 (s : N.State) (i : N.Inputs) :
  R.v54544 (state s) (inputs i) = Zmod.unsigned (N.v54544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54544 s i)) at 1.
  unfold R.v54544, N.v54544.
  rewrite ?node_54542.
  rewrite ?node_54543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54545 (s : N.State) (i : N.Inputs) :
  R.v54545 (state s) (inputs i) = Zmod.unsigned (N.v54545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54545 s i)) at 1.
  unfold R.v54545, N.v54545.
  unfold R.v16463, N.v16463.
  rewrite ?node_54544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54546 (s : N.State) (i : N.Inputs) :
  R.v54546 (state s) (inputs i) = Zmod.unsigned (N.v54546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54546 s i)) at 1.
  unfold R.v54546, N.v54546.
  rewrite ?node_6064.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54547 (s : N.State) (i : N.Inputs) :
  R.v54547 (state s) (inputs i) = Zmod.unsigned (N.v54547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54547 s i)) at 1.
  unfold R.v54547, N.v54547.
  unfold R.v6, N.v6.
  rewrite ?node_6136.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54548 (s : N.State) (i : N.Inputs) :
  R.v54548 (state s) (inputs i) = Zmod.unsigned (N.v54548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54548 s i)) at 1.
  unfold R.v54548, N.v54548.
  rewrite ?node_54546.
  rewrite ?node_54547.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54549 (s : N.State) (i : N.Inputs) :
  R.v54549 (state s) (inputs i) = Zmod.unsigned (N.v54549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54549 s i)) at 1.
  unfold R.v54549, N.v54549.
  rewrite ?node_54545.
  rewrite ?node_54548.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54550 (s : N.State) (i : N.Inputs) :
  R.v54550 (state s) (inputs i) = Zmod.unsigned (N.v54550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54550 s i)) at 1.
  unfold R.v54550, N.v54550.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54551 (s : N.State) (i : N.Inputs) :
  R.v54551 (state s) (inputs i) = Zmod.unsigned (N.v54551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54551 s i)) at 1.
  unfold R.v54551, N.v54551.
  unfold R.v6, N.v6.
  rewrite ?node_6134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54552 (s : N.State) (i : N.Inputs) :
  R.v54552 (state s) (inputs i) = Zmod.unsigned (N.v54552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54552 s i)) at 1.
  unfold R.v54552, N.v54552.
  unfold R.v6, N.v6.
  rewrite ?node_6131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54553 (s : N.State) (i : N.Inputs) :
  R.v54553 (state s) (inputs i) = Zmod.unsigned (N.v54553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54553 s i)) at 1.
  unfold R.v54553, N.v54553.
  rewrite ?node_54551.
  rewrite ?node_54552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54554 (s : N.State) (i : N.Inputs) :
  R.v54554 (state s) (inputs i) = Zmod.unsigned (N.v54554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54554 s i)) at 1.
  unfold R.v54554, N.v54554.
  unfold R.v16463, N.v16463.
  rewrite ?node_54553.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54555 (s : N.State) (i : N.Inputs) :
  R.v54555 (state s) (inputs i) = Zmod.unsigned (N.v54555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54555 s i)) at 1.
  unfold R.v54555, N.v54555.
  rewrite ?node_6135.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54556 (s : N.State) (i : N.Inputs) :
  R.v54556 (state s) (inputs i) = Zmod.unsigned (N.v54556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54556 s i)) at 1.
  unfold R.v54556, N.v54556.
  unfold R.v6, N.v6.
  rewrite ?node_6208.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54557 (s : N.State) (i : N.Inputs) :
  R.v54557 (state s) (inputs i) = Zmod.unsigned (N.v54557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54557 s i)) at 1.
  unfold R.v54557, N.v54557.
  rewrite ?node_54555.
  rewrite ?node_54556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54558 (s : N.State) (i : N.Inputs) :
  R.v54558 (state s) (inputs i) = Zmod.unsigned (N.v54558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54558 s i)) at 1.
  unfold R.v54558, N.v54558.
  rewrite ?node_54554.
  rewrite ?node_54557.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54559 (s : N.State) (i : N.Inputs) :
  R.v54559 (state s) (inputs i) = Zmod.unsigned (N.v54559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54559 s i)) at 1.
  unfold R.v54559, N.v54559.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54560 (s : N.State) (i : N.Inputs) :
  R.v54560 (state s) (inputs i) = Zmod.unsigned (N.v54560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54560 s i)) at 1.
  unfold R.v54560, N.v54560.
  unfold R.v6, N.v6.
  rewrite ?node_6206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54561 (s : N.State) (i : N.Inputs) :
  R.v54561 (state s) (inputs i) = Zmod.unsigned (N.v54561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54561 s i)) at 1.
  unfold R.v54561, N.v54561.
  unfold R.v6, N.v6.
  rewrite ?node_6203.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54562 (s : N.State) (i : N.Inputs) :
  R.v54562 (state s) (inputs i) = Zmod.unsigned (N.v54562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54562 s i)) at 1.
  unfold R.v54562, N.v54562.
  rewrite ?node_54560.
  rewrite ?node_54561.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54563 (s : N.State) (i : N.Inputs) :
  R.v54563 (state s) (inputs i) = Zmod.unsigned (N.v54563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54563 s i)) at 1.
  unfold R.v54563, N.v54563.
  unfold R.v16463, N.v16463.
  rewrite ?node_54562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54564 (s : N.State) (i : N.Inputs) :
  R.v54564 (state s) (inputs i) = Zmod.unsigned (N.v54564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54564 s i)) at 1.
  unfold R.v54564, N.v54564.
  rewrite ?node_6207.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54565 (s : N.State) (i : N.Inputs) :
  R.v54565 (state s) (inputs i) = Zmod.unsigned (N.v54565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54565 s i)) at 1.
  unfold R.v54565, N.v54565.
  unfold R.v6, N.v6.
  rewrite ?node_6282.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54566 (s : N.State) (i : N.Inputs) :
  R.v54566 (state s) (inputs i) = Zmod.unsigned (N.v54566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54566 s i)) at 1.
  unfold R.v54566, N.v54566.
  rewrite ?node_54564.
  rewrite ?node_54565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54567 (s : N.State) (i : N.Inputs) :
  R.v54567 (state s) (inputs i) = Zmod.unsigned (N.v54567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54567 s i)) at 1.
  unfold R.v54567, N.v54567.
  rewrite ?node_54563.
  rewrite ?node_54566.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54568 (s : N.State) (i : N.Inputs) :
  R.v54568 (state s) (inputs i) = Zmod.unsigned (N.v54568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54568 s i)) at 1.
  unfold R.v54568, N.v54568.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54569 (s : N.State) (i : N.Inputs) :
  R.v54569 (state s) (inputs i) = Zmod.unsigned (N.v54569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54569 s i)) at 1.
  unfold R.v54569, N.v54569.
  unfold R.v6, N.v6.
  rewrite ?node_6280.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54570 (s : N.State) (i : N.Inputs) :
  R.v54570 (state s) (inputs i) = Zmod.unsigned (N.v54570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54570 s i)) at 1.
  unfold R.v54570, N.v54570.
  unfold R.v6, N.v6.
  rewrite ?node_6277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54571 (s : N.State) (i : N.Inputs) :
  R.v54571 (state s) (inputs i) = Zmod.unsigned (N.v54571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54571 s i)) at 1.
  unfold R.v54571, N.v54571.
  rewrite ?node_54569.
  rewrite ?node_54570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54572 (s : N.State) (i : N.Inputs) :
  R.v54572 (state s) (inputs i) = Zmod.unsigned (N.v54572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54572 s i)) at 1.
  unfold R.v54572, N.v54572.
  unfold R.v16463, N.v16463.
  rewrite ?node_54571.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54573 (s : N.State) (i : N.Inputs) :
  R.v54573 (state s) (inputs i) = Zmod.unsigned (N.v54573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54573 s i)) at 1.
  unfold R.v54573, N.v54573.
  rewrite ?node_6281.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54574 (s : N.State) (i : N.Inputs) :
  R.v54574 (state s) (inputs i) = Zmod.unsigned (N.v54574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54574 s i)) at 1.
  unfold R.v54574, N.v54574.
  unfold R.v6, N.v6.
  rewrite ?node_6359.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54575 (s : N.State) (i : N.Inputs) :
  R.v54575 (state s) (inputs i) = Zmod.unsigned (N.v54575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54575 s i)) at 1.
  unfold R.v54575, N.v54575.
  rewrite ?node_54573.
  rewrite ?node_54574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54576 (s : N.State) (i : N.Inputs) :
  R.v54576 (state s) (inputs i) = Zmod.unsigned (N.v54576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54576 s i)) at 1.
  unfold R.v54576, N.v54576.
  rewrite ?node_54572.
  rewrite ?node_54575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54577 (s : N.State) (i : N.Inputs) :
  R.v54577 (state s) (inputs i) = Zmod.unsigned (N.v54577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54577 s i)) at 1.
  unfold R.v54577, N.v54577.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54578 (s : N.State) (i : N.Inputs) :
  R.v54578 (state s) (inputs i) = Zmod.unsigned (N.v54578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54578 s i)) at 1.
  unfold R.v54578, N.v54578.
  rewrite ?node_6357.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54579 (s : N.State) (i : N.Inputs) :
  R.v54579 (state s) (inputs i) = Zmod.unsigned (N.v54579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54579 s i)) at 1.
  unfold R.v54579, N.v54579.
  unfold R.v6, N.v6.
  rewrite ?node_6353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54580 (s : N.State) (i : N.Inputs) :
  R.v54580 (state s) (inputs i) = Zmod.unsigned (N.v54580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54580 s i)) at 1.
  unfold R.v54580, N.v54580.
  unfold R.v6, N.v6.
  rewrite ?node_6350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54581 (s : N.State) (i : N.Inputs) :
  R.v54581 (state s) (inputs i) = Zmod.unsigned (N.v54581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54581 s i)) at 1.
  unfold R.v54581, N.v54581.
  rewrite ?node_54579.
  rewrite ?node_54580.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54582 (s : N.State) (i : N.Inputs) :
  R.v54582 (state s) (inputs i) = Zmod.unsigned (N.v54582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54582 s i)) at 1.
  unfold R.v54582, N.v54582.
  unfold R.v16484, N.v16484.
  rewrite ?node_54581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54583 (s : N.State) (i : N.Inputs) :
  R.v54583 (state s) (inputs i) = Zmod.unsigned (N.v54583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54583 s i)) at 1.
  unfold R.v54583, N.v54583.
  rewrite ?node_54578.
  rewrite ?node_54582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54584 (s : N.State) (i : N.Inputs) :
  R.v54584 (state s) (inputs i) = Zmod.unsigned (N.v54584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54584 s i)) at 1.
  unfold R.v54584, N.v54584.
  unfold R.v6, N.v6.
  rewrite ?node_54583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54585 (s : N.State) (i : N.Inputs) :
  R.v54585 (state s) (inputs i) = Zmod.unsigned (N.v54585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54585 s i)) at 1.
  unfold R.v54585, N.v54585.
  rewrite ?node_6358.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54586 (s : N.State) (i : N.Inputs) :
  R.v54586 (state s) (inputs i) = Zmod.unsigned (N.v54586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54586 s i)) at 1.
  unfold R.v54586, N.v54586.
  unfold R.v6, N.v6.
  rewrite ?node_6438.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54587 (s : N.State) (i : N.Inputs) :
  R.v54587 (state s) (inputs i) = Zmod.unsigned (N.v54587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54587 s i)) at 1.
  unfold R.v54587, N.v54587.
  rewrite ?node_54585.
  rewrite ?node_54586.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54588 (s : N.State) (i : N.Inputs) :
  R.v54588 (state s) (inputs i) = Zmod.unsigned (N.v54588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54588 s i)) at 1.
  unfold R.v54588, N.v54588.
  rewrite ?node_54584.
  rewrite ?node_54587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54589 (s : N.State) (i : N.Inputs) :
  R.v54589 (state s) (inputs i) = Zmod.unsigned (N.v54589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54589 s i)) at 1.
  unfold R.v54589, N.v54589.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54590 (s : N.State) (i : N.Inputs) :
  R.v54590 (state s) (inputs i) = Zmod.unsigned (N.v54590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54590 s i)) at 1.
  unfold R.v54590, N.v54590.
  rewrite ?node_6434.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54591 (s : N.State) (i : N.Inputs) :
  R.v54591 (state s) (inputs i) = Zmod.unsigned (N.v54591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54591 s i)) at 1.
  unfold R.v54591, N.v54591.
  unfold R.v6, N.v6.
  rewrite ?node_6430.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54592 (s : N.State) (i : N.Inputs) :
  R.v54592 (state s) (inputs i) = Zmod.unsigned (N.v54592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54592 s i)) at 1.
  unfold R.v54592, N.v54592.
  unfold R.v6, N.v6.
  rewrite ?node_6427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54593 (s : N.State) (i : N.Inputs) :
  R.v54593 (state s) (inputs i) = Zmod.unsigned (N.v54593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54593 s i)) at 1.
  unfold R.v54593, N.v54593.
  rewrite ?node_54591.
  rewrite ?node_54592.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54594 (s : N.State) (i : N.Inputs) :
  R.v54594 (state s) (inputs i) = Zmod.unsigned (N.v54594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54594 s i)) at 1.
  unfold R.v54594, N.v54594.
  unfold R.v16484, N.v16484.
  rewrite ?node_54593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54595 (s : N.State) (i : N.Inputs) :
  R.v54595 (state s) (inputs i) = Zmod.unsigned (N.v54595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54595 s i)) at 1.
  unfold R.v54595, N.v54595.
  rewrite ?node_54590.
  rewrite ?node_54594.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54596 (s : N.State) (i : N.Inputs) :
  R.v54596 (state s) (inputs i) = Zmod.unsigned (N.v54596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54596 s i)) at 1.
  unfold R.v54596, N.v54596.
  unfold R.v6, N.v6.
  rewrite ?node_54595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54597 (s : N.State) (i : N.Inputs) :
  R.v54597 (state s) (inputs i) = Zmod.unsigned (N.v54597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54597 s i)) at 1.
  unfold R.v54597, N.v54597.
  rewrite ?node_6435.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54598 (s : N.State) (i : N.Inputs) :
  R.v54598 (state s) (inputs i) = Zmod.unsigned (N.v54598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54598 s i)) at 1.
  unfold R.v54598, N.v54598.
  unfold R.v6, N.v6.
  rewrite ?node_6518.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54599 (s : N.State) (i : N.Inputs) :
  R.v54599 (state s) (inputs i) = Zmod.unsigned (N.v54599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54599 s i)) at 1.
  unfold R.v54599, N.v54599.
  rewrite ?node_54597.
  rewrite ?node_54598.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54600 (s : N.State) (i : N.Inputs) :
  R.v54600 (state s) (inputs i) = Zmod.unsigned (N.v54600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54600 s i)) at 1.
  unfold R.v54600, N.v54600.
  rewrite ?node_54596.
  rewrite ?node_54599.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54601 (s : N.State) (i : N.Inputs) :
  R.v54601 (state s) (inputs i) = Zmod.unsigned (N.v54601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54601 s i)) at 1.
  unfold R.v54601, N.v54601.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54602 (s : N.State) (i : N.Inputs) :
  R.v54602 (state s) (inputs i) = Zmod.unsigned (N.v54602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54602 s i)) at 1.
  unfold R.v54602, N.v54602.
  rewrite ?node_6514.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54603 (s : N.State) (i : N.Inputs) :
  R.v54603 (state s) (inputs i) = Zmod.unsigned (N.v54603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54603 s i)) at 1.
  unfold R.v54603, N.v54603.
  unfold R.v6, N.v6.
  rewrite ?node_6510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54604 (s : N.State) (i : N.Inputs) :
  R.v54604 (state s) (inputs i) = Zmod.unsigned (N.v54604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54604 s i)) at 1.
  unfold R.v54604, N.v54604.
  unfold R.v6, N.v6.
  rewrite ?node_6507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54605 (s : N.State) (i : N.Inputs) :
  R.v54605 (state s) (inputs i) = Zmod.unsigned (N.v54605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54605 s i)) at 1.
  unfold R.v54605, N.v54605.
  rewrite ?node_54603.
  rewrite ?node_54604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54606 (s : N.State) (i : N.Inputs) :
  R.v54606 (state s) (inputs i) = Zmod.unsigned (N.v54606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54606 s i)) at 1.
  unfold R.v54606, N.v54606.
  unfold R.v16484, N.v16484.
  rewrite ?node_54605.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54607 (s : N.State) (i : N.Inputs) :
  R.v54607 (state s) (inputs i) = Zmod.unsigned (N.v54607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54607 s i)) at 1.
  unfold R.v54607, N.v54607.
  rewrite ?node_54602.
  rewrite ?node_54606.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54608 (s : N.State) (i : N.Inputs) :
  R.v54608 (state s) (inputs i) = Zmod.unsigned (N.v54608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54608 s i)) at 1.
  unfold R.v54608, N.v54608.
  unfold R.v6, N.v6.
  rewrite ?node_54607.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54609 (s : N.State) (i : N.Inputs) :
  R.v54609 (state s) (inputs i) = Zmod.unsigned (N.v54609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54609 s i)) at 1.
  unfold R.v54609, N.v54609.
  rewrite ?node_6515.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54610 (s : N.State) (i : N.Inputs) :
  R.v54610 (state s) (inputs i) = Zmod.unsigned (N.v54610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54610 s i)) at 1.
  unfold R.v54610, N.v54610.
  unfold R.v6, N.v6.
  rewrite ?node_6600.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54611 (s : N.State) (i : N.Inputs) :
  R.v54611 (state s) (inputs i) = Zmod.unsigned (N.v54611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54611 s i)) at 1.
  unfold R.v54611, N.v54611.
  rewrite ?node_54609.
  rewrite ?node_54610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54612 (s : N.State) (i : N.Inputs) :
  R.v54612 (state s) (inputs i) = Zmod.unsigned (N.v54612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54612 s i)) at 1.
  unfold R.v54612, N.v54612.
  rewrite ?node_54608.
  rewrite ?node_54611.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54613 (s : N.State) (i : N.Inputs) :
  R.v54613 (state s) (inputs i) = Zmod.unsigned (N.v54613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54613 s i)) at 1.
  unfold R.v54613, N.v54613.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54614 (s : N.State) (i : N.Inputs) :
  R.v54614 (state s) (inputs i) = Zmod.unsigned (N.v54614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54614 s i)) at 1.
  unfold R.v54614, N.v54614.
  rewrite ?node_6596.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54615 (s : N.State) (i : N.Inputs) :
  R.v54615 (state s) (inputs i) = Zmod.unsigned (N.v54615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54615 s i)) at 1.
  unfold R.v54615, N.v54615.
  unfold R.v6, N.v6.
  rewrite ?node_6592.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54616 (s : N.State) (i : N.Inputs) :
  R.v54616 (state s) (inputs i) = Zmod.unsigned (N.v54616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54616 s i)) at 1.
  unfold R.v54616, N.v54616.
  unfold R.v6, N.v6.
  rewrite ?node_6589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54617 (s : N.State) (i : N.Inputs) :
  R.v54617 (state s) (inputs i) = Zmod.unsigned (N.v54617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54617 s i)) at 1.
  unfold R.v54617, N.v54617.
  rewrite ?node_54615.
  rewrite ?node_54616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54618 (s : N.State) (i : N.Inputs) :
  R.v54618 (state s) (inputs i) = Zmod.unsigned (N.v54618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54618 s i)) at 1.
  unfold R.v54618, N.v54618.
  unfold R.v16484, N.v16484.
  rewrite ?node_54617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54619 (s : N.State) (i : N.Inputs) :
  R.v54619 (state s) (inputs i) = Zmod.unsigned (N.v54619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54619 s i)) at 1.
  unfold R.v54619, N.v54619.
  rewrite ?node_54614.
  rewrite ?node_54618.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54620 (s : N.State) (i : N.Inputs) :
  R.v54620 (state s) (inputs i) = Zmod.unsigned (N.v54620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54620 s i)) at 1.
  unfold R.v54620, N.v54620.
  unfold R.v6, N.v6.
  rewrite ?node_54619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54621 (s : N.State) (i : N.Inputs) :
  R.v54621 (state s) (inputs i) = Zmod.unsigned (N.v54621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54621 s i)) at 1.
  unfold R.v54621, N.v54621.
  rewrite ?node_6597.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54622 (s : N.State) (i : N.Inputs) :
  R.v54622 (state s) (inputs i) = Zmod.unsigned (N.v54622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54622 s i)) at 1.
  unfold R.v54622, N.v54622.
  unfold R.v6, N.v6.
  rewrite ?node_6685.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54623 (s : N.State) (i : N.Inputs) :
  R.v54623 (state s) (inputs i) = Zmod.unsigned (N.v54623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54623 s i)) at 1.
  unfold R.v54623, N.v54623.
  rewrite ?node_54621.
  rewrite ?node_54622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54624 (s : N.State) (i : N.Inputs) :
  R.v54624 (state s) (inputs i) = Zmod.unsigned (N.v54624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54624 s i)) at 1.
  unfold R.v54624, N.v54624.
  rewrite ?node_54620.
  rewrite ?node_54623.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54625 (s : N.State) (i : N.Inputs) :
  R.v54625 (state s) (inputs i) = Zmod.unsigned (N.v54625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54625 s i)) at 1.
  unfold R.v54625, N.v54625.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54626 (s : N.State) (i : N.Inputs) :
  R.v54626 (state s) (inputs i) = Zmod.unsigned (N.v54626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54626 s i)) at 1.
  unfold R.v54626, N.v54626.
  rewrite ?node_6681.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54627 (s : N.State) (i : N.Inputs) :
  R.v54627 (state s) (inputs i) = Zmod.unsigned (N.v54627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54627 s i)) at 1.
  unfold R.v54627, N.v54627.
  unfold R.v6, N.v6.
  rewrite ?node_6677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54628 (s : N.State) (i : N.Inputs) :
  R.v54628 (state s) (inputs i) = Zmod.unsigned (N.v54628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54628 s i)) at 1.
  unfold R.v54628, N.v54628.
  unfold R.v6, N.v6.
  rewrite ?node_6672.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54629 (s : N.State) (i : N.Inputs) :
  R.v54629 (state s) (inputs i) = Zmod.unsigned (N.v54629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54629 s i)) at 1.
  unfold R.v54629, N.v54629.
  rewrite ?node_54627.
  rewrite ?node_54628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54630 (s : N.State) (i : N.Inputs) :
  R.v54630 (state s) (inputs i) = Zmod.unsigned (N.v54630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54630 s i)) at 1.
  unfold R.v54630, N.v54630.
  unfold R.v16484, N.v16484.
  rewrite ?node_54629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54631 (s : N.State) (i : N.Inputs) :
  R.v54631 (state s) (inputs i) = Zmod.unsigned (N.v54631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54631 s i)) at 1.
  unfold R.v54631, N.v54631.
  rewrite ?node_54626.
  rewrite ?node_54630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54632 (s : N.State) (i : N.Inputs) :
  R.v54632 (state s) (inputs i) = Zmod.unsigned (N.v54632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54632 s i)) at 1.
  unfold R.v54632, N.v54632.
  unfold R.v6, N.v6.
  rewrite ?node_54631.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54633 (s : N.State) (i : N.Inputs) :
  R.v54633 (state s) (inputs i) = Zmod.unsigned (N.v54633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54633 s i)) at 1.
  unfold R.v54633, N.v54633.
  rewrite ?node_6682.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54634 (s : N.State) (i : N.Inputs) :
  R.v54634 (state s) (inputs i) = Zmod.unsigned (N.v54634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54634 s i)) at 1.
  unfold R.v54634, N.v54634.
  unfold R.v6, N.v6.
  rewrite ?node_6774.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54635 (s : N.State) (i : N.Inputs) :
  R.v54635 (state s) (inputs i) = Zmod.unsigned (N.v54635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54635 s i)) at 1.
  unfold R.v54635, N.v54635.
  rewrite ?node_54633.
  rewrite ?node_54634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54636 (s : N.State) (i : N.Inputs) :
  R.v54636 (state s) (inputs i) = Zmod.unsigned (N.v54636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54636 s i)) at 1.
  unfold R.v54636, N.v54636.
  rewrite ?node_54632.
  rewrite ?node_54635.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54637 (s : N.State) (i : N.Inputs) :
  R.v54637 (state s) (inputs i) = Zmod.unsigned (N.v54637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54637 s i)) at 1.
  unfold R.v54637, N.v54637.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54638 (s : N.State) (i : N.Inputs) :
  R.v54638 (state s) (inputs i) = Zmod.unsigned (N.v54638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54638 s i)) at 1.
  unfold R.v54638, N.v54638.
  rewrite ?node_6770.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54639 (s : N.State) (i : N.Inputs) :
  R.v54639 (state s) (inputs i) = Zmod.unsigned (N.v54639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54639 s i)) at 1.
  unfold R.v54639, N.v54639.
  rewrite ?node_6768.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54640 (s : N.State) (i : N.Inputs) :
  R.v54640 (state s) (inputs i) = Zmod.unsigned (N.v54640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54640 s i)) at 1.
  unfold R.v54640, N.v54640.
  unfold R.v6, N.v6.
  rewrite ?node_6764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54641 (s : N.State) (i : N.Inputs) :
  R.v54641 (state s) (inputs i) = Zmod.unsigned (N.v54641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54641 s i)) at 1.
  unfold R.v54641, N.v54641.
  unfold R.v6, N.v6.
  rewrite ?node_6759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54642 (s : N.State) (i : N.Inputs) :
  R.v54642 (state s) (inputs i) = Zmod.unsigned (N.v54642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54642 s i)) at 1.
  unfold R.v54642, N.v54642.
  rewrite ?node_54640.
  rewrite ?node_54641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54643 (s : N.State) (i : N.Inputs) :
  R.v54643 (state s) (inputs i) = Zmod.unsigned (N.v54643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54643 s i)) at 1.
  unfold R.v54643, N.v54643.
  unfold R.v16484, N.v16484.
  rewrite ?node_54642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54644 (s : N.State) (i : N.Inputs) :
  R.v54644 (state s) (inputs i) = Zmod.unsigned (N.v54644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54644 s i)) at 1.
  unfold R.v54644, N.v54644.
  rewrite ?node_54638.
  rewrite ?node_54639.
  rewrite ?node_54643.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54645 (s : N.State) (i : N.Inputs) :
  R.v54645 (state s) (inputs i) = Zmod.unsigned (N.v54645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54645 s i)) at 1.
  unfold R.v54645, N.v54645.
  unfold R.v6, N.v6.
  rewrite ?node_54644.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54646 (s : N.State) (i : N.Inputs) :
  R.v54646 (state s) (inputs i) = Zmod.unsigned (N.v54646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54646 s i)) at 1.
  unfold R.v54646, N.v54646.
  rewrite ?node_6771.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54647 (s : N.State) (i : N.Inputs) :
  R.v54647 (state s) (inputs i) = Zmod.unsigned (N.v54647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54647 s i)) at 1.
  unfold R.v54647, N.v54647.
  unfold R.v6, N.v6.
  rewrite ?node_6864.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54648 (s : N.State) (i : N.Inputs) :
  R.v54648 (state s) (inputs i) = Zmod.unsigned (N.v54648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54648 s i)) at 1.
  unfold R.v54648, N.v54648.
  unfold R.v6, N.v6.
  rewrite ?node_6866.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54649 (s : N.State) (i : N.Inputs) :
  R.v54649 (state s) (inputs i) = Zmod.unsigned (N.v54649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54649 s i)) at 1.
  unfold R.v54649, N.v54649.
  rewrite ?node_54646.
  rewrite ?node_54647.
  rewrite ?node_54648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54650 (s : N.State) (i : N.Inputs) :
  R.v54650 (state s) (inputs i) = Zmod.unsigned (N.v54650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54650 s i)) at 1.
  unfold R.v54650, N.v54650.
  rewrite ?node_54645.
  rewrite ?node_54649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54651 (s : N.State) (i : N.Inputs) :
  R.v54651 (state s) (inputs i) = Zmod.unsigned (N.v54651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54651 s i)) at 1.
  unfold R.v54651, N.v54651.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54652 (s : N.State) (i : N.Inputs) :
  R.v54652 (state s) (inputs i) = Zmod.unsigned (N.v54652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54652 s i)) at 1.
  unfold R.v54652, N.v54652.
  rewrite ?node_6768.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54653 (s : N.State) (i : N.Inputs) :
  R.v54653 (state s) (inputs i) = Zmod.unsigned (N.v54653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54653 s i)) at 1.
  unfold R.v54653, N.v54653.
  unfold R.v6, N.v6.
  rewrite ?node_6764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54654 (s : N.State) (i : N.Inputs) :
  R.v54654 (state s) (inputs i) = Zmod.unsigned (N.v54654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54654 s i)) at 1.
  unfold R.v54654, N.v54654.
  unfold R.v6, N.v6.
  rewrite ?node_6759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54655 (s : N.State) (i : N.Inputs) :
  R.v54655 (state s) (inputs i) = Zmod.unsigned (N.v54655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54655 s i)) at 1.
  unfold R.v54655, N.v54655.
  rewrite ?node_54653.
  rewrite ?node_54654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54656 (s : N.State) (i : N.Inputs) :
  R.v54656 (state s) (inputs i) = Zmod.unsigned (N.v54656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54656 s i)) at 1.
  unfold R.v54656, N.v54656.
  unfold R.v16484, N.v16484.
  rewrite ?node_54655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54657 (s : N.State) (i : N.Inputs) :
  R.v54657 (state s) (inputs i) = Zmod.unsigned (N.v54657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54657 s i)) at 1.
  unfold R.v54657, N.v54657.
  rewrite ?node_54652.
  rewrite ?node_54656.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54658 (s : N.State) (i : N.Inputs) :
  R.v54658 (state s) (inputs i) = Zmod.unsigned (N.v54658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54658 s i)) at 1.
  unfold R.v54658, N.v54658.
  unfold R.v6, N.v6.
  rewrite ?node_54657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54659 (s : N.State) (i : N.Inputs) :
  R.v54659 (state s) (inputs i) = Zmod.unsigned (N.v54659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54659 s i)) at 1.
  unfold R.v54659, N.v54659.
  rewrite ?node_6769.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54660 (s : N.State) (i : N.Inputs) :
  R.v54660 (state s) (inputs i) = Zmod.unsigned (N.v54660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54660 s i)) at 1.
  unfold R.v54660, N.v54660.
  unfold R.v6, N.v6.
  rewrite ?node_6864.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54661 (s : N.State) (i : N.Inputs) :
  R.v54661 (state s) (inputs i) = Zmod.unsigned (N.v54661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54661 s i)) at 1.
  unfold R.v54661, N.v54661.
  rewrite ?node_54659.
  rewrite ?node_54660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54662 (s : N.State) (i : N.Inputs) :
  R.v54662 (state s) (inputs i) = Zmod.unsigned (N.v54662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54662 s i)) at 1.
  unfold R.v54662, N.v54662.
  rewrite ?node_54658.
  rewrite ?node_54661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54663 (s : N.State) (i : N.Inputs) :
  R.v54663 (state s) (inputs i) = Zmod.unsigned (N.v54663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54663 s i)) at 1.
  unfold R.v54663, N.v54663.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54664 (s : N.State) (i : N.Inputs) :
  R.v54664 (state s) (inputs i) = Zmod.unsigned (N.v54664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54664 s i)) at 1.
  unfold R.v54664, N.v54664.
  unfold R.v6, N.v6.
  rewrite ?node_6770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54665 (s : N.State) (i : N.Inputs) :
  R.v54665 (state s) (inputs i) = Zmod.unsigned (N.v54665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54665 s i)) at 1.
  unfold R.v54665, N.v54665.
  unfold R.v6, N.v6.
  rewrite ?node_6769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54666 (s : N.State) (i : N.Inputs) :
  R.v54666 (state s) (inputs i) = Zmod.unsigned (N.v54666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54666 s i)) at 1.
  unfold R.v54666, N.v54666.
  rewrite ?node_54664.
  rewrite ?node_54665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54667 (s : N.State) (i : N.Inputs) :
  R.v54667 (state s) (inputs i) = Zmod.unsigned (N.v54667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54667 s i)) at 1.
  unfold R.v54667, N.v54667.
  unfold R.v16463, N.v16463.
  rewrite ?node_54666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54668 (s : N.State) (i : N.Inputs) :
  R.v54668 (state s) (inputs i) = Zmod.unsigned (N.v54668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54668 s i)) at 1.
  unfold R.v54668, N.v54668.
  rewrite ?node_6771.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54669 (s : N.State) (i : N.Inputs) :
  R.v54669 (state s) (inputs i) = Zmod.unsigned (N.v54669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54669 s i)) at 1.
  unfold R.v54669, N.v54669.
  unfold R.v6, N.v6.
  rewrite ?node_6866.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54670 (s : N.State) (i : N.Inputs) :
  R.v54670 (state s) (inputs i) = Zmod.unsigned (N.v54670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54670 s i)) at 1.
  unfold R.v54670, N.v54670.
  rewrite ?node_54668.
  rewrite ?node_54669.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54671 (s : N.State) (i : N.Inputs) :
  R.v54671 (state s) (inputs i) = Zmod.unsigned (N.v54671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54671 s i)) at 1.
  unfold R.v54671, N.v54671.
  rewrite ?node_54667.
  rewrite ?node_54670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54672 (s : N.State) (i : N.Inputs) :
  R.v54672 (state s) (inputs i) = Zmod.unsigned (N.v54672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54672 s i)) at 1.
  unfold R.v54672, N.v54672.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54673 (s : N.State) (i : N.Inputs) :
  R.v54673 (state s) (inputs i) = Zmod.unsigned (N.v54673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54673 s i)) at 1.
  unfold R.v54673, N.v54673.
  rewrite ?node_6864.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54674 (s : N.State) (i : N.Inputs) :
  R.v54674 (state s) (inputs i) = Zmod.unsigned (N.v54674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54674 s i)) at 1.
  unfold R.v54674, N.v54674.
  rewrite ?node_6860.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54675 (s : N.State) (i : N.Inputs) :
  R.v54675 (state s) (inputs i) = Zmod.unsigned (N.v54675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54675 s i)) at 1.
  unfold R.v54675, N.v54675.
  rewrite ?node_6858.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54676 (s : N.State) (i : N.Inputs) :
  R.v54676 (state s) (inputs i) = Zmod.unsigned (N.v54676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54676 s i)) at 1.
  unfold R.v54676, N.v54676.
  unfold R.v6, N.v6.
  rewrite ?node_6854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54677 (s : N.State) (i : N.Inputs) :
  R.v54677 (state s) (inputs i) = Zmod.unsigned (N.v54677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54677 s i)) at 1.
  unfold R.v54677, N.v54677.
  unfold R.v6, N.v6.
  rewrite ?node_6849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54678 (s : N.State) (i : N.Inputs) :
  R.v54678 (state s) (inputs i) = Zmod.unsigned (N.v54678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54678 s i)) at 1.
  unfold R.v54678, N.v54678.
  rewrite ?node_54676.
  rewrite ?node_54677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54679 (s : N.State) (i : N.Inputs) :
  R.v54679 (state s) (inputs i) = Zmod.unsigned (N.v54679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54679 s i)) at 1.
  unfold R.v54679, N.v54679.
  unfold R.v16484, N.v16484.
  rewrite ?node_54678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54680 (s : N.State) (i : N.Inputs) :
  R.v54680 (state s) (inputs i) = Zmod.unsigned (N.v54680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54680 s i)) at 1.
  unfold R.v54680, N.v54680.
  rewrite ?node_54673.
  rewrite ?node_54674.
  rewrite ?node_54675.
  rewrite ?node_54679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54681 (s : N.State) (i : N.Inputs) :
  R.v54681 (state s) (inputs i) = Zmod.unsigned (N.v54681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54681 s i)) at 1.
  unfold R.v54681, N.v54681.
  unfold R.v6, N.v6.
  rewrite ?node_54680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54682 (s : N.State) (i : N.Inputs) :
  R.v54682 (state s) (inputs i) = Zmod.unsigned (N.v54682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54682 s i)) at 1.
  unfold R.v54682, N.v54682.
  rewrite ?node_6865.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54683 (s : N.State) (i : N.Inputs) :
  R.v54683 (state s) (inputs i) = Zmod.unsigned (N.v54683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54683 s i)) at 1.
  unfold R.v54683, N.v54683.
  unfold R.v6, N.v6.
  rewrite ?node_6958.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54684 (s : N.State) (i : N.Inputs) :
  R.v54684 (state s) (inputs i) = Zmod.unsigned (N.v54684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54684 s i)) at 1.
  unfold R.v54684, N.v54684.
  unfold R.v6, N.v6.
  rewrite ?node_6962.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54685 (s : N.State) (i : N.Inputs) :
  R.v54685 (state s) (inputs i) = Zmod.unsigned (N.v54685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54685 s i)) at 1.
  unfold R.v54685, N.v54685.
  rewrite ?node_54682.
  rewrite ?node_54683.
  rewrite ?node_54684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54686 (s : N.State) (i : N.Inputs) :
  R.v54686 (state s) (inputs i) = Zmod.unsigned (N.v54686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54686 s i)) at 1.
  unfold R.v54686, N.v54686.
  rewrite ?node_54681.
  rewrite ?node_54685.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54687 (s : N.State) (i : N.Inputs) :
  R.v54687 (state s) (inputs i) = Zmod.unsigned (N.v54687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54687 s i)) at 1.
  unfold R.v54687, N.v54687.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54688 (s : N.State) (i : N.Inputs) :
  R.v54688 (state s) (inputs i) = Zmod.unsigned (N.v54688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54688 s i)) at 1.
  unfold R.v54688, N.v54688.
  rewrite ?node_6858.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54689 (s : N.State) (i : N.Inputs) :
  R.v54689 (state s) (inputs i) = Zmod.unsigned (N.v54689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54689 s i)) at 1.
  unfold R.v54689, N.v54689.
  unfold R.v6, N.v6.
  rewrite ?node_6854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54690 (s : N.State) (i : N.Inputs) :
  R.v54690 (state s) (inputs i) = Zmod.unsigned (N.v54690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54690 s i)) at 1.
  unfold R.v54690, N.v54690.
  unfold R.v6, N.v6.
  rewrite ?node_6849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54691 (s : N.State) (i : N.Inputs) :
  R.v54691 (state s) (inputs i) = Zmod.unsigned (N.v54691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54691 s i)) at 1.
  unfold R.v54691, N.v54691.
  rewrite ?node_54689.
  rewrite ?node_54690.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54692 (s : N.State) (i : N.Inputs) :
  R.v54692 (state s) (inputs i) = Zmod.unsigned (N.v54692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54692 s i)) at 1.
  unfold R.v54692, N.v54692.
  unfold R.v16484, N.v16484.
  rewrite ?node_54691.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54693 (s : N.State) (i : N.Inputs) :
  R.v54693 (state s) (inputs i) = Zmod.unsigned (N.v54693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54693 s i)) at 1.
  unfold R.v54693, N.v54693.
  rewrite ?node_54688.
  rewrite ?node_54692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54694 (s : N.State) (i : N.Inputs) :
  R.v54694 (state s) (inputs i) = Zmod.unsigned (N.v54694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54694 s i)) at 1.
  unfold R.v54694, N.v54694.
  unfold R.v6, N.v6.
  rewrite ?node_54693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54695 (s : N.State) (i : N.Inputs) :
  R.v54695 (state s) (inputs i) = Zmod.unsigned (N.v54695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54695 s i)) at 1.
  unfold R.v54695, N.v54695.
  rewrite ?node_6859.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54696 (s : N.State) (i : N.Inputs) :
  R.v54696 (state s) (inputs i) = Zmod.unsigned (N.v54696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54696 s i)) at 1.
  unfold R.v54696, N.v54696.
  unfold R.v6, N.v6.
  rewrite ?node_6958.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54697 (s : N.State) (i : N.Inputs) :
  R.v54697 (state s) (inputs i) = Zmod.unsigned (N.v54697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54697 s i)) at 1.
  unfold R.v54697, N.v54697.
  rewrite ?node_54695.
  rewrite ?node_54696.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54698 (s : N.State) (i : N.Inputs) :
  R.v54698 (state s) (inputs i) = Zmod.unsigned (N.v54698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54698 s i)) at 1.
  unfold R.v54698, N.v54698.
  rewrite ?node_54694.
  rewrite ?node_54697.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54699 (s : N.State) (i : N.Inputs) :
  R.v54699 (state s) (inputs i) = Zmod.unsigned (N.v54699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54699 s i)) at 1.
  unfold R.v54699, N.v54699.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54700 (s : N.State) (i : N.Inputs) :
  R.v54700 (state s) (inputs i) = Zmod.unsigned (N.v54700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54700 s i)) at 1.
  unfold R.v54700, N.v54700.
  rewrite ?node_6864.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54701 (s : N.State) (i : N.Inputs) :
  R.v54701 (state s) (inputs i) = Zmod.unsigned (N.v54701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54701 s i)) at 1.
  unfold R.v54701, N.v54701.
  unfold R.v6, N.v6.
  rewrite ?node_6860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54702 (s : N.State) (i : N.Inputs) :
  R.v54702 (state s) (inputs i) = Zmod.unsigned (N.v54702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54702 s i)) at 1.
  unfold R.v54702, N.v54702.
  unfold R.v6, N.v6.
  rewrite ?node_6859.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54703 (s : N.State) (i : N.Inputs) :
  R.v54703 (state s) (inputs i) = Zmod.unsigned (N.v54703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54703 s i)) at 1.
  unfold R.v54703, N.v54703.
  rewrite ?node_54701.
  rewrite ?node_54702.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54704 (s : N.State) (i : N.Inputs) :
  R.v54704 (state s) (inputs i) = Zmod.unsigned (N.v54704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54704 s i)) at 1.
  unfold R.v54704, N.v54704.
  unfold R.v16484, N.v16484.
  rewrite ?node_54703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54705 (s : N.State) (i : N.Inputs) :
  R.v54705 (state s) (inputs i) = Zmod.unsigned (N.v54705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54705 s i)) at 1.
  unfold R.v54705, N.v54705.
  rewrite ?node_54700.
  rewrite ?node_54704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54706 (s : N.State) (i : N.Inputs) :
  R.v54706 (state s) (inputs i) = Zmod.unsigned (N.v54706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54706 s i)) at 1.
  unfold R.v54706, N.v54706.
  unfold R.v6, N.v6.
  rewrite ?node_54705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54707 (s : N.State) (i : N.Inputs) :
  R.v54707 (state s) (inputs i) = Zmod.unsigned (N.v54707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54707 s i)) at 1.
  unfold R.v54707, N.v54707.
  rewrite ?node_6865.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54708 (s : N.State) (i : N.Inputs) :
  R.v54708 (state s) (inputs i) = Zmod.unsigned (N.v54708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54708 s i)) at 1.
  unfold R.v54708, N.v54708.
  unfold R.v6, N.v6.
  rewrite ?node_6962.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54709 (s : N.State) (i : N.Inputs) :
  R.v54709 (state s) (inputs i) = Zmod.unsigned (N.v54709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54709 s i)) at 1.
  unfold R.v54709, N.v54709.
  rewrite ?node_54707.
  rewrite ?node_54708.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54710 (s : N.State) (i : N.Inputs) :
  R.v54710 (state s) (inputs i) = Zmod.unsigned (N.v54710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54710 s i)) at 1.
  unfold R.v54710, N.v54710.
  rewrite ?node_54706.
  rewrite ?node_54709.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54711 (s : N.State) (i : N.Inputs) :
  R.v54711 (state s) (inputs i) = Zmod.unsigned (N.v54711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54711 s i)) at 1.
  unfold R.v54711, N.v54711.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54712 (s : N.State) (i : N.Inputs) :
  R.v54712 (state s) (inputs i) = Zmod.unsigned (N.v54712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54712 s i)) at 1.
  unfold R.v54712, N.v54712.
  rewrite ?node_6958.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54713 (s : N.State) (i : N.Inputs) :
  R.v54713 (state s) (inputs i) = Zmod.unsigned (N.v54713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54713 s i)) at 1.
  unfold R.v54713, N.v54713.
  rewrite ?node_6954.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54714 (s : N.State) (i : N.Inputs) :
  R.v54714 (state s) (inputs i) = Zmod.unsigned (N.v54714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54714 s i)) at 1.
  unfold R.v54714, N.v54714.
  rewrite ?node_6952.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54715 (s : N.State) (i : N.Inputs) :
  R.v54715 (state s) (inputs i) = Zmod.unsigned (N.v54715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54715 s i)) at 1.
  unfold R.v54715, N.v54715.
  unfold R.v6, N.v6.
  rewrite ?node_6948.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54716 (s : N.State) (i : N.Inputs) :
  R.v54716 (state s) (inputs i) = Zmod.unsigned (N.v54716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54716 s i)) at 1.
  unfold R.v54716, N.v54716.
  unfold R.v6, N.v6.
  rewrite ?node_6943.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54717 (s : N.State) (i : N.Inputs) :
  R.v54717 (state s) (inputs i) = Zmod.unsigned (N.v54717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54717 s i)) at 1.
  unfold R.v54717, N.v54717.
  rewrite ?node_54715.
  rewrite ?node_54716.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54718 (s : N.State) (i : N.Inputs) :
  R.v54718 (state s) (inputs i) = Zmod.unsigned (N.v54718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54718 s i)) at 1.
  unfold R.v54718, N.v54718.
  unfold R.v16484, N.v16484.
  rewrite ?node_54717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54719 (s : N.State) (i : N.Inputs) :
  R.v54719 (state s) (inputs i) = Zmod.unsigned (N.v54719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54719 s i)) at 1.
  unfold R.v54719, N.v54719.
  rewrite ?node_54712.
  rewrite ?node_54713.
  rewrite ?node_54714.
  rewrite ?node_54718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54720 (s : N.State) (i : N.Inputs) :
  R.v54720 (state s) (inputs i) = Zmod.unsigned (N.v54720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54720 s i)) at 1.
  unfold R.v54720, N.v54720.
  unfold R.v6, N.v6.
  rewrite ?node_54719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54721 (s : N.State) (i : N.Inputs) :
  R.v54721 (state s) (inputs i) = Zmod.unsigned (N.v54721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54721 s i)) at 1.
  unfold R.v54721, N.v54721.
  rewrite ?node_6959.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54722 (s : N.State) (i : N.Inputs) :
  R.v54722 (state s) (inputs i) = Zmod.unsigned (N.v54722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54722 s i)) at 1.
  unfold R.v54722, N.v54722.
  unfold R.v6, N.v6.
  rewrite ?node_7057.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54723 (s : N.State) (i : N.Inputs) :
  R.v54723 (state s) (inputs i) = Zmod.unsigned (N.v54723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54723 s i)) at 1.
  unfold R.v54723, N.v54723.
  unfold R.v6, N.v6.
  rewrite ?node_7061.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54724 (s : N.State) (i : N.Inputs) :
  R.v54724 (state s) (inputs i) = Zmod.unsigned (N.v54724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54724 s i)) at 1.
  unfold R.v54724, N.v54724.
  rewrite ?node_54721.
  rewrite ?node_54722.
  rewrite ?node_54723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54725 (s : N.State) (i : N.Inputs) :
  R.v54725 (state s) (inputs i) = Zmod.unsigned (N.v54725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54725 s i)) at 1.
  unfold R.v54725, N.v54725.
  rewrite ?node_54720.
  rewrite ?node_54724.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54726 (s : N.State) (i : N.Inputs) :
  R.v54726 (state s) (inputs i) = Zmod.unsigned (N.v54726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54726 s i)) at 1.
  unfold R.v54726, N.v54726.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54727 (s : N.State) (i : N.Inputs) :
  R.v54727 (state s) (inputs i) = Zmod.unsigned (N.v54727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54727 s i)) at 1.
  unfold R.v54727, N.v54727.
  rewrite ?node_6952.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54728 (s : N.State) (i : N.Inputs) :
  R.v54728 (state s) (inputs i) = Zmod.unsigned (N.v54728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54728 s i)) at 1.
  unfold R.v54728, N.v54728.
  unfold R.v6, N.v6.
  rewrite ?node_6948.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54729 (s : N.State) (i : N.Inputs) :
  R.v54729 (state s) (inputs i) = Zmod.unsigned (N.v54729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54729 s i)) at 1.
  unfold R.v54729, N.v54729.
  unfold R.v6, N.v6.
  rewrite ?node_6943.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54730 (s : N.State) (i : N.Inputs) :
  R.v54730 (state s) (inputs i) = Zmod.unsigned (N.v54730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54730 s i)) at 1.
  unfold R.v54730, N.v54730.
  rewrite ?node_54728.
  rewrite ?node_54729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54731 (s : N.State) (i : N.Inputs) :
  R.v54731 (state s) (inputs i) = Zmod.unsigned (N.v54731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54731 s i)) at 1.
  unfold R.v54731, N.v54731.
  unfold R.v16484, N.v16484.
  rewrite ?node_54730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54732 (s : N.State) (i : N.Inputs) :
  R.v54732 (state s) (inputs i) = Zmod.unsigned (N.v54732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54732 s i)) at 1.
  unfold R.v54732, N.v54732.
  rewrite ?node_54727.
  rewrite ?node_54731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54733 (s : N.State) (i : N.Inputs) :
  R.v54733 (state s) (inputs i) = Zmod.unsigned (N.v54733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54733 s i)) at 1.
  unfold R.v54733, N.v54733.
  unfold R.v6, N.v6.
  rewrite ?node_54732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54734 (s : N.State) (i : N.Inputs) :
  R.v54734 (state s) (inputs i) = Zmod.unsigned (N.v54734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54734 s i)) at 1.
  unfold R.v54734, N.v54734.
  rewrite ?node_6953.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54735 (s : N.State) (i : N.Inputs) :
  R.v54735 (state s) (inputs i) = Zmod.unsigned (N.v54735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54735 s i)) at 1.
  unfold R.v54735, N.v54735.
  unfold R.v6, N.v6.
  rewrite ?node_7057.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54736 (s : N.State) (i : N.Inputs) :
  R.v54736 (state s) (inputs i) = Zmod.unsigned (N.v54736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54736 s i)) at 1.
  unfold R.v54736, N.v54736.
  rewrite ?node_54734.
  rewrite ?node_54735.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54737 (s : N.State) (i : N.Inputs) :
  R.v54737 (state s) (inputs i) = Zmod.unsigned (N.v54737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54737 s i)) at 1.
  unfold R.v54737, N.v54737.
  rewrite ?node_54733.
  rewrite ?node_54736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54738 (s : N.State) (i : N.Inputs) :
  R.v54738 (state s) (inputs i) = Zmod.unsigned (N.v54738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54738 s i)) at 1.
  unfold R.v54738, N.v54738.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54739 (s : N.State) (i : N.Inputs) :
  R.v54739 (state s) (inputs i) = Zmod.unsigned (N.v54739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54739 s i)) at 1.
  unfold R.v54739, N.v54739.
  rewrite ?node_6958.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54740 (s : N.State) (i : N.Inputs) :
  R.v54740 (state s) (inputs i) = Zmod.unsigned (N.v54740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54740 s i)) at 1.
  unfold R.v54740, N.v54740.
  unfold R.v6, N.v6.
  rewrite ?node_6954.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54741 (s : N.State) (i : N.Inputs) :
  R.v54741 (state s) (inputs i) = Zmod.unsigned (N.v54741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54741 s i)) at 1.
  unfold R.v54741, N.v54741.
  unfold R.v6, N.v6.
  rewrite ?node_6953.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54742 (s : N.State) (i : N.Inputs) :
  R.v54742 (state s) (inputs i) = Zmod.unsigned (N.v54742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54742 s i)) at 1.
  unfold R.v54742, N.v54742.
  rewrite ?node_54740.
  rewrite ?node_54741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54743 (s : N.State) (i : N.Inputs) :
  R.v54743 (state s) (inputs i) = Zmod.unsigned (N.v54743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54743 s i)) at 1.
  unfold R.v54743, N.v54743.
  unfold R.v16484, N.v16484.
  rewrite ?node_54742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54744 (s : N.State) (i : N.Inputs) :
  R.v54744 (state s) (inputs i) = Zmod.unsigned (N.v54744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54744 s i)) at 1.
  unfold R.v54744, N.v54744.
  rewrite ?node_54739.
  rewrite ?node_54743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54745 (s : N.State) (i : N.Inputs) :
  R.v54745 (state s) (inputs i) = Zmod.unsigned (N.v54745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54745 s i)) at 1.
  unfold R.v54745, N.v54745.
  unfold R.v6, N.v6.
  rewrite ?node_54744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54746 (s : N.State) (i : N.Inputs) :
  R.v54746 (state s) (inputs i) = Zmod.unsigned (N.v54746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54746 s i)) at 1.
  unfold R.v54746, N.v54746.
  rewrite ?node_6959.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54747 (s : N.State) (i : N.Inputs) :
  R.v54747 (state s) (inputs i) = Zmod.unsigned (N.v54747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54747 s i)) at 1.
  unfold R.v54747, N.v54747.
  unfold R.v6, N.v6.
  rewrite ?node_7061.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54748 (s : N.State) (i : N.Inputs) :
  R.v54748 (state s) (inputs i) = Zmod.unsigned (N.v54748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54748 s i)) at 1.
  unfold R.v54748, N.v54748.
  rewrite ?node_54746.
  rewrite ?node_54747.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54749 (s : N.State) (i : N.Inputs) :
  R.v54749 (state s) (inputs i) = Zmod.unsigned (N.v54749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54749 s i)) at 1.
  unfold R.v54749, N.v54749.
  rewrite ?node_54745.
  rewrite ?node_54748.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54750 (s : N.State) (i : N.Inputs) :
  R.v54750 (state s) (inputs i) = Zmod.unsigned (N.v54750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54750 s i)) at 1.
  unfold R.v54750, N.v54750.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54751 (s : N.State) (i : N.Inputs) :
  R.v54751 (state s) (inputs i) = Zmod.unsigned (N.v54751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54751 s i)) at 1.
  unfold R.v54751, N.v54751.
  rewrite ?node_7057.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54752 (s : N.State) (i : N.Inputs) :
  R.v54752 (state s) (inputs i) = Zmod.unsigned (N.v54752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54752 s i)) at 1.
  unfold R.v54752, N.v54752.
  rewrite ?node_7053.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54753 (s : N.State) (i : N.Inputs) :
  R.v54753 (state s) (inputs i) = Zmod.unsigned (N.v54753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54753 s i)) at 1.
  unfold R.v54753, N.v54753.
  rewrite ?node_7051.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54754 (s : N.State) (i : N.Inputs) :
  R.v54754 (state s) (inputs i) = Zmod.unsigned (N.v54754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54754 s i)) at 1.
  unfold R.v54754, N.v54754.
  unfold R.v6, N.v6.
  rewrite ?node_7047.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54755 (s : N.State) (i : N.Inputs) :
  R.v54755 (state s) (inputs i) = Zmod.unsigned (N.v54755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54755 s i)) at 1.
  unfold R.v54755, N.v54755.
  unfold R.v6, N.v6.
  rewrite ?node_7042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54756 (s : N.State) (i : N.Inputs) :
  R.v54756 (state s) (inputs i) = Zmod.unsigned (N.v54756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54756 s i)) at 1.
  unfold R.v54756, N.v54756.
  rewrite ?node_54754.
  rewrite ?node_54755.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54757 (s : N.State) (i : N.Inputs) :
  R.v54757 (state s) (inputs i) = Zmod.unsigned (N.v54757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54757 s i)) at 1.
  unfold R.v54757, N.v54757.
  unfold R.v16484, N.v16484.
  rewrite ?node_54756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54758 (s : N.State) (i : N.Inputs) :
  R.v54758 (state s) (inputs i) = Zmod.unsigned (N.v54758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54758 s i)) at 1.
  unfold R.v54758, N.v54758.
  rewrite ?node_54751.
  rewrite ?node_54752.
  rewrite ?node_54753.
  rewrite ?node_54757.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54759 (s : N.State) (i : N.Inputs) :
  R.v54759 (state s) (inputs i) = Zmod.unsigned (N.v54759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54759 s i)) at 1.
  unfold R.v54759, N.v54759.
  unfold R.v6, N.v6.
  rewrite ?node_54758.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54760 (s : N.State) (i : N.Inputs) :
  R.v54760 (state s) (inputs i) = Zmod.unsigned (N.v54760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54760 s i)) at 1.
  unfold R.v54760, N.v54760.
  rewrite ?node_7058.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54761 (s : N.State) (i : N.Inputs) :
  R.v54761 (state s) (inputs i) = Zmod.unsigned (N.v54761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54761 s i)) at 1.
  unfold R.v54761, N.v54761.
  unfold R.v6, N.v6.
  rewrite ?node_7158.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54762 (s : N.State) (i : N.Inputs) :
  R.v54762 (state s) (inputs i) = Zmod.unsigned (N.v54762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54762 s i)) at 1.
  unfold R.v54762, N.v54762.
  unfold R.v6, N.v6.
  rewrite ?node_7162.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54763 (s : N.State) (i : N.Inputs) :
  R.v54763 (state s) (inputs i) = Zmod.unsigned (N.v54763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54763 s i)) at 1.
  unfold R.v54763, N.v54763.
  rewrite ?node_54760.
  rewrite ?node_54761.
  rewrite ?node_54762.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54764 (s : N.State) (i : N.Inputs) :
  R.v54764 (state s) (inputs i) = Zmod.unsigned (N.v54764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54764 s i)) at 1.
  unfold R.v54764, N.v54764.
  rewrite ?node_54759.
  rewrite ?node_54763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54765 (s : N.State) (i : N.Inputs) :
  R.v54765 (state s) (inputs i) = Zmod.unsigned (N.v54765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54765 s i)) at 1.
  unfold R.v54765, N.v54765.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54766 (s : N.State) (i : N.Inputs) :
  R.v54766 (state s) (inputs i) = Zmod.unsigned (N.v54766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54766 s i)) at 1.
  unfold R.v54766, N.v54766.
  rewrite ?node_7051.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54767 (s : N.State) (i : N.Inputs) :
  R.v54767 (state s) (inputs i) = Zmod.unsigned (N.v54767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54767 s i)) at 1.
  unfold R.v54767, N.v54767.
  unfold R.v6, N.v6.
  rewrite ?node_7047.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54768 (s : N.State) (i : N.Inputs) :
  R.v54768 (state s) (inputs i) = Zmod.unsigned (N.v54768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54768 s i)) at 1.
  unfold R.v54768, N.v54768.
  unfold R.v6, N.v6.
  rewrite ?node_7042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54769 (s : N.State) (i : N.Inputs) :
  R.v54769 (state s) (inputs i) = Zmod.unsigned (N.v54769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54769 s i)) at 1.
  unfold R.v54769, N.v54769.
  rewrite ?node_54767.
  rewrite ?node_54768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54770 (s : N.State) (i : N.Inputs) :
  R.v54770 (state s) (inputs i) = Zmod.unsigned (N.v54770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54770 s i)) at 1.
  unfold R.v54770, N.v54770.
  unfold R.v16484, N.v16484.
  rewrite ?node_54769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54771 (s : N.State) (i : N.Inputs) :
  R.v54771 (state s) (inputs i) = Zmod.unsigned (N.v54771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54771 s i)) at 1.
  unfold R.v54771, N.v54771.
  rewrite ?node_54766.
  rewrite ?node_54770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54772 (s : N.State) (i : N.Inputs) :
  R.v54772 (state s) (inputs i) = Zmod.unsigned (N.v54772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54772 s i)) at 1.
  unfold R.v54772, N.v54772.
  unfold R.v6, N.v6.
  rewrite ?node_54771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54773 (s : N.State) (i : N.Inputs) :
  R.v54773 (state s) (inputs i) = Zmod.unsigned (N.v54773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54773 s i)) at 1.
  unfold R.v54773, N.v54773.
  rewrite ?node_7052.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54774 (s : N.State) (i : N.Inputs) :
  R.v54774 (state s) (inputs i) = Zmod.unsigned (N.v54774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54774 s i)) at 1.
  unfold R.v54774, N.v54774.
  unfold R.v6, N.v6.
  rewrite ?node_7158.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54775 (s : N.State) (i : N.Inputs) :
  R.v54775 (state s) (inputs i) = Zmod.unsigned (N.v54775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54775 s i)) at 1.
  unfold R.v54775, N.v54775.
  rewrite ?node_54773.
  rewrite ?node_54774.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54776 (s : N.State) (i : N.Inputs) :
  R.v54776 (state s) (inputs i) = Zmod.unsigned (N.v54776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54776 s i)) at 1.
  unfold R.v54776, N.v54776.
  rewrite ?node_54772.
  rewrite ?node_54775.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54777 (s : N.State) (i : N.Inputs) :
  R.v54777 (state s) (inputs i) = Zmod.unsigned (N.v54777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54777 s i)) at 1.
  unfold R.v54777, N.v54777.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54778 (s : N.State) (i : N.Inputs) :
  R.v54778 (state s) (inputs i) = Zmod.unsigned (N.v54778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54778 s i)) at 1.
  unfold R.v54778, N.v54778.
  rewrite ?node_7057.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54779 (s : N.State) (i : N.Inputs) :
  R.v54779 (state s) (inputs i) = Zmod.unsigned (N.v54779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54779 s i)) at 1.
  unfold R.v54779, N.v54779.
  unfold R.v6, N.v6.
  rewrite ?node_7053.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54780 (s : N.State) (i : N.Inputs) :
  R.v54780 (state s) (inputs i) = Zmod.unsigned (N.v54780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54780 s i)) at 1.
  unfold R.v54780, N.v54780.
  unfold R.v6, N.v6.
  rewrite ?node_7052.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54781 (s : N.State) (i : N.Inputs) :
  R.v54781 (state s) (inputs i) = Zmod.unsigned (N.v54781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54781 s i)) at 1.
  unfold R.v54781, N.v54781.
  rewrite ?node_54779.
  rewrite ?node_54780.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54782 (s : N.State) (i : N.Inputs) :
  R.v54782 (state s) (inputs i) = Zmod.unsigned (N.v54782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54782 s i)) at 1.
  unfold R.v54782, N.v54782.
  unfold R.v16484, N.v16484.
  rewrite ?node_54781.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54783 (s : N.State) (i : N.Inputs) :
  R.v54783 (state s) (inputs i) = Zmod.unsigned (N.v54783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54783 s i)) at 1.
  unfold R.v54783, N.v54783.
  rewrite ?node_54778.
  rewrite ?node_54782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54784 (s : N.State) (i : N.Inputs) :
  R.v54784 (state s) (inputs i) = Zmod.unsigned (N.v54784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54784 s i)) at 1.
  unfold R.v54784, N.v54784.
  unfold R.v6, N.v6.
  rewrite ?node_54783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54785 (s : N.State) (i : N.Inputs) :
  R.v54785 (state s) (inputs i) = Zmod.unsigned (N.v54785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54785 s i)) at 1.
  unfold R.v54785, N.v54785.
  rewrite ?node_7058.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54786 (s : N.State) (i : N.Inputs) :
  R.v54786 (state s) (inputs i) = Zmod.unsigned (N.v54786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54786 s i)) at 1.
  unfold R.v54786, N.v54786.
  unfold R.v6, N.v6.
  rewrite ?node_7162.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54787 (s : N.State) (i : N.Inputs) :
  R.v54787 (state s) (inputs i) = Zmod.unsigned (N.v54787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54787 s i)) at 1.
  unfold R.v54787, N.v54787.
  rewrite ?node_54785.
  rewrite ?node_54786.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54788 (s : N.State) (i : N.Inputs) :
  R.v54788 (state s) (inputs i) = Zmod.unsigned (N.v54788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54788 s i)) at 1.
  unfold R.v54788, N.v54788.
  rewrite ?node_54784.
  rewrite ?node_54787.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54789 (s : N.State) (i : N.Inputs) :
  R.v54789 (state s) (inputs i) = Zmod.unsigned (N.v54789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54789 s i)) at 1.
  unfold R.v54789, N.v54789.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54790 (s : N.State) (i : N.Inputs) :
  R.v54790 (state s) (inputs i) = Zmod.unsigned (N.v54790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54790 s i)) at 1.
  unfold R.v54790, N.v54790.
  rewrite ?node_7158.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54791 (s : N.State) (i : N.Inputs) :
  R.v54791 (state s) (inputs i) = Zmod.unsigned (N.v54791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54791 s i)) at 1.
  unfold R.v54791, N.v54791.
  rewrite ?node_7154.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54792 (s : N.State) (i : N.Inputs) :
  R.v54792 (state s) (inputs i) = Zmod.unsigned (N.v54792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54792 s i)) at 1.
  unfold R.v54792, N.v54792.
  rewrite ?node_7152.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54793 (s : N.State) (i : N.Inputs) :
  R.v54793 (state s) (inputs i) = Zmod.unsigned (N.v54793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54793 s i)) at 1.
  unfold R.v54793, N.v54793.
  unfold R.v6, N.v6.
  rewrite ?node_7148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54794 (s : N.State) (i : N.Inputs) :
  R.v54794 (state s) (inputs i) = Zmod.unsigned (N.v54794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54794 s i)) at 1.
  unfold R.v54794, N.v54794.
  unfold R.v6, N.v6.
  rewrite ?node_7141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54795 (s : N.State) (i : N.Inputs) :
  R.v54795 (state s) (inputs i) = Zmod.unsigned (N.v54795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54795 s i)) at 1.
  unfold R.v54795, N.v54795.
  rewrite ?node_54793.
  rewrite ?node_54794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54796 (s : N.State) (i : N.Inputs) :
  R.v54796 (state s) (inputs i) = Zmod.unsigned (N.v54796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54796 s i)) at 1.
  unfold R.v54796, N.v54796.
  unfold R.v16484, N.v16484.
  rewrite ?node_54795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54797 (s : N.State) (i : N.Inputs) :
  R.v54797 (state s) (inputs i) = Zmod.unsigned (N.v54797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54797 s i)) at 1.
  unfold R.v54797, N.v54797.
  rewrite ?node_54790.
  rewrite ?node_54791.
  rewrite ?node_54792.
  rewrite ?node_54796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54798 (s : N.State) (i : N.Inputs) :
  R.v54798 (state s) (inputs i) = Zmod.unsigned (N.v54798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54798 s i)) at 1.
  unfold R.v54798, N.v54798.
  unfold R.v6, N.v6.
  rewrite ?node_54797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54799 (s : N.State) (i : N.Inputs) :
  R.v54799 (state s) (inputs i) = Zmod.unsigned (N.v54799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54799 s i)) at 1.
  unfold R.v54799, N.v54799.
  rewrite ?node_7159.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54800 (s : N.State) (i : N.Inputs) :
  R.v54800 (state s) (inputs i) = Zmod.unsigned (N.v54800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54800 s i)) at 1.
  unfold R.v54800, N.v54800.
  unfold R.v6, N.v6.
  rewrite ?node_7260.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54801 (s : N.State) (i : N.Inputs) :
  R.v54801 (state s) (inputs i) = Zmod.unsigned (N.v54801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54801 s i)) at 1.
  unfold R.v54801, N.v54801.
  unfold R.v6, N.v6.
  rewrite ?node_7264.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54802 (s : N.State) (i : N.Inputs) :
  R.v54802 (state s) (inputs i) = Zmod.unsigned (N.v54802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54802 s i)) at 1.
  unfold R.v54802, N.v54802.
  rewrite ?node_54799.
  rewrite ?node_54800.
  rewrite ?node_54801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54803 (s : N.State) (i : N.Inputs) :
  R.v54803 (state s) (inputs i) = Zmod.unsigned (N.v54803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54803 s i)) at 1.
  unfold R.v54803, N.v54803.
  rewrite ?node_54798.
  rewrite ?node_54802.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54804 (s : N.State) (i : N.Inputs) :
  R.v54804 (state s) (inputs i) = Zmod.unsigned (N.v54804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54804 s i)) at 1.
  unfold R.v54804, N.v54804.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54805 (s : N.State) (i : N.Inputs) :
  R.v54805 (state s) (inputs i) = Zmod.unsigned (N.v54805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54805 s i)) at 1.
  unfold R.v54805, N.v54805.
  rewrite ?node_7152.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54806 (s : N.State) (i : N.Inputs) :
  R.v54806 (state s) (inputs i) = Zmod.unsigned (N.v54806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54806 s i)) at 1.
  unfold R.v54806, N.v54806.
  unfold R.v6, N.v6.
  rewrite ?node_7148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54807 (s : N.State) (i : N.Inputs) :
  R.v54807 (state s) (inputs i) = Zmod.unsigned (N.v54807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54807 s i)) at 1.
  unfold R.v54807, N.v54807.
  unfold R.v6, N.v6.
  rewrite ?node_7141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54808 (s : N.State) (i : N.Inputs) :
  R.v54808 (state s) (inputs i) = Zmod.unsigned (N.v54808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54808 s i)) at 1.
  unfold R.v54808, N.v54808.
  rewrite ?node_54806.
  rewrite ?node_54807.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54809 (s : N.State) (i : N.Inputs) :
  R.v54809 (state s) (inputs i) = Zmod.unsigned (N.v54809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54809 s i)) at 1.
  unfold R.v54809, N.v54809.
  unfold R.v16484, N.v16484.
  rewrite ?node_54808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54810 (s : N.State) (i : N.Inputs) :
  R.v54810 (state s) (inputs i) = Zmod.unsigned (N.v54810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54810 s i)) at 1.
  unfold R.v54810, N.v54810.
  rewrite ?node_54805.
  rewrite ?node_54809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54811 (s : N.State) (i : N.Inputs) :
  R.v54811 (state s) (inputs i) = Zmod.unsigned (N.v54811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54811 s i)) at 1.
  unfold R.v54811, N.v54811.
  unfold R.v6, N.v6.
  rewrite ?node_54810.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54812 (s : N.State) (i : N.Inputs) :
  R.v54812 (state s) (inputs i) = Zmod.unsigned (N.v54812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54812 s i)) at 1.
  unfold R.v54812, N.v54812.
  rewrite ?node_7153.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54813 (s : N.State) (i : N.Inputs) :
  R.v54813 (state s) (inputs i) = Zmod.unsigned (N.v54813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54813 s i)) at 1.
  unfold R.v54813, N.v54813.
  unfold R.v6, N.v6.
  rewrite ?node_7260.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54814 (s : N.State) (i : N.Inputs) :
  R.v54814 (state s) (inputs i) = Zmod.unsigned (N.v54814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54814 s i)) at 1.
  unfold R.v54814, N.v54814.
  rewrite ?node_54812.
  rewrite ?node_54813.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54815 (s : N.State) (i : N.Inputs) :
  R.v54815 (state s) (inputs i) = Zmod.unsigned (N.v54815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54815 s i)) at 1.
  unfold R.v54815, N.v54815.
  rewrite ?node_54811.
  rewrite ?node_54814.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54816 (s : N.State) (i : N.Inputs) :
  R.v54816 (state s) (inputs i) = Zmod.unsigned (N.v54816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54816 s i)) at 1.
  unfold R.v54816, N.v54816.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54817 (s : N.State) (i : N.Inputs) :
  R.v54817 (state s) (inputs i) = Zmod.unsigned (N.v54817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54817 s i)) at 1.
  unfold R.v54817, N.v54817.
  rewrite ?node_7158.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54818 (s : N.State) (i : N.Inputs) :
  R.v54818 (state s) (inputs i) = Zmod.unsigned (N.v54818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54818 s i)) at 1.
  unfold R.v54818, N.v54818.
  unfold R.v6, N.v6.
  rewrite ?node_7154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54819 (s : N.State) (i : N.Inputs) :
  R.v54819 (state s) (inputs i) = Zmod.unsigned (N.v54819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54819 s i)) at 1.
  unfold R.v54819, N.v54819.
  unfold R.v6, N.v6.
  rewrite ?node_7153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54820 (s : N.State) (i : N.Inputs) :
  R.v54820 (state s) (inputs i) = Zmod.unsigned (N.v54820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54820 s i)) at 1.
  unfold R.v54820, N.v54820.
  rewrite ?node_54818.
  rewrite ?node_54819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54821 (s : N.State) (i : N.Inputs) :
  R.v54821 (state s) (inputs i) = Zmod.unsigned (N.v54821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54821 s i)) at 1.
  unfold R.v54821, N.v54821.
  unfold R.v16484, N.v16484.
  rewrite ?node_54820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54822 (s : N.State) (i : N.Inputs) :
  R.v54822 (state s) (inputs i) = Zmod.unsigned (N.v54822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54822 s i)) at 1.
  unfold R.v54822, N.v54822.
  rewrite ?node_54817.
  rewrite ?node_54821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54823 (s : N.State) (i : N.Inputs) :
  R.v54823 (state s) (inputs i) = Zmod.unsigned (N.v54823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54823 s i)) at 1.
  unfold R.v54823, N.v54823.
  unfold R.v6, N.v6.
  rewrite ?node_54822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54824 (s : N.State) (i : N.Inputs) :
  R.v54824 (state s) (inputs i) = Zmod.unsigned (N.v54824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54824 s i)) at 1.
  unfold R.v54824, N.v54824.
  rewrite ?node_7159.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54825 (s : N.State) (i : N.Inputs) :
  R.v54825 (state s) (inputs i) = Zmod.unsigned (N.v54825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54825 s i)) at 1.
  unfold R.v54825, N.v54825.
  unfold R.v6, N.v6.
  rewrite ?node_7264.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54826 (s : N.State) (i : N.Inputs) :
  R.v54826 (state s) (inputs i) = Zmod.unsigned (N.v54826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54826 s i)) at 1.
  unfold R.v54826, N.v54826.
  rewrite ?node_54824.
  rewrite ?node_54825.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54827 (s : N.State) (i : N.Inputs) :
  R.v54827 (state s) (inputs i) = Zmod.unsigned (N.v54827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54827 s i)) at 1.
  unfold R.v54827, N.v54827.
  rewrite ?node_54823.
  rewrite ?node_54826.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54828 (s : N.State) (i : N.Inputs) :
  R.v54828 (state s) (inputs i) = Zmod.unsigned (N.v54828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54828 s i)) at 1.
  unfold R.v54828, N.v54828.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54829 (s : N.State) (i : N.Inputs) :
  R.v54829 (state s) (inputs i) = Zmod.unsigned (N.v54829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54829 s i)) at 1.
  unfold R.v54829, N.v54829.
  rewrite ?node_7260.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54830 (s : N.State) (i : N.Inputs) :
  R.v54830 (state s) (inputs i) = Zmod.unsigned (N.v54830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54830 s i)) at 1.
  unfold R.v54830, N.v54830.
  rewrite ?node_7256.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54831 (s : N.State) (i : N.Inputs) :
  R.v54831 (state s) (inputs i) = Zmod.unsigned (N.v54831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54831 s i)) at 1.
  unfold R.v54831, N.v54831.
  rewrite ?node_7254.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54832 (s : N.State) (i : N.Inputs) :
  R.v54832 (state s) (inputs i) = Zmod.unsigned (N.v54832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54832 s i)) at 1.
  unfold R.v54832, N.v54832.
  unfold R.v6, N.v6.
  rewrite ?node_7250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54833 (s : N.State) (i : N.Inputs) :
  R.v54833 (state s) (inputs i) = Zmod.unsigned (N.v54833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54833 s i)) at 1.
  unfold R.v54833, N.v54833.
  unfold R.v6, N.v6.
  rewrite ?node_7243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54834 (s : N.State) (i : N.Inputs) :
  R.v54834 (state s) (inputs i) = Zmod.unsigned (N.v54834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54834 s i)) at 1.
  unfold R.v54834, N.v54834.
  rewrite ?node_54832.
  rewrite ?node_54833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54835 (s : N.State) (i : N.Inputs) :
  R.v54835 (state s) (inputs i) = Zmod.unsigned (N.v54835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54835 s i)) at 1.
  unfold R.v54835, N.v54835.
  unfold R.v16484, N.v16484.
  rewrite ?node_54834.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54836 (s : N.State) (i : N.Inputs) :
  R.v54836 (state s) (inputs i) = Zmod.unsigned (N.v54836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54836 s i)) at 1.
  unfold R.v54836, N.v54836.
  rewrite ?node_54829.
  rewrite ?node_54830.
  rewrite ?node_54831.
  rewrite ?node_54835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54837 (s : N.State) (i : N.Inputs) :
  R.v54837 (state s) (inputs i) = Zmod.unsigned (N.v54837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54837 s i)) at 1.
  unfold R.v54837, N.v54837.
  unfold R.v6, N.v6.
  rewrite ?node_54836.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54838 (s : N.State) (i : N.Inputs) :
  R.v54838 (state s) (inputs i) = Zmod.unsigned (N.v54838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54838 s i)) at 1.
  unfold R.v54838, N.v54838.
  rewrite ?node_7261.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54839 (s : N.State) (i : N.Inputs) :
  R.v54839 (state s) (inputs i) = Zmod.unsigned (N.v54839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54839 s i)) at 1.
  unfold R.v54839, N.v54839.
  unfold R.v6, N.v6.
  rewrite ?node_7364.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54840 (s : N.State) (i : N.Inputs) :
  R.v54840 (state s) (inputs i) = Zmod.unsigned (N.v54840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54840 s i)) at 1.
  unfold R.v54840, N.v54840.
  unfold R.v6, N.v6.
  rewrite ?node_7368.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54841 (s : N.State) (i : N.Inputs) :
  R.v54841 (state s) (inputs i) = Zmod.unsigned (N.v54841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54841 s i)) at 1.
  unfold R.v54841, N.v54841.
  rewrite ?node_54838.
  rewrite ?node_54839.
  rewrite ?node_54840.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54842 (s : N.State) (i : N.Inputs) :
  R.v54842 (state s) (inputs i) = Zmod.unsigned (N.v54842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54842 s i)) at 1.
  unfold R.v54842, N.v54842.
  rewrite ?node_54837.
  rewrite ?node_54841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54843 (s : N.State) (i : N.Inputs) :
  R.v54843 (state s) (inputs i) = Zmod.unsigned (N.v54843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54843 s i)) at 1.
  unfold R.v54843, N.v54843.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54844 (s : N.State) (i : N.Inputs) :
  R.v54844 (state s) (inputs i) = Zmod.unsigned (N.v54844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54844 s i)) at 1.
  unfold R.v54844, N.v54844.
  rewrite ?node_7254.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54845 (s : N.State) (i : N.Inputs) :
  R.v54845 (state s) (inputs i) = Zmod.unsigned (N.v54845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54845 s i)) at 1.
  unfold R.v54845, N.v54845.
  unfold R.v6, N.v6.
  rewrite ?node_7250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54846 (s : N.State) (i : N.Inputs) :
  R.v54846 (state s) (inputs i) = Zmod.unsigned (N.v54846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54846 s i)) at 1.
  unfold R.v54846, N.v54846.
  unfold R.v6, N.v6.
  rewrite ?node_7243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54847 (s : N.State) (i : N.Inputs) :
  R.v54847 (state s) (inputs i) = Zmod.unsigned (N.v54847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54847 s i)) at 1.
  unfold R.v54847, N.v54847.
  rewrite ?node_54845.
  rewrite ?node_54846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54848 (s : N.State) (i : N.Inputs) :
  R.v54848 (state s) (inputs i) = Zmod.unsigned (N.v54848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54848 s i)) at 1.
  unfold R.v54848, N.v54848.
  unfold R.v16484, N.v16484.
  rewrite ?node_54847.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54849 (s : N.State) (i : N.Inputs) :
  R.v54849 (state s) (inputs i) = Zmod.unsigned (N.v54849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54849 s i)) at 1.
  unfold R.v54849, N.v54849.
  rewrite ?node_54844.
  rewrite ?node_54848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54850 (s : N.State) (i : N.Inputs) :
  R.v54850 (state s) (inputs i) = Zmod.unsigned (N.v54850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54850 s i)) at 1.
  unfold R.v54850, N.v54850.
  unfold R.v6, N.v6.
  rewrite ?node_54849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54851 (s : N.State) (i : N.Inputs) :
  R.v54851 (state s) (inputs i) = Zmod.unsigned (N.v54851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54851 s i)) at 1.
  unfold R.v54851, N.v54851.
  rewrite ?node_7255.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54852 (s : N.State) (i : N.Inputs) :
  R.v54852 (state s) (inputs i) = Zmod.unsigned (N.v54852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54852 s i)) at 1.
  unfold R.v54852, N.v54852.
  unfold R.v6, N.v6.
  rewrite ?node_7364.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54853 (s : N.State) (i : N.Inputs) :
  R.v54853 (state s) (inputs i) = Zmod.unsigned (N.v54853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54853 s i)) at 1.
  unfold R.v54853, N.v54853.
  rewrite ?node_54851.
  rewrite ?node_54852.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54854 (s : N.State) (i : N.Inputs) :
  R.v54854 (state s) (inputs i) = Zmod.unsigned (N.v54854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54854 s i)) at 1.
  unfold R.v54854, N.v54854.
  rewrite ?node_54850.
  rewrite ?node_54853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54855 (s : N.State) (i : N.Inputs) :
  R.v54855 (state s) (inputs i) = Zmod.unsigned (N.v54855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54855 s i)) at 1.
  unfold R.v54855, N.v54855.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54856 (s : N.State) (i : N.Inputs) :
  R.v54856 (state s) (inputs i) = Zmod.unsigned (N.v54856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54856 s i)) at 1.
  unfold R.v54856, N.v54856.
  rewrite ?node_7260.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54857 (s : N.State) (i : N.Inputs) :
  R.v54857 (state s) (inputs i) = Zmod.unsigned (N.v54857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54857 s i)) at 1.
  unfold R.v54857, N.v54857.
  unfold R.v6, N.v6.
  rewrite ?node_7256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54858 (s : N.State) (i : N.Inputs) :
  R.v54858 (state s) (inputs i) = Zmod.unsigned (N.v54858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54858 s i)) at 1.
  unfold R.v54858, N.v54858.
  unfold R.v6, N.v6.
  rewrite ?node_7255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54859 (s : N.State) (i : N.Inputs) :
  R.v54859 (state s) (inputs i) = Zmod.unsigned (N.v54859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54859 s i)) at 1.
  unfold R.v54859, N.v54859.
  rewrite ?node_54857.
  rewrite ?node_54858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54860 (s : N.State) (i : N.Inputs) :
  R.v54860 (state s) (inputs i) = Zmod.unsigned (N.v54860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54860 s i)) at 1.
  unfold R.v54860, N.v54860.
  unfold R.v16484, N.v16484.
  rewrite ?node_54859.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54861 (s : N.State) (i : N.Inputs) :
  R.v54861 (state s) (inputs i) = Zmod.unsigned (N.v54861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54861 s i)) at 1.
  unfold R.v54861, N.v54861.
  rewrite ?node_54856.
  rewrite ?node_54860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54862 (s : N.State) (i : N.Inputs) :
  R.v54862 (state s) (inputs i) = Zmod.unsigned (N.v54862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54862 s i)) at 1.
  unfold R.v54862, N.v54862.
  unfold R.v6, N.v6.
  rewrite ?node_54861.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54863 (s : N.State) (i : N.Inputs) :
  R.v54863 (state s) (inputs i) = Zmod.unsigned (N.v54863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54863 s i)) at 1.
  unfold R.v54863, N.v54863.
  rewrite ?node_7261.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54864 (s : N.State) (i : N.Inputs) :
  R.v54864 (state s) (inputs i) = Zmod.unsigned (N.v54864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54864 s i)) at 1.
  unfold R.v54864, N.v54864.
  unfold R.v6, N.v6.
  rewrite ?node_7368.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54865 (s : N.State) (i : N.Inputs) :
  R.v54865 (state s) (inputs i) = Zmod.unsigned (N.v54865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54865 s i)) at 1.
  unfold R.v54865, N.v54865.
  rewrite ?node_54863.
  rewrite ?node_54864.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54866 (s : N.State) (i : N.Inputs) :
  R.v54866 (state s) (inputs i) = Zmod.unsigned (N.v54866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54866 s i)) at 1.
  unfold R.v54866, N.v54866.
  rewrite ?node_54862.
  rewrite ?node_54865.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54867 (s : N.State) (i : N.Inputs) :
  R.v54867 (state s) (inputs i) = Zmod.unsigned (N.v54867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54867 s i)) at 1.
  unfold R.v54867, N.v54867.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54868 (s : N.State) (i : N.Inputs) :
  R.v54868 (state s) (inputs i) = Zmod.unsigned (N.v54868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54868 s i)) at 1.
  unfold R.v54868, N.v54868.
  rewrite ?node_7364.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54869 (s : N.State) (i : N.Inputs) :
  R.v54869 (state s) (inputs i) = Zmod.unsigned (N.v54869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54869 s i)) at 1.
  unfold R.v54869, N.v54869.
  rewrite ?node_7360.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54870 (s : N.State) (i : N.Inputs) :
  R.v54870 (state s) (inputs i) = Zmod.unsigned (N.v54870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54870 s i)) at 1.
  unfold R.v54870, N.v54870.
  rewrite ?node_7358.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54871 (s : N.State) (i : N.Inputs) :
  R.v54871 (state s) (inputs i) = Zmod.unsigned (N.v54871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54871 s i)) at 1.
  unfold R.v54871, N.v54871.
  unfold R.v6, N.v6.
  rewrite ?node_7354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54872 (s : N.State) (i : N.Inputs) :
  R.v54872 (state s) (inputs i) = Zmod.unsigned (N.v54872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54872 s i)) at 1.
  unfold R.v54872, N.v54872.
  unfold R.v6, N.v6.
  rewrite ?node_7347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54873 (s : N.State) (i : N.Inputs) :
  R.v54873 (state s) (inputs i) = Zmod.unsigned (N.v54873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54873 s i)) at 1.
  unfold R.v54873, N.v54873.
  rewrite ?node_54871.
  rewrite ?node_54872.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54874 (s : N.State) (i : N.Inputs) :
  R.v54874 (state s) (inputs i) = Zmod.unsigned (N.v54874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54874 s i)) at 1.
  unfold R.v54874, N.v54874.
  unfold R.v16484, N.v16484.
  rewrite ?node_54873.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54875 (s : N.State) (i : N.Inputs) :
  R.v54875 (state s) (inputs i) = Zmod.unsigned (N.v54875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54875 s i)) at 1.
  unfold R.v54875, N.v54875.
  rewrite ?node_54868.
  rewrite ?node_54869.
  rewrite ?node_54870.
  rewrite ?node_54874.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54876 (s : N.State) (i : N.Inputs) :
  R.v54876 (state s) (inputs i) = Zmod.unsigned (N.v54876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54876 s i)) at 1.
  unfold R.v54876, N.v54876.
  unfold R.v6, N.v6.
  rewrite ?node_54875.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54877 (s : N.State) (i : N.Inputs) :
  R.v54877 (state s) (inputs i) = Zmod.unsigned (N.v54877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54877 s i)) at 1.
  unfold R.v54877, N.v54877.
  rewrite ?node_7365.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54878 (s : N.State) (i : N.Inputs) :
  R.v54878 (state s) (inputs i) = Zmod.unsigned (N.v54878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54878 s i)) at 1.
  unfold R.v54878, N.v54878.
  unfold R.v6, N.v6.
  rewrite ?node_7471.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54879 (s : N.State) (i : N.Inputs) :
  R.v54879 (state s) (inputs i) = Zmod.unsigned (N.v54879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54879 s i)) at 1.
  unfold R.v54879, N.v54879.
  unfold R.v6, N.v6.
  rewrite ?node_7475.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54880 (s : N.State) (i : N.Inputs) :
  R.v54880 (state s) (inputs i) = Zmod.unsigned (N.v54880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54880 s i)) at 1.
  unfold R.v54880, N.v54880.
  rewrite ?node_54877.
  rewrite ?node_54878.
  rewrite ?node_54879.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54881 (s : N.State) (i : N.Inputs) :
  R.v54881 (state s) (inputs i) = Zmod.unsigned (N.v54881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54881 s i)) at 1.
  unfold R.v54881, N.v54881.
  rewrite ?node_54876.
  rewrite ?node_54880.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54882 (s : N.State) (i : N.Inputs) :
  R.v54882 (state s) (inputs i) = Zmod.unsigned (N.v54882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54882 s i)) at 1.
  unfold R.v54882, N.v54882.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54883 (s : N.State) (i : N.Inputs) :
  R.v54883 (state s) (inputs i) = Zmod.unsigned (N.v54883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54883 s i)) at 1.
  unfold R.v54883, N.v54883.
  rewrite ?node_7358.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54884 (s : N.State) (i : N.Inputs) :
  R.v54884 (state s) (inputs i) = Zmod.unsigned (N.v54884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54884 s i)) at 1.
  unfold R.v54884, N.v54884.
  unfold R.v6, N.v6.
  rewrite ?node_7354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54885 (s : N.State) (i : N.Inputs) :
  R.v54885 (state s) (inputs i) = Zmod.unsigned (N.v54885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54885 s i)) at 1.
  unfold R.v54885, N.v54885.
  unfold R.v6, N.v6.
  rewrite ?node_7347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54886 (s : N.State) (i : N.Inputs) :
  R.v54886 (state s) (inputs i) = Zmod.unsigned (N.v54886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54886 s i)) at 1.
  unfold R.v54886, N.v54886.
  rewrite ?node_54884.
  rewrite ?node_54885.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54887 (s : N.State) (i : N.Inputs) :
  R.v54887 (state s) (inputs i) = Zmod.unsigned (N.v54887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54887 s i)) at 1.
  unfold R.v54887, N.v54887.
  unfold R.v16484, N.v16484.
  rewrite ?node_54886.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54888 (s : N.State) (i : N.Inputs) :
  R.v54888 (state s) (inputs i) = Zmod.unsigned (N.v54888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54888 s i)) at 1.
  unfold R.v54888, N.v54888.
  rewrite ?node_54883.
  rewrite ?node_54887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54889 (s : N.State) (i : N.Inputs) :
  R.v54889 (state s) (inputs i) = Zmod.unsigned (N.v54889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54889 s i)) at 1.
  unfold R.v54889, N.v54889.
  unfold R.v6, N.v6.
  rewrite ?node_54888.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54890 (s : N.State) (i : N.Inputs) :
  R.v54890 (state s) (inputs i) = Zmod.unsigned (N.v54890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54890 s i)) at 1.
  unfold R.v54890, N.v54890.
  rewrite ?node_7359.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54891 (s : N.State) (i : N.Inputs) :
  R.v54891 (state s) (inputs i) = Zmod.unsigned (N.v54891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54891 s i)) at 1.
  unfold R.v54891, N.v54891.
  unfold R.v6, N.v6.
  rewrite ?node_7471.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54892 (s : N.State) (i : N.Inputs) :
  R.v54892 (state s) (inputs i) = Zmod.unsigned (N.v54892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54892 s i)) at 1.
  unfold R.v54892, N.v54892.
  rewrite ?node_54890.
  rewrite ?node_54891.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54893 (s : N.State) (i : N.Inputs) :
  R.v54893 (state s) (inputs i) = Zmod.unsigned (N.v54893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54893 s i)) at 1.
  unfold R.v54893, N.v54893.
  rewrite ?node_54889.
  rewrite ?node_54892.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54894 (s : N.State) (i : N.Inputs) :
  R.v54894 (state s) (inputs i) = Zmod.unsigned (N.v54894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54894 s i)) at 1.
  unfold R.v54894, N.v54894.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54895 (s : N.State) (i : N.Inputs) :
  R.v54895 (state s) (inputs i) = Zmod.unsigned (N.v54895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54895 s i)) at 1.
  unfold R.v54895, N.v54895.
  rewrite ?node_7364.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54896 (s : N.State) (i : N.Inputs) :
  R.v54896 (state s) (inputs i) = Zmod.unsigned (N.v54896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54896 s i)) at 1.
  unfold R.v54896, N.v54896.
  unfold R.v6, N.v6.
  rewrite ?node_7360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54897 (s : N.State) (i : N.Inputs) :
  R.v54897 (state s) (inputs i) = Zmod.unsigned (N.v54897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54897 s i)) at 1.
  unfold R.v54897, N.v54897.
  unfold R.v6, N.v6.
  rewrite ?node_7359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54898 (s : N.State) (i : N.Inputs) :
  R.v54898 (state s) (inputs i) = Zmod.unsigned (N.v54898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54898 s i)) at 1.
  unfold R.v54898, N.v54898.
  rewrite ?node_54896.
  rewrite ?node_54897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54899 (s : N.State) (i : N.Inputs) :
  R.v54899 (state s) (inputs i) = Zmod.unsigned (N.v54899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54899 s i)) at 1.
  unfold R.v54899, N.v54899.
  unfold R.v16484, N.v16484.
  rewrite ?node_54898.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54900 (s : N.State) (i : N.Inputs) :
  R.v54900 (state s) (inputs i) = Zmod.unsigned (N.v54900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54900 s i)) at 1.
  unfold R.v54900, N.v54900.
  rewrite ?node_54895.
  rewrite ?node_54899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54901 (s : N.State) (i : N.Inputs) :
  R.v54901 (state s) (inputs i) = Zmod.unsigned (N.v54901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54901 s i)) at 1.
  unfold R.v54901, N.v54901.
  unfold R.v6, N.v6.
  rewrite ?node_54900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54902 (s : N.State) (i : N.Inputs) :
  R.v54902 (state s) (inputs i) = Zmod.unsigned (N.v54902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54902 s i)) at 1.
  unfold R.v54902, N.v54902.
  rewrite ?node_7365.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54903 (s : N.State) (i : N.Inputs) :
  R.v54903 (state s) (inputs i) = Zmod.unsigned (N.v54903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54903 s i)) at 1.
  unfold R.v54903, N.v54903.
  unfold R.v6, N.v6.
  rewrite ?node_7475.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54904 (s : N.State) (i : N.Inputs) :
  R.v54904 (state s) (inputs i) = Zmod.unsigned (N.v54904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54904 s i)) at 1.
  unfold R.v54904, N.v54904.
  rewrite ?node_54902.
  rewrite ?node_54903.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54905 (s : N.State) (i : N.Inputs) :
  R.v54905 (state s) (inputs i) = Zmod.unsigned (N.v54905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54905 s i)) at 1.
  unfold R.v54905, N.v54905.
  rewrite ?node_54901.
  rewrite ?node_54904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54906 (s : N.State) (i : N.Inputs) :
  R.v54906 (state s) (inputs i) = Zmod.unsigned (N.v54906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54906 s i)) at 1.
  unfold R.v54906, N.v54906.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54907 (s : N.State) (i : N.Inputs) :
  R.v54907 (state s) (inputs i) = Zmod.unsigned (N.v54907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54907 s i)) at 1.
  unfold R.v54907, N.v54907.
  rewrite ?node_7471.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54908 (s : N.State) (i : N.Inputs) :
  R.v54908 (state s) (inputs i) = Zmod.unsigned (N.v54908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54908 s i)) at 1.
  unfold R.v54908, N.v54908.
  rewrite ?node_7467.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54909 (s : N.State) (i : N.Inputs) :
  R.v54909 (state s) (inputs i) = Zmod.unsigned (N.v54909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54909 s i)) at 1.
  unfold R.v54909, N.v54909.
  rewrite ?node_7465.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54910 (s : N.State) (i : N.Inputs) :
  R.v54910 (state s) (inputs i) = Zmod.unsigned (N.v54910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54910 s i)) at 1.
  unfold R.v54910, N.v54910.
  unfold R.v6, N.v6.
  rewrite ?node_7461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54911 (s : N.State) (i : N.Inputs) :
  R.v54911 (state s) (inputs i) = Zmod.unsigned (N.v54911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54911 s i)) at 1.
  unfold R.v54911, N.v54911.
  unfold R.v6, N.v6.
  rewrite ?node_7456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54912 (s : N.State) (i : N.Inputs) :
  R.v54912 (state s) (inputs i) = Zmod.unsigned (N.v54912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54912 s i)) at 1.
  unfold R.v54912, N.v54912.
  rewrite ?node_54910.
  rewrite ?node_54911.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54913 (s : N.State) (i : N.Inputs) :
  R.v54913 (state s) (inputs i) = Zmod.unsigned (N.v54913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54913 s i)) at 1.
  unfold R.v54913, N.v54913.
  unfold R.v16484, N.v16484.
  rewrite ?node_54912.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54914 (s : N.State) (i : N.Inputs) :
  R.v54914 (state s) (inputs i) = Zmod.unsigned (N.v54914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54914 s i)) at 1.
  unfold R.v54914, N.v54914.
  rewrite ?node_54907.
  rewrite ?node_54908.
  rewrite ?node_54909.
  rewrite ?node_54913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54915 (s : N.State) (i : N.Inputs) :
  R.v54915 (state s) (inputs i) = Zmod.unsigned (N.v54915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54915 s i)) at 1.
  unfold R.v54915, N.v54915.
  unfold R.v6, N.v6.
  rewrite ?node_54914.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54916 (s : N.State) (i : N.Inputs) :
  R.v54916 (state s) (inputs i) = Zmod.unsigned (N.v54916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54916 s i)) at 1.
  unfold R.v54916, N.v54916.
  rewrite ?node_7472.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54917 (s : N.State) (i : N.Inputs) :
  R.v54917 (state s) (inputs i) = Zmod.unsigned (N.v54917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54917 s i)) at 1.
  unfold R.v54917, N.v54917.
  unfold R.v6, N.v6.
  rewrite ?node_7582.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54918 (s : N.State) (i : N.Inputs) :
  R.v54918 (state s) (inputs i) = Zmod.unsigned (N.v54918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54918 s i)) at 1.
  unfold R.v54918, N.v54918.
  unfold R.v6, N.v6.
  rewrite ?node_7586.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54919 (s : N.State) (i : N.Inputs) :
  R.v54919 (state s) (inputs i) = Zmod.unsigned (N.v54919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54919 s i)) at 1.
  unfold R.v54919, N.v54919.
  rewrite ?node_54916.
  rewrite ?node_54917.
  rewrite ?node_54918.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54920 (s : N.State) (i : N.Inputs) :
  R.v54920 (state s) (inputs i) = Zmod.unsigned (N.v54920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54920 s i)) at 1.
  unfold R.v54920, N.v54920.
  rewrite ?node_54915.
  rewrite ?node_54919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54921 (s : N.State) (i : N.Inputs) :
  R.v54921 (state s) (inputs i) = Zmod.unsigned (N.v54921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54921 s i)) at 1.
  unfold R.v54921, N.v54921.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54922 (s : N.State) (i : N.Inputs) :
  R.v54922 (state s) (inputs i) = Zmod.unsigned (N.v54922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54922 s i)) at 1.
  unfold R.v54922, N.v54922.
  rewrite ?node_7465.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54923 (s : N.State) (i : N.Inputs) :
  R.v54923 (state s) (inputs i) = Zmod.unsigned (N.v54923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54923 s i)) at 1.
  unfold R.v54923, N.v54923.
  unfold R.v6, N.v6.
  rewrite ?node_7461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54924 (s : N.State) (i : N.Inputs) :
  R.v54924 (state s) (inputs i) = Zmod.unsigned (N.v54924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54924 s i)) at 1.
  unfold R.v54924, N.v54924.
  unfold R.v6, N.v6.
  rewrite ?node_7456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54925 (s : N.State) (i : N.Inputs) :
  R.v54925 (state s) (inputs i) = Zmod.unsigned (N.v54925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54925 s i)) at 1.
  unfold R.v54925, N.v54925.
  rewrite ?node_54923.
  rewrite ?node_54924.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54926 (s : N.State) (i : N.Inputs) :
  R.v54926 (state s) (inputs i) = Zmod.unsigned (N.v54926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54926 s i)) at 1.
  unfold R.v54926, N.v54926.
  unfold R.v16484, N.v16484.
  rewrite ?node_54925.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54927 (s : N.State) (i : N.Inputs) :
  R.v54927 (state s) (inputs i) = Zmod.unsigned (N.v54927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54927 s i)) at 1.
  unfold R.v54927, N.v54927.
  rewrite ?node_54922.
  rewrite ?node_54926.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54928 (s : N.State) (i : N.Inputs) :
  R.v54928 (state s) (inputs i) = Zmod.unsigned (N.v54928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54928 s i)) at 1.
  unfold R.v54928, N.v54928.
  unfold R.v6, N.v6.
  rewrite ?node_54927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54929 (s : N.State) (i : N.Inputs) :
  R.v54929 (state s) (inputs i) = Zmod.unsigned (N.v54929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54929 s i)) at 1.
  unfold R.v54929, N.v54929.
  rewrite ?node_7466.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54930 (s : N.State) (i : N.Inputs) :
  R.v54930 (state s) (inputs i) = Zmod.unsigned (N.v54930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54930 s i)) at 1.
  unfold R.v54930, N.v54930.
  unfold R.v6, N.v6.
  rewrite ?node_7582.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54931 (s : N.State) (i : N.Inputs) :
  R.v54931 (state s) (inputs i) = Zmod.unsigned (N.v54931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54931 s i)) at 1.
  unfold R.v54931, N.v54931.
  rewrite ?node_54929.
  rewrite ?node_54930.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54932 (s : N.State) (i : N.Inputs) :
  R.v54932 (state s) (inputs i) = Zmod.unsigned (N.v54932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54932 s i)) at 1.
  unfold R.v54932, N.v54932.
  rewrite ?node_54928.
  rewrite ?node_54931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54933 (s : N.State) (i : N.Inputs) :
  R.v54933 (state s) (inputs i) = Zmod.unsigned (N.v54933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54933 s i)) at 1.
  unfold R.v54933, N.v54933.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54934 (s : N.State) (i : N.Inputs) :
  R.v54934 (state s) (inputs i) = Zmod.unsigned (N.v54934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54934 s i)) at 1.
  unfold R.v54934, N.v54934.
  rewrite ?node_7471.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54935 (s : N.State) (i : N.Inputs) :
  R.v54935 (state s) (inputs i) = Zmod.unsigned (N.v54935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54935 s i)) at 1.
  unfold R.v54935, N.v54935.
  unfold R.v6, N.v6.
  rewrite ?node_7467.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54936 (s : N.State) (i : N.Inputs) :
  R.v54936 (state s) (inputs i) = Zmod.unsigned (N.v54936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54936 s i)) at 1.
  unfold R.v54936, N.v54936.
  unfold R.v6, N.v6.
  rewrite ?node_7466.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54937 (s : N.State) (i : N.Inputs) :
  R.v54937 (state s) (inputs i) = Zmod.unsigned (N.v54937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54937 s i)) at 1.
  unfold R.v54937, N.v54937.
  rewrite ?node_54935.
  rewrite ?node_54936.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54938 (s : N.State) (i : N.Inputs) :
  R.v54938 (state s) (inputs i) = Zmod.unsigned (N.v54938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54938 s i)) at 1.
  unfold R.v54938, N.v54938.
  unfold R.v16484, N.v16484.
  rewrite ?node_54937.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54939 (s : N.State) (i : N.Inputs) :
  R.v54939 (state s) (inputs i) = Zmod.unsigned (N.v54939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54939 s i)) at 1.
  unfold R.v54939, N.v54939.
  rewrite ?node_54934.
  rewrite ?node_54938.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54940 (s : N.State) (i : N.Inputs) :
  R.v54940 (state s) (inputs i) = Zmod.unsigned (N.v54940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54940 s i)) at 1.
  unfold R.v54940, N.v54940.
  unfold R.v6, N.v6.
  rewrite ?node_54939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54941 (s : N.State) (i : N.Inputs) :
  R.v54941 (state s) (inputs i) = Zmod.unsigned (N.v54941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54941 s i)) at 1.
  unfold R.v54941, N.v54941.
  rewrite ?node_7472.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54942 (s : N.State) (i : N.Inputs) :
  R.v54942 (state s) (inputs i) = Zmod.unsigned (N.v54942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54942 s i)) at 1.
  unfold R.v54942, N.v54942.
  unfold R.v6, N.v6.
  rewrite ?node_7586.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54943 (s : N.State) (i : N.Inputs) :
  R.v54943 (state s) (inputs i) = Zmod.unsigned (N.v54943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54943 s i)) at 1.
  unfold R.v54943, N.v54943.
  rewrite ?node_54941.
  rewrite ?node_54942.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54944 (s : N.State) (i : N.Inputs) :
  R.v54944 (state s) (inputs i) = Zmod.unsigned (N.v54944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54944 s i)) at 1.
  unfold R.v54944, N.v54944.
  rewrite ?node_54940.
  rewrite ?node_54943.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54945 (s : N.State) (i : N.Inputs) :
  R.v54945 (state s) (inputs i) = Zmod.unsigned (N.v54945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54945 s i)) at 1.
  unfold R.v54945, N.v54945.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54946 (s : N.State) (i : N.Inputs) :
  R.v54946 (state s) (inputs i) = Zmod.unsigned (N.v54946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54946 s i)) at 1.
  unfold R.v54946, N.v54946.
  rewrite ?node_7582.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54947 (s : N.State) (i : N.Inputs) :
  R.v54947 (state s) (inputs i) = Zmod.unsigned (N.v54947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54947 s i)) at 1.
  unfold R.v54947, N.v54947.
  rewrite ?node_7578.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54948 (s : N.State) (i : N.Inputs) :
  R.v54948 (state s) (inputs i) = Zmod.unsigned (N.v54948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54948 s i)) at 1.
  unfold R.v54948, N.v54948.
  rewrite ?node_7576.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54949 (s : N.State) (i : N.Inputs) :
  R.v54949 (state s) (inputs i) = Zmod.unsigned (N.v54949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54949 s i)) at 1.
  unfold R.v54949, N.v54949.
  unfold R.v6, N.v6.
  rewrite ?node_7572.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54950 (s : N.State) (i : N.Inputs) :
  R.v54950 (state s) (inputs i) = Zmod.unsigned (N.v54950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54950 s i)) at 1.
  unfold R.v54950, N.v54950.
  unfold R.v6, N.v6.
  rewrite ?node_7565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54951 (s : N.State) (i : N.Inputs) :
  R.v54951 (state s) (inputs i) = Zmod.unsigned (N.v54951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54951 s i)) at 1.
  unfold R.v54951, N.v54951.
  rewrite ?node_54949.
  rewrite ?node_54950.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54952 (s : N.State) (i : N.Inputs) :
  R.v54952 (state s) (inputs i) = Zmod.unsigned (N.v54952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54952 s i)) at 1.
  unfold R.v54952, N.v54952.
  unfold R.v16484, N.v16484.
  rewrite ?node_54951.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54953 (s : N.State) (i : N.Inputs) :
  R.v54953 (state s) (inputs i) = Zmod.unsigned (N.v54953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54953 s i)) at 1.
  unfold R.v54953, N.v54953.
  rewrite ?node_54946.
  rewrite ?node_54947.
  rewrite ?node_54948.
  rewrite ?node_54952.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54954 (s : N.State) (i : N.Inputs) :
  R.v54954 (state s) (inputs i) = Zmod.unsigned (N.v54954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54954 s i)) at 1.
  unfold R.v54954, N.v54954.
  unfold R.v6, N.v6.
  rewrite ?node_54953.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54955 (s : N.State) (i : N.Inputs) :
  R.v54955 (state s) (inputs i) = Zmod.unsigned (N.v54955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54955 s i)) at 1.
  unfold R.v54955, N.v54955.
  rewrite ?node_7583.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54956 (s : N.State) (i : N.Inputs) :
  R.v54956 (state s) (inputs i) = Zmod.unsigned (N.v54956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54956 s i)) at 1.
  unfold R.v54956, N.v54956.
  unfold R.v6, N.v6.
  rewrite ?node_7694.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54957 (s : N.State) (i : N.Inputs) :
  R.v54957 (state s) (inputs i) = Zmod.unsigned (N.v54957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54957 s i)) at 1.
  unfold R.v54957, N.v54957.
  unfold R.v6, N.v6.
  rewrite ?node_7698.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54958 (s : N.State) (i : N.Inputs) :
  R.v54958 (state s) (inputs i) = Zmod.unsigned (N.v54958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54958 s i)) at 1.
  unfold R.v54958, N.v54958.
  rewrite ?node_54955.
  rewrite ?node_54956.
  rewrite ?node_54957.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54959 (s : N.State) (i : N.Inputs) :
  R.v54959 (state s) (inputs i) = Zmod.unsigned (N.v54959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54959 s i)) at 1.
  unfold R.v54959, N.v54959.
  rewrite ?node_54954.
  rewrite ?node_54958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54960 (s : N.State) (i : N.Inputs) :
  R.v54960 (state s) (inputs i) = Zmod.unsigned (N.v54960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54960 s i)) at 1.
  unfold R.v54960, N.v54960.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54961 (s : N.State) (i : N.Inputs) :
  R.v54961 (state s) (inputs i) = Zmod.unsigned (N.v54961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54961 s i)) at 1.
  unfold R.v54961, N.v54961.
  rewrite ?node_7576.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54962 (s : N.State) (i : N.Inputs) :
  R.v54962 (state s) (inputs i) = Zmod.unsigned (N.v54962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54962 s i)) at 1.
  unfold R.v54962, N.v54962.
  unfold R.v6, N.v6.
  rewrite ?node_7572.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54963 (s : N.State) (i : N.Inputs) :
  R.v54963 (state s) (inputs i) = Zmod.unsigned (N.v54963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54963 s i)) at 1.
  unfold R.v54963, N.v54963.
  unfold R.v6, N.v6.
  rewrite ?node_7565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54964 (s : N.State) (i : N.Inputs) :
  R.v54964 (state s) (inputs i) = Zmod.unsigned (N.v54964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54964 s i)) at 1.
  unfold R.v54964, N.v54964.
  rewrite ?node_54962.
  rewrite ?node_54963.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54965 (s : N.State) (i : N.Inputs) :
  R.v54965 (state s) (inputs i) = Zmod.unsigned (N.v54965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54965 s i)) at 1.
  unfold R.v54965, N.v54965.
  unfold R.v16484, N.v16484.
  rewrite ?node_54964.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54966 (s : N.State) (i : N.Inputs) :
  R.v54966 (state s) (inputs i) = Zmod.unsigned (N.v54966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54966 s i)) at 1.
  unfold R.v54966, N.v54966.
  rewrite ?node_54961.
  rewrite ?node_54965.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54967 (s : N.State) (i : N.Inputs) :
  R.v54967 (state s) (inputs i) = Zmod.unsigned (N.v54967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54967 s i)) at 1.
  unfold R.v54967, N.v54967.
  unfold R.v6, N.v6.
  rewrite ?node_54966.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54968 (s : N.State) (i : N.Inputs) :
  R.v54968 (state s) (inputs i) = Zmod.unsigned (N.v54968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54968 s i)) at 1.
  unfold R.v54968, N.v54968.
  rewrite ?node_7577.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54969 (s : N.State) (i : N.Inputs) :
  R.v54969 (state s) (inputs i) = Zmod.unsigned (N.v54969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54969 s i)) at 1.
  unfold R.v54969, N.v54969.
  unfold R.v6, N.v6.
  rewrite ?node_7694.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54970 (s : N.State) (i : N.Inputs) :
  R.v54970 (state s) (inputs i) = Zmod.unsigned (N.v54970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54970 s i)) at 1.
  unfold R.v54970, N.v54970.
  rewrite ?node_54968.
  rewrite ?node_54969.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54971 (s : N.State) (i : N.Inputs) :
  R.v54971 (state s) (inputs i) = Zmod.unsigned (N.v54971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54971 s i)) at 1.
  unfold R.v54971, N.v54971.
  rewrite ?node_54967.
  rewrite ?node_54970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54972 (s : N.State) (i : N.Inputs) :
  R.v54972 (state s) (inputs i) = Zmod.unsigned (N.v54972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54972 s i)) at 1.
  unfold R.v54972, N.v54972.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54973 (s : N.State) (i : N.Inputs) :
  R.v54973 (state s) (inputs i) = Zmod.unsigned (N.v54973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54973 s i)) at 1.
  unfold R.v54973, N.v54973.
  rewrite ?node_7582.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54974 (s : N.State) (i : N.Inputs) :
  R.v54974 (state s) (inputs i) = Zmod.unsigned (N.v54974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54974 s i)) at 1.
  unfold R.v54974, N.v54974.
  unfold R.v6, N.v6.
  rewrite ?node_7578.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54975 (s : N.State) (i : N.Inputs) :
  R.v54975 (state s) (inputs i) = Zmod.unsigned (N.v54975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54975 s i)) at 1.
  unfold R.v54975, N.v54975.
  unfold R.v6, N.v6.
  rewrite ?node_7577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54976 (s : N.State) (i : N.Inputs) :
  R.v54976 (state s) (inputs i) = Zmod.unsigned (N.v54976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54976 s i)) at 1.
  unfold R.v54976, N.v54976.
  rewrite ?node_54974.
  rewrite ?node_54975.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54977 (s : N.State) (i : N.Inputs) :
  R.v54977 (state s) (inputs i) = Zmod.unsigned (N.v54977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54977 s i)) at 1.
  unfold R.v54977, N.v54977.
  unfold R.v16484, N.v16484.
  rewrite ?node_54976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54978 (s : N.State) (i : N.Inputs) :
  R.v54978 (state s) (inputs i) = Zmod.unsigned (N.v54978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54978 s i)) at 1.
  unfold R.v54978, N.v54978.
  rewrite ?node_54973.
  rewrite ?node_54977.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54979 (s : N.State) (i : N.Inputs) :
  R.v54979 (state s) (inputs i) = Zmod.unsigned (N.v54979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54979 s i)) at 1.
  unfold R.v54979, N.v54979.
  unfold R.v6, N.v6.
  rewrite ?node_54978.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54980 (s : N.State) (i : N.Inputs) :
  R.v54980 (state s) (inputs i) = Zmod.unsigned (N.v54980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54980 s i)) at 1.
  unfold R.v54980, N.v54980.
  rewrite ?node_7583.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54981 (s : N.State) (i : N.Inputs) :
  R.v54981 (state s) (inputs i) = Zmod.unsigned (N.v54981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54981 s i)) at 1.
  unfold R.v54981, N.v54981.
  unfold R.v6, N.v6.
  rewrite ?node_7698.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54982 (s : N.State) (i : N.Inputs) :
  R.v54982 (state s) (inputs i) = Zmod.unsigned (N.v54982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54982 s i)) at 1.
  unfold R.v54982, N.v54982.
  rewrite ?node_54980.
  rewrite ?node_54981.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54983 (s : N.State) (i : N.Inputs) :
  R.v54983 (state s) (inputs i) = Zmod.unsigned (N.v54983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54983 s i)) at 1.
  unfold R.v54983, N.v54983.
  rewrite ?node_54979.
  rewrite ?node_54982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54984 (s : N.State) (i : N.Inputs) :
  R.v54984 (state s) (inputs i) = Zmod.unsigned (N.v54984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54984 s i)) at 1.
  unfold R.v54984, N.v54984.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54985 (s : N.State) (i : N.Inputs) :
  R.v54985 (state s) (inputs i) = Zmod.unsigned (N.v54985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54985 s i)) at 1.
  unfold R.v54985, N.v54985.
  rewrite ?node_7694.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54986 (s : N.State) (i : N.Inputs) :
  R.v54986 (state s) (inputs i) = Zmod.unsigned (N.v54986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54986 s i)) at 1.
  unfold R.v54986, N.v54986.
  rewrite ?node_7690.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54987 (s : N.State) (i : N.Inputs) :
  R.v54987 (state s) (inputs i) = Zmod.unsigned (N.v54987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54987 s i)) at 1.
  unfold R.v54987, N.v54987.
  rewrite ?node_7688.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54988 (s : N.State) (i : N.Inputs) :
  R.v54988 (state s) (inputs i) = Zmod.unsigned (N.v54988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54988 s i)) at 1.
  unfold R.v54988, N.v54988.
  unfold R.v6, N.v6.
  rewrite ?node_7684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54989 (s : N.State) (i : N.Inputs) :
  R.v54989 (state s) (inputs i) = Zmod.unsigned (N.v54989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54989 s i)) at 1.
  unfold R.v54989, N.v54989.
  unfold R.v6, N.v6.
  rewrite ?node_7677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54990 (s : N.State) (i : N.Inputs) :
  R.v54990 (state s) (inputs i) = Zmod.unsigned (N.v54990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54990 s i)) at 1.
  unfold R.v54990, N.v54990.
  rewrite ?node_54988.
  rewrite ?node_54989.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54991 (s : N.State) (i : N.Inputs) :
  R.v54991 (state s) (inputs i) = Zmod.unsigned (N.v54991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54991 s i)) at 1.
  unfold R.v54991, N.v54991.
  unfold R.v16484, N.v16484.
  rewrite ?node_54990.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54992 (s : N.State) (i : N.Inputs) :
  R.v54992 (state s) (inputs i) = Zmod.unsigned (N.v54992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54992 s i)) at 1.
  unfold R.v54992, N.v54992.
  rewrite ?node_54985.
  rewrite ?node_54986.
  rewrite ?node_54987.
  rewrite ?node_54991.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54993 (s : N.State) (i : N.Inputs) :
  R.v54993 (state s) (inputs i) = Zmod.unsigned (N.v54993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54993 s i)) at 1.
  unfold R.v54993, N.v54993.
  unfold R.v6, N.v6.
  rewrite ?node_54992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54994 (s : N.State) (i : N.Inputs) :
  R.v54994 (state s) (inputs i) = Zmod.unsigned (N.v54994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54994 s i)) at 1.
  unfold R.v54994, N.v54994.
  rewrite ?node_7695.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54995 (s : N.State) (i : N.Inputs) :
  R.v54995 (state s) (inputs i) = Zmod.unsigned (N.v54995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54995 s i)) at 1.
  unfold R.v54995, N.v54995.
  unfold R.v6, N.v6.
  rewrite ?node_7808.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54996 (s : N.State) (i : N.Inputs) :
  R.v54996 (state s) (inputs i) = Zmod.unsigned (N.v54996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54996 s i)) at 1.
  unfold R.v54996, N.v54996.
  unfold R.v6, N.v6.
  rewrite ?node_7812.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54997 (s : N.State) (i : N.Inputs) :
  R.v54997 (state s) (inputs i) = Zmod.unsigned (N.v54997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54997 s i)) at 1.
  unfold R.v54997, N.v54997.
  rewrite ?node_54994.
  rewrite ?node_54995.
  rewrite ?node_54996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54998 (s : N.State) (i : N.Inputs) :
  R.v54998 (state s) (inputs i) = Zmod.unsigned (N.v54998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54998 s i)) at 1.
  unfold R.v54998, N.v54998.
  rewrite ?node_54993.
  rewrite ?node_54997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54999 (s : N.State) (i : N.Inputs) :
  R.v54999 (state s) (inputs i) = Zmod.unsigned (N.v54999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54999 s i)) at 1.
  unfold R.v54999, N.v54999.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
