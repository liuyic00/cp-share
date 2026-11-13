(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes054.
Lemma node_55000 (s : N.State) (i : N.Inputs) :
  R.v55000 (state s) (inputs i) = Zmod.unsigned (N.v55000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55000 s i)) at 1.
  unfold R.v55000, N.v55000.
  rewrite ?node_7688.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55001 (s : N.State) (i : N.Inputs) :
  R.v55001 (state s) (inputs i) = Zmod.unsigned (N.v55001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55001 s i)) at 1.
  unfold R.v55001, N.v55001.
  unfold R.v6, N.v6.
  rewrite ?node_7684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55002 (s : N.State) (i : N.Inputs) :
  R.v55002 (state s) (inputs i) = Zmod.unsigned (N.v55002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55002 s i)) at 1.
  unfold R.v55002, N.v55002.
  unfold R.v6, N.v6.
  rewrite ?node_7677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55003 (s : N.State) (i : N.Inputs) :
  R.v55003 (state s) (inputs i) = Zmod.unsigned (N.v55003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55003 s i)) at 1.
  unfold R.v55003, N.v55003.
  rewrite ?node_55001.
  rewrite ?node_55002.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55004 (s : N.State) (i : N.Inputs) :
  R.v55004 (state s) (inputs i) = Zmod.unsigned (N.v55004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55004 s i)) at 1.
  unfold R.v55004, N.v55004.
  unfold R.v16484, N.v16484.
  rewrite ?node_55003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55005 (s : N.State) (i : N.Inputs) :
  R.v55005 (state s) (inputs i) = Zmod.unsigned (N.v55005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55005 s i)) at 1.
  unfold R.v55005, N.v55005.
  rewrite ?node_55000.
  rewrite ?node_55004.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55006 (s : N.State) (i : N.Inputs) :
  R.v55006 (state s) (inputs i) = Zmod.unsigned (N.v55006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55006 s i)) at 1.
  unfold R.v55006, N.v55006.
  unfold R.v6, N.v6.
  rewrite ?node_55005.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55007 (s : N.State) (i : N.Inputs) :
  R.v55007 (state s) (inputs i) = Zmod.unsigned (N.v55007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55007 s i)) at 1.
  unfold R.v55007, N.v55007.
  rewrite ?node_7689.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55008 (s : N.State) (i : N.Inputs) :
  R.v55008 (state s) (inputs i) = Zmod.unsigned (N.v55008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55008 s i)) at 1.
  unfold R.v55008, N.v55008.
  unfold R.v6, N.v6.
  rewrite ?node_7808.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55009 (s : N.State) (i : N.Inputs) :
  R.v55009 (state s) (inputs i) = Zmod.unsigned (N.v55009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55009 s i)) at 1.
  unfold R.v55009, N.v55009.
  rewrite ?node_55007.
  rewrite ?node_55008.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55010 (s : N.State) (i : N.Inputs) :
  R.v55010 (state s) (inputs i) = Zmod.unsigned (N.v55010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55010 s i)) at 1.
  unfold R.v55010, N.v55010.
  rewrite ?node_55006.
  rewrite ?node_55009.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55011 (s : N.State) (i : N.Inputs) :
  R.v55011 (state s) (inputs i) = Zmod.unsigned (N.v55011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55011 s i)) at 1.
  unfold R.v55011, N.v55011.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55012 (s : N.State) (i : N.Inputs) :
  R.v55012 (state s) (inputs i) = Zmod.unsigned (N.v55012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55012 s i)) at 1.
  unfold R.v55012, N.v55012.
  rewrite ?node_7694.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55013 (s : N.State) (i : N.Inputs) :
  R.v55013 (state s) (inputs i) = Zmod.unsigned (N.v55013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55013 s i)) at 1.
  unfold R.v55013, N.v55013.
  unfold R.v6, N.v6.
  rewrite ?node_7690.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55014 (s : N.State) (i : N.Inputs) :
  R.v55014 (state s) (inputs i) = Zmod.unsigned (N.v55014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55014 s i)) at 1.
  unfold R.v55014, N.v55014.
  unfold R.v6, N.v6.
  rewrite ?node_7689.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55015 (s : N.State) (i : N.Inputs) :
  R.v55015 (state s) (inputs i) = Zmod.unsigned (N.v55015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55015 s i)) at 1.
  unfold R.v55015, N.v55015.
  rewrite ?node_55013.
  rewrite ?node_55014.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55016 (s : N.State) (i : N.Inputs) :
  R.v55016 (state s) (inputs i) = Zmod.unsigned (N.v55016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55016 s i)) at 1.
  unfold R.v55016, N.v55016.
  unfold R.v16484, N.v16484.
  rewrite ?node_55015.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55017 (s : N.State) (i : N.Inputs) :
  R.v55017 (state s) (inputs i) = Zmod.unsigned (N.v55017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55017 s i)) at 1.
  unfold R.v55017, N.v55017.
  rewrite ?node_55012.
  rewrite ?node_55016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55018 (s : N.State) (i : N.Inputs) :
  R.v55018 (state s) (inputs i) = Zmod.unsigned (N.v55018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55018 s i)) at 1.
  unfold R.v55018, N.v55018.
  unfold R.v6, N.v6.
  rewrite ?node_55017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55019 (s : N.State) (i : N.Inputs) :
  R.v55019 (state s) (inputs i) = Zmod.unsigned (N.v55019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55019 s i)) at 1.
  unfold R.v55019, N.v55019.
  rewrite ?node_7695.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55020 (s : N.State) (i : N.Inputs) :
  R.v55020 (state s) (inputs i) = Zmod.unsigned (N.v55020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55020 s i)) at 1.
  unfold R.v55020, N.v55020.
  unfold R.v6, N.v6.
  rewrite ?node_7812.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55021 (s : N.State) (i : N.Inputs) :
  R.v55021 (state s) (inputs i) = Zmod.unsigned (N.v55021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55021 s i)) at 1.
  unfold R.v55021, N.v55021.
  rewrite ?node_55019.
  rewrite ?node_55020.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55022 (s : N.State) (i : N.Inputs) :
  R.v55022 (state s) (inputs i) = Zmod.unsigned (N.v55022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55022 s i)) at 1.
  unfold R.v55022, N.v55022.
  rewrite ?node_55018.
  rewrite ?node_55021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55023 (s : N.State) (i : N.Inputs) :
  R.v55023 (state s) (inputs i) = Zmod.unsigned (N.v55023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55023 s i)) at 1.
  unfold R.v55023, N.v55023.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55024 (s : N.State) (i : N.Inputs) :
  R.v55024 (state s) (inputs i) = Zmod.unsigned (N.v55024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55024 s i)) at 1.
  unfold R.v55024, N.v55024.
  rewrite ?node_7808.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55025 (s : N.State) (i : N.Inputs) :
  R.v55025 (state s) (inputs i) = Zmod.unsigned (N.v55025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55025 s i)) at 1.
  unfold R.v55025, N.v55025.
  rewrite ?node_7804.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55026 (s : N.State) (i : N.Inputs) :
  R.v55026 (state s) (inputs i) = Zmod.unsigned (N.v55026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55026 s i)) at 1.
  unfold R.v55026, N.v55026.
  rewrite ?node_7802.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55027 (s : N.State) (i : N.Inputs) :
  R.v55027 (state s) (inputs i) = Zmod.unsigned (N.v55027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55027 s i)) at 1.
  unfold R.v55027, N.v55027.
  unfold R.v6, N.v6.
  rewrite ?node_7798.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55028 (s : N.State) (i : N.Inputs) :
  R.v55028 (state s) (inputs i) = Zmod.unsigned (N.v55028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55028 s i)) at 1.
  unfold R.v55028, N.v55028.
  unfold R.v6, N.v6.
  rewrite ?node_7791.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55029 (s : N.State) (i : N.Inputs) :
  R.v55029 (state s) (inputs i) = Zmod.unsigned (N.v55029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55029 s i)) at 1.
  unfold R.v55029, N.v55029.
  rewrite ?node_55027.
  rewrite ?node_55028.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55030 (s : N.State) (i : N.Inputs) :
  R.v55030 (state s) (inputs i) = Zmod.unsigned (N.v55030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55030 s i)) at 1.
  unfold R.v55030, N.v55030.
  unfold R.v16484, N.v16484.
  rewrite ?node_55029.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55031 (s : N.State) (i : N.Inputs) :
  R.v55031 (state s) (inputs i) = Zmod.unsigned (N.v55031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55031 s i)) at 1.
  unfold R.v55031, N.v55031.
  rewrite ?node_55024.
  rewrite ?node_55025.
  rewrite ?node_55026.
  rewrite ?node_55030.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55032 (s : N.State) (i : N.Inputs) :
  R.v55032 (state s) (inputs i) = Zmod.unsigned (N.v55032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55032 s i)) at 1.
  unfold R.v55032, N.v55032.
  unfold R.v6, N.v6.
  rewrite ?node_55031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55033 (s : N.State) (i : N.Inputs) :
  R.v55033 (state s) (inputs i) = Zmod.unsigned (N.v55033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55033 s i)) at 1.
  unfold R.v55033, N.v55033.
  rewrite ?node_7809.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55034 (s : N.State) (i : N.Inputs) :
  R.v55034 (state s) (inputs i) = Zmod.unsigned (N.v55034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55034 s i)) at 1.
  unfold R.v55034, N.v55034.
  unfold R.v6, N.v6.
  rewrite ?node_7925.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55035 (s : N.State) (i : N.Inputs) :
  R.v55035 (state s) (inputs i) = Zmod.unsigned (N.v55035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55035 s i)) at 1.
  unfold R.v55035, N.v55035.
  unfold R.v6, N.v6.
  rewrite ?node_7929.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55036 (s : N.State) (i : N.Inputs) :
  R.v55036 (state s) (inputs i) = Zmod.unsigned (N.v55036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55036 s i)) at 1.
  unfold R.v55036, N.v55036.
  rewrite ?node_55033.
  rewrite ?node_55034.
  rewrite ?node_55035.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55037 (s : N.State) (i : N.Inputs) :
  R.v55037 (state s) (inputs i) = Zmod.unsigned (N.v55037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55037 s i)) at 1.
  unfold R.v55037, N.v55037.
  rewrite ?node_55032.
  rewrite ?node_55036.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55038 (s : N.State) (i : N.Inputs) :
  R.v55038 (state s) (inputs i) = Zmod.unsigned (N.v55038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55038 s i)) at 1.
  unfold R.v55038, N.v55038.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55039 (s : N.State) (i : N.Inputs) :
  R.v55039 (state s) (inputs i) = Zmod.unsigned (N.v55039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55039 s i)) at 1.
  unfold R.v55039, N.v55039.
  rewrite ?node_7802.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55040 (s : N.State) (i : N.Inputs) :
  R.v55040 (state s) (inputs i) = Zmod.unsigned (N.v55040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55040 s i)) at 1.
  unfold R.v55040, N.v55040.
  unfold R.v6, N.v6.
  rewrite ?node_7798.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55041 (s : N.State) (i : N.Inputs) :
  R.v55041 (state s) (inputs i) = Zmod.unsigned (N.v55041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55041 s i)) at 1.
  unfold R.v55041, N.v55041.
  unfold R.v6, N.v6.
  rewrite ?node_7791.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55042 (s : N.State) (i : N.Inputs) :
  R.v55042 (state s) (inputs i) = Zmod.unsigned (N.v55042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55042 s i)) at 1.
  unfold R.v55042, N.v55042.
  rewrite ?node_55040.
  rewrite ?node_55041.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55043 (s : N.State) (i : N.Inputs) :
  R.v55043 (state s) (inputs i) = Zmod.unsigned (N.v55043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55043 s i)) at 1.
  unfold R.v55043, N.v55043.
  unfold R.v16484, N.v16484.
  rewrite ?node_55042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55044 (s : N.State) (i : N.Inputs) :
  R.v55044 (state s) (inputs i) = Zmod.unsigned (N.v55044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55044 s i)) at 1.
  unfold R.v55044, N.v55044.
  rewrite ?node_55039.
  rewrite ?node_55043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55045 (s : N.State) (i : N.Inputs) :
  R.v55045 (state s) (inputs i) = Zmod.unsigned (N.v55045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55045 s i)) at 1.
  unfold R.v55045, N.v55045.
  unfold R.v6, N.v6.
  rewrite ?node_55044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55046 (s : N.State) (i : N.Inputs) :
  R.v55046 (state s) (inputs i) = Zmod.unsigned (N.v55046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55046 s i)) at 1.
  unfold R.v55046, N.v55046.
  rewrite ?node_7803.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55047 (s : N.State) (i : N.Inputs) :
  R.v55047 (state s) (inputs i) = Zmod.unsigned (N.v55047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55047 s i)) at 1.
  unfold R.v55047, N.v55047.
  unfold R.v6, N.v6.
  rewrite ?node_7925.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55048 (s : N.State) (i : N.Inputs) :
  R.v55048 (state s) (inputs i) = Zmod.unsigned (N.v55048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55048 s i)) at 1.
  unfold R.v55048, N.v55048.
  rewrite ?node_55046.
  rewrite ?node_55047.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55049 (s : N.State) (i : N.Inputs) :
  R.v55049 (state s) (inputs i) = Zmod.unsigned (N.v55049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55049 s i)) at 1.
  unfold R.v55049, N.v55049.
  rewrite ?node_55045.
  rewrite ?node_55048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55050 (s : N.State) (i : N.Inputs) :
  R.v55050 (state s) (inputs i) = Zmod.unsigned (N.v55050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55050 s i)) at 1.
  unfold R.v55050, N.v55050.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55051 (s : N.State) (i : N.Inputs) :
  R.v55051 (state s) (inputs i) = Zmod.unsigned (N.v55051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55051 s i)) at 1.
  unfold R.v55051, N.v55051.
  rewrite ?node_7808.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55052 (s : N.State) (i : N.Inputs) :
  R.v55052 (state s) (inputs i) = Zmod.unsigned (N.v55052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55052 s i)) at 1.
  unfold R.v55052, N.v55052.
  unfold R.v6, N.v6.
  rewrite ?node_7804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55053 (s : N.State) (i : N.Inputs) :
  R.v55053 (state s) (inputs i) = Zmod.unsigned (N.v55053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55053 s i)) at 1.
  unfold R.v55053, N.v55053.
  unfold R.v6, N.v6.
  rewrite ?node_7803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55054 (s : N.State) (i : N.Inputs) :
  R.v55054 (state s) (inputs i) = Zmod.unsigned (N.v55054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55054 s i)) at 1.
  unfold R.v55054, N.v55054.
  rewrite ?node_55052.
  rewrite ?node_55053.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55055 (s : N.State) (i : N.Inputs) :
  R.v55055 (state s) (inputs i) = Zmod.unsigned (N.v55055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55055 s i)) at 1.
  unfold R.v55055, N.v55055.
  unfold R.v16484, N.v16484.
  rewrite ?node_55054.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55056 (s : N.State) (i : N.Inputs) :
  R.v55056 (state s) (inputs i) = Zmod.unsigned (N.v55056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55056 s i)) at 1.
  unfold R.v55056, N.v55056.
  rewrite ?node_55051.
  rewrite ?node_55055.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55057 (s : N.State) (i : N.Inputs) :
  R.v55057 (state s) (inputs i) = Zmod.unsigned (N.v55057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55057 s i)) at 1.
  unfold R.v55057, N.v55057.
  unfold R.v6, N.v6.
  rewrite ?node_55056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55058 (s : N.State) (i : N.Inputs) :
  R.v55058 (state s) (inputs i) = Zmod.unsigned (N.v55058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55058 s i)) at 1.
  unfold R.v55058, N.v55058.
  rewrite ?node_7809.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55059 (s : N.State) (i : N.Inputs) :
  R.v55059 (state s) (inputs i) = Zmod.unsigned (N.v55059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55059 s i)) at 1.
  unfold R.v55059, N.v55059.
  unfold R.v6, N.v6.
  rewrite ?node_7929.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55060 (s : N.State) (i : N.Inputs) :
  R.v55060 (state s) (inputs i) = Zmod.unsigned (N.v55060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55060 s i)) at 1.
  unfold R.v55060, N.v55060.
  rewrite ?node_55058.
  rewrite ?node_55059.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55061 (s : N.State) (i : N.Inputs) :
  R.v55061 (state s) (inputs i) = Zmod.unsigned (N.v55061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55061 s i)) at 1.
  unfold R.v55061, N.v55061.
  rewrite ?node_55057.
  rewrite ?node_55060.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55062 (s : N.State) (i : N.Inputs) :
  R.v55062 (state s) (inputs i) = Zmod.unsigned (N.v55062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55062 s i)) at 1.
  unfold R.v55062, N.v55062.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55063 (s : N.State) (i : N.Inputs) :
  R.v55063 (state s) (inputs i) = Zmod.unsigned (N.v55063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55063 s i)) at 1.
  unfold R.v55063, N.v55063.
  rewrite ?node_7925.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55064 (s : N.State) (i : N.Inputs) :
  R.v55064 (state s) (inputs i) = Zmod.unsigned (N.v55064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55064 s i)) at 1.
  unfold R.v55064, N.v55064.
  rewrite ?node_7921.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55065 (s : N.State) (i : N.Inputs) :
  R.v55065 (state s) (inputs i) = Zmod.unsigned (N.v55065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55065 s i)) at 1.
  unfold R.v55065, N.v55065.
  rewrite ?node_7919.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55066 (s : N.State) (i : N.Inputs) :
  R.v55066 (state s) (inputs i) = Zmod.unsigned (N.v55066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55066 s i)) at 1.
  unfold R.v55066, N.v55066.
  unfold R.v6, N.v6.
  rewrite ?node_7915.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55067 (s : N.State) (i : N.Inputs) :
  R.v55067 (state s) (inputs i) = Zmod.unsigned (N.v55067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55067 s i)) at 1.
  unfold R.v55067, N.v55067.
  unfold R.v6, N.v6.
  rewrite ?node_7904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55068 (s : N.State) (i : N.Inputs) :
  R.v55068 (state s) (inputs i) = Zmod.unsigned (N.v55068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55068 s i)) at 1.
  unfold R.v55068, N.v55068.
  rewrite ?node_55066.
  rewrite ?node_55067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55069 (s : N.State) (i : N.Inputs) :
  R.v55069 (state s) (inputs i) = Zmod.unsigned (N.v55069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55069 s i)) at 1.
  unfold R.v55069, N.v55069.
  unfold R.v16484, N.v16484.
  rewrite ?node_55068.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55070 (s : N.State) (i : N.Inputs) :
  R.v55070 (state s) (inputs i) = Zmod.unsigned (N.v55070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55070 s i)) at 1.
  unfold R.v55070, N.v55070.
  rewrite ?node_55063.
  rewrite ?node_55064.
  rewrite ?node_55065.
  rewrite ?node_55069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55071 (s : N.State) (i : N.Inputs) :
  R.v55071 (state s) (inputs i) = Zmod.unsigned (N.v55071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55071 s i)) at 1.
  unfold R.v55071, N.v55071.
  unfold R.v6, N.v6.
  rewrite ?node_55070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55072 (s : N.State) (i : N.Inputs) :
  R.v55072 (state s) (inputs i) = Zmod.unsigned (N.v55072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55072 s i)) at 1.
  unfold R.v55072, N.v55072.
  rewrite ?node_7926.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55073 (s : N.State) (i : N.Inputs) :
  R.v55073 (state s) (inputs i) = Zmod.unsigned (N.v55073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55073 s i)) at 1.
  unfold R.v55073, N.v55073.
  unfold R.v6, N.v6.
  rewrite ?node_8044.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55074 (s : N.State) (i : N.Inputs) :
  R.v55074 (state s) (inputs i) = Zmod.unsigned (N.v55074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55074 s i)) at 1.
  unfold R.v55074, N.v55074.
  unfold R.v6, N.v6.
  rewrite ?node_8048.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55075 (s : N.State) (i : N.Inputs) :
  R.v55075 (state s) (inputs i) = Zmod.unsigned (N.v55075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55075 s i)) at 1.
  unfold R.v55075, N.v55075.
  rewrite ?node_55072.
  rewrite ?node_55073.
  rewrite ?node_55074.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55076 (s : N.State) (i : N.Inputs) :
  R.v55076 (state s) (inputs i) = Zmod.unsigned (N.v55076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55076 s i)) at 1.
  unfold R.v55076, N.v55076.
  rewrite ?node_55071.
  rewrite ?node_55075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55077 (s : N.State) (i : N.Inputs) :
  R.v55077 (state s) (inputs i) = Zmod.unsigned (N.v55077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55077 s i)) at 1.
  unfold R.v55077, N.v55077.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55078 (s : N.State) (i : N.Inputs) :
  R.v55078 (state s) (inputs i) = Zmod.unsigned (N.v55078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55078 s i)) at 1.
  unfold R.v55078, N.v55078.
  rewrite ?node_7919.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55079 (s : N.State) (i : N.Inputs) :
  R.v55079 (state s) (inputs i) = Zmod.unsigned (N.v55079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55079 s i)) at 1.
  unfold R.v55079, N.v55079.
  unfold R.v6, N.v6.
  rewrite ?node_7915.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55080 (s : N.State) (i : N.Inputs) :
  R.v55080 (state s) (inputs i) = Zmod.unsigned (N.v55080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55080 s i)) at 1.
  unfold R.v55080, N.v55080.
  unfold R.v6, N.v6.
  rewrite ?node_7904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55081 (s : N.State) (i : N.Inputs) :
  R.v55081 (state s) (inputs i) = Zmod.unsigned (N.v55081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55081 s i)) at 1.
  unfold R.v55081, N.v55081.
  rewrite ?node_55079.
  rewrite ?node_55080.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55082 (s : N.State) (i : N.Inputs) :
  R.v55082 (state s) (inputs i) = Zmod.unsigned (N.v55082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55082 s i)) at 1.
  unfold R.v55082, N.v55082.
  unfold R.v16484, N.v16484.
  rewrite ?node_55081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55083 (s : N.State) (i : N.Inputs) :
  R.v55083 (state s) (inputs i) = Zmod.unsigned (N.v55083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55083 s i)) at 1.
  unfold R.v55083, N.v55083.
  rewrite ?node_55078.
  rewrite ?node_55082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55084 (s : N.State) (i : N.Inputs) :
  R.v55084 (state s) (inputs i) = Zmod.unsigned (N.v55084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55084 s i)) at 1.
  unfold R.v55084, N.v55084.
  unfold R.v6, N.v6.
  rewrite ?node_55083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55085 (s : N.State) (i : N.Inputs) :
  R.v55085 (state s) (inputs i) = Zmod.unsigned (N.v55085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55085 s i)) at 1.
  unfold R.v55085, N.v55085.
  rewrite ?node_7920.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55086 (s : N.State) (i : N.Inputs) :
  R.v55086 (state s) (inputs i) = Zmod.unsigned (N.v55086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55086 s i)) at 1.
  unfold R.v55086, N.v55086.
  unfold R.v6, N.v6.
  rewrite ?node_8044.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55087 (s : N.State) (i : N.Inputs) :
  R.v55087 (state s) (inputs i) = Zmod.unsigned (N.v55087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55087 s i)) at 1.
  unfold R.v55087, N.v55087.
  rewrite ?node_55085.
  rewrite ?node_55086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55088 (s : N.State) (i : N.Inputs) :
  R.v55088 (state s) (inputs i) = Zmod.unsigned (N.v55088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55088 s i)) at 1.
  unfold R.v55088, N.v55088.
  rewrite ?node_55084.
  rewrite ?node_55087.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55089 (s : N.State) (i : N.Inputs) :
  R.v55089 (state s) (inputs i) = Zmod.unsigned (N.v55089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55089 s i)) at 1.
  unfold R.v55089, N.v55089.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55090 (s : N.State) (i : N.Inputs) :
  R.v55090 (state s) (inputs i) = Zmod.unsigned (N.v55090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55090 s i)) at 1.
  unfold R.v55090, N.v55090.
  rewrite ?node_7925.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55091 (s : N.State) (i : N.Inputs) :
  R.v55091 (state s) (inputs i) = Zmod.unsigned (N.v55091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55091 s i)) at 1.
  unfold R.v55091, N.v55091.
  unfold R.v6, N.v6.
  rewrite ?node_7921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55092 (s : N.State) (i : N.Inputs) :
  R.v55092 (state s) (inputs i) = Zmod.unsigned (N.v55092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55092 s i)) at 1.
  unfold R.v55092, N.v55092.
  unfold R.v6, N.v6.
  rewrite ?node_7920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55093 (s : N.State) (i : N.Inputs) :
  R.v55093 (state s) (inputs i) = Zmod.unsigned (N.v55093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55093 s i)) at 1.
  unfold R.v55093, N.v55093.
  rewrite ?node_55091.
  rewrite ?node_55092.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55094 (s : N.State) (i : N.Inputs) :
  R.v55094 (state s) (inputs i) = Zmod.unsigned (N.v55094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55094 s i)) at 1.
  unfold R.v55094, N.v55094.
  unfold R.v16484, N.v16484.
  rewrite ?node_55093.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55095 (s : N.State) (i : N.Inputs) :
  R.v55095 (state s) (inputs i) = Zmod.unsigned (N.v55095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55095 s i)) at 1.
  unfold R.v55095, N.v55095.
  rewrite ?node_55090.
  rewrite ?node_55094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55096 (s : N.State) (i : N.Inputs) :
  R.v55096 (state s) (inputs i) = Zmod.unsigned (N.v55096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55096 s i)) at 1.
  unfold R.v55096, N.v55096.
  unfold R.v6, N.v6.
  rewrite ?node_55095.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55097 (s : N.State) (i : N.Inputs) :
  R.v55097 (state s) (inputs i) = Zmod.unsigned (N.v55097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55097 s i)) at 1.
  unfold R.v55097, N.v55097.
  rewrite ?node_7926.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55098 (s : N.State) (i : N.Inputs) :
  R.v55098 (state s) (inputs i) = Zmod.unsigned (N.v55098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55098 s i)) at 1.
  unfold R.v55098, N.v55098.
  unfold R.v6, N.v6.
  rewrite ?node_8048.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55099 (s : N.State) (i : N.Inputs) :
  R.v55099 (state s) (inputs i) = Zmod.unsigned (N.v55099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55099 s i)) at 1.
  unfold R.v55099, N.v55099.
  rewrite ?node_55097.
  rewrite ?node_55098.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55100 (s : N.State) (i : N.Inputs) :
  R.v55100 (state s) (inputs i) = Zmod.unsigned (N.v55100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55100 s i)) at 1.
  unfold R.v55100, N.v55100.
  rewrite ?node_55096.
  rewrite ?node_55099.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55101 (s : N.State) (i : N.Inputs) :
  R.v55101 (state s) (inputs i) = Zmod.unsigned (N.v55101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55101 s i)) at 1.
  unfold R.v55101, N.v55101.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55102 (s : N.State) (i : N.Inputs) :
  R.v55102 (state s) (inputs i) = Zmod.unsigned (N.v55102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55102 s i)) at 1.
  unfold R.v55102, N.v55102.
  rewrite ?node_8044.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55103 (s : N.State) (i : N.Inputs) :
  R.v55103 (state s) (inputs i) = Zmod.unsigned (N.v55103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55103 s i)) at 1.
  unfold R.v55103, N.v55103.
  rewrite ?node_8040.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55104 (s : N.State) (i : N.Inputs) :
  R.v55104 (state s) (inputs i) = Zmod.unsigned (N.v55104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55104 s i)) at 1.
  unfold R.v55104, N.v55104.
  rewrite ?node_8036.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55105 (s : N.State) (i : N.Inputs) :
  R.v55105 (state s) (inputs i) = Zmod.unsigned (N.v55105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55105 s i)) at 1.
  unfold R.v55105, N.v55105.
  unfold R.v6, N.v6.
  rewrite ?node_8032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55106 (s : N.State) (i : N.Inputs) :
  R.v55106 (state s) (inputs i) = Zmod.unsigned (N.v55106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55106 s i)) at 1.
  unfold R.v55106, N.v55106.
  unfold R.v6, N.v6.
  rewrite ?node_8021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55107 (s : N.State) (i : N.Inputs) :
  R.v55107 (state s) (inputs i) = Zmod.unsigned (N.v55107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55107 s i)) at 1.
  unfold R.v55107, N.v55107.
  rewrite ?node_55105.
  rewrite ?node_55106.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55108 (s : N.State) (i : N.Inputs) :
  R.v55108 (state s) (inputs i) = Zmod.unsigned (N.v55108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55108 s i)) at 1.
  unfold R.v55108, N.v55108.
  unfold R.v16484, N.v16484.
  rewrite ?node_55107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55109 (s : N.State) (i : N.Inputs) :
  R.v55109 (state s) (inputs i) = Zmod.unsigned (N.v55109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55109 s i)) at 1.
  unfold R.v55109, N.v55109.
  rewrite ?node_55102.
  rewrite ?node_55103.
  rewrite ?node_55104.
  rewrite ?node_55108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55110 (s : N.State) (i : N.Inputs) :
  R.v55110 (state s) (inputs i) = Zmod.unsigned (N.v55110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55110 s i)) at 1.
  unfold R.v55110, N.v55110.
  unfold R.v6, N.v6.
  rewrite ?node_55109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55111 (s : N.State) (i : N.Inputs) :
  R.v55111 (state s) (inputs i) = Zmod.unsigned (N.v55111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55111 s i)) at 1.
  unfold R.v55111, N.v55111.
  rewrite ?node_8045.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55112 (s : N.State) (i : N.Inputs) :
  R.v55112 (state s) (inputs i) = Zmod.unsigned (N.v55112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55112 s i)) at 1.
  unfold R.v55112, N.v55112.
  unfold R.v6, N.v6.
  rewrite ?node_8164.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55113 (s : N.State) (i : N.Inputs) :
  R.v55113 (state s) (inputs i) = Zmod.unsigned (N.v55113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55113 s i)) at 1.
  unfold R.v55113, N.v55113.
  unfold R.v6, N.v6.
  rewrite ?node_8168.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55114 (s : N.State) (i : N.Inputs) :
  R.v55114 (state s) (inputs i) = Zmod.unsigned (N.v55114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55114 s i)) at 1.
  unfold R.v55114, N.v55114.
  rewrite ?node_55111.
  rewrite ?node_55112.
  rewrite ?node_55113.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55115 (s : N.State) (i : N.Inputs) :
  R.v55115 (state s) (inputs i) = Zmod.unsigned (N.v55115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55115 s i)) at 1.
  unfold R.v55115, N.v55115.
  rewrite ?node_55110.
  rewrite ?node_55114.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55116 (s : N.State) (i : N.Inputs) :
  R.v55116 (state s) (inputs i) = Zmod.unsigned (N.v55116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55116 s i)) at 1.
  unfold R.v55116, N.v55116.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55117 (s : N.State) (i : N.Inputs) :
  R.v55117 (state s) (inputs i) = Zmod.unsigned (N.v55117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55117 s i)) at 1.
  unfold R.v55117, N.v55117.
  rewrite ?node_8036.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55118 (s : N.State) (i : N.Inputs) :
  R.v55118 (state s) (inputs i) = Zmod.unsigned (N.v55118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55118 s i)) at 1.
  unfold R.v55118, N.v55118.
  unfold R.v6, N.v6.
  rewrite ?node_8032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55119 (s : N.State) (i : N.Inputs) :
  R.v55119 (state s) (inputs i) = Zmod.unsigned (N.v55119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55119 s i)) at 1.
  unfold R.v55119, N.v55119.
  unfold R.v6, N.v6.
  rewrite ?node_8021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55120 (s : N.State) (i : N.Inputs) :
  R.v55120 (state s) (inputs i) = Zmod.unsigned (N.v55120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55120 s i)) at 1.
  unfold R.v55120, N.v55120.
  rewrite ?node_55118.
  rewrite ?node_55119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55121 (s : N.State) (i : N.Inputs) :
  R.v55121 (state s) (inputs i) = Zmod.unsigned (N.v55121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55121 s i)) at 1.
  unfold R.v55121, N.v55121.
  unfold R.v16484, N.v16484.
  rewrite ?node_55120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55122 (s : N.State) (i : N.Inputs) :
  R.v55122 (state s) (inputs i) = Zmod.unsigned (N.v55122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55122 s i)) at 1.
  unfold R.v55122, N.v55122.
  rewrite ?node_55117.
  rewrite ?node_55121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55123 (s : N.State) (i : N.Inputs) :
  R.v55123 (state s) (inputs i) = Zmod.unsigned (N.v55123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55123 s i)) at 1.
  unfold R.v55123, N.v55123.
  unfold R.v6, N.v6.
  rewrite ?node_55122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55124 (s : N.State) (i : N.Inputs) :
  R.v55124 (state s) (inputs i) = Zmod.unsigned (N.v55124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55124 s i)) at 1.
  unfold R.v55124, N.v55124.
  rewrite ?node_8037.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55125 (s : N.State) (i : N.Inputs) :
  R.v55125 (state s) (inputs i) = Zmod.unsigned (N.v55125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55125 s i)) at 1.
  unfold R.v55125, N.v55125.
  unfold R.v6, N.v6.
  rewrite ?node_8164.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55126 (s : N.State) (i : N.Inputs) :
  R.v55126 (state s) (inputs i) = Zmod.unsigned (N.v55126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55126 s i)) at 1.
  unfold R.v55126, N.v55126.
  rewrite ?node_55124.
  rewrite ?node_55125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55127 (s : N.State) (i : N.Inputs) :
  R.v55127 (state s) (inputs i) = Zmod.unsigned (N.v55127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55127 s i)) at 1.
  unfold R.v55127, N.v55127.
  rewrite ?node_55123.
  rewrite ?node_55126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55128 (s : N.State) (i : N.Inputs) :
  R.v55128 (state s) (inputs i) = Zmod.unsigned (N.v55128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55128 s i)) at 1.
  unfold R.v55128, N.v55128.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55129 (s : N.State) (i : N.Inputs) :
  R.v55129 (state s) (inputs i) = Zmod.unsigned (N.v55129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55129 s i)) at 1.
  unfold R.v55129, N.v55129.
  rewrite ?node_8044.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55130 (s : N.State) (i : N.Inputs) :
  R.v55130 (state s) (inputs i) = Zmod.unsigned (N.v55130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55130 s i)) at 1.
  unfold R.v55130, N.v55130.
  unfold R.v6, N.v6.
  rewrite ?node_8040.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55131 (s : N.State) (i : N.Inputs) :
  R.v55131 (state s) (inputs i) = Zmod.unsigned (N.v55131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55131 s i)) at 1.
  unfold R.v55131, N.v55131.
  unfold R.v6, N.v6.
  rewrite ?node_8037.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55132 (s : N.State) (i : N.Inputs) :
  R.v55132 (state s) (inputs i) = Zmod.unsigned (N.v55132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55132 s i)) at 1.
  unfold R.v55132, N.v55132.
  rewrite ?node_55130.
  rewrite ?node_55131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55133 (s : N.State) (i : N.Inputs) :
  R.v55133 (state s) (inputs i) = Zmod.unsigned (N.v55133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55133 s i)) at 1.
  unfold R.v55133, N.v55133.
  unfold R.v16484, N.v16484.
  rewrite ?node_55132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55134 (s : N.State) (i : N.Inputs) :
  R.v55134 (state s) (inputs i) = Zmod.unsigned (N.v55134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55134 s i)) at 1.
  unfold R.v55134, N.v55134.
  rewrite ?node_55129.
  rewrite ?node_55133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55135 (s : N.State) (i : N.Inputs) :
  R.v55135 (state s) (inputs i) = Zmod.unsigned (N.v55135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55135 s i)) at 1.
  unfold R.v55135, N.v55135.
  unfold R.v6, N.v6.
  rewrite ?node_55134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55136 (s : N.State) (i : N.Inputs) :
  R.v55136 (state s) (inputs i) = Zmod.unsigned (N.v55136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55136 s i)) at 1.
  unfold R.v55136, N.v55136.
  rewrite ?node_8045.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55137 (s : N.State) (i : N.Inputs) :
  R.v55137 (state s) (inputs i) = Zmod.unsigned (N.v55137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55137 s i)) at 1.
  unfold R.v55137, N.v55137.
  unfold R.v6, N.v6.
  rewrite ?node_8168.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55138 (s : N.State) (i : N.Inputs) :
  R.v55138 (state s) (inputs i) = Zmod.unsigned (N.v55138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55138 s i)) at 1.
  unfold R.v55138, N.v55138.
  rewrite ?node_55136.
  rewrite ?node_55137.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55139 (s : N.State) (i : N.Inputs) :
  R.v55139 (state s) (inputs i) = Zmod.unsigned (N.v55139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55139 s i)) at 1.
  unfold R.v55139, N.v55139.
  rewrite ?node_55135.
  rewrite ?node_55138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55140 (s : N.State) (i : N.Inputs) :
  R.v55140 (state s) (inputs i) = Zmod.unsigned (N.v55140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55140 s i)) at 1.
  unfold R.v55140, N.v55140.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55141 (s : N.State) (i : N.Inputs) :
  R.v55141 (state s) (inputs i) = Zmod.unsigned (N.v55141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55141 s i)) at 1.
  unfold R.v55141, N.v55141.
  rewrite ?node_8164.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55142 (s : N.State) (i : N.Inputs) :
  R.v55142 (state s) (inputs i) = Zmod.unsigned (N.v55142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55142 s i)) at 1.
  unfold R.v55142, N.v55142.
  rewrite ?node_8160.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55143 (s : N.State) (i : N.Inputs) :
  R.v55143 (state s) (inputs i) = Zmod.unsigned (N.v55143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55143 s i)) at 1.
  unfold R.v55143, N.v55143.
  rewrite ?node_8156.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55144 (s : N.State) (i : N.Inputs) :
  R.v55144 (state s) (inputs i) = Zmod.unsigned (N.v55144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55144 s i)) at 1.
  unfold R.v55144, N.v55144.
  unfold R.v6, N.v6.
  rewrite ?node_8152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55145 (s : N.State) (i : N.Inputs) :
  R.v55145 (state s) (inputs i) = Zmod.unsigned (N.v55145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55145 s i)) at 1.
  unfold R.v55145, N.v55145.
  unfold R.v6, N.v6.
  rewrite ?node_8141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55146 (s : N.State) (i : N.Inputs) :
  R.v55146 (state s) (inputs i) = Zmod.unsigned (N.v55146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55146 s i)) at 1.
  unfold R.v55146, N.v55146.
  rewrite ?node_55144.
  rewrite ?node_55145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55147 (s : N.State) (i : N.Inputs) :
  R.v55147 (state s) (inputs i) = Zmod.unsigned (N.v55147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55147 s i)) at 1.
  unfold R.v55147, N.v55147.
  unfold R.v16484, N.v16484.
  rewrite ?node_55146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55148 (s : N.State) (i : N.Inputs) :
  R.v55148 (state s) (inputs i) = Zmod.unsigned (N.v55148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55148 s i)) at 1.
  unfold R.v55148, N.v55148.
  rewrite ?node_55141.
  rewrite ?node_55142.
  rewrite ?node_55143.
  rewrite ?node_55147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55149 (s : N.State) (i : N.Inputs) :
  R.v55149 (state s) (inputs i) = Zmod.unsigned (N.v55149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55149 s i)) at 1.
  unfold R.v55149, N.v55149.
  unfold R.v6, N.v6.
  rewrite ?node_55148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55150 (s : N.State) (i : N.Inputs) :
  R.v55150 (state s) (inputs i) = Zmod.unsigned (N.v55150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55150 s i)) at 1.
  unfold R.v55150, N.v55150.
  rewrite ?node_8165.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55151 (s : N.State) (i : N.Inputs) :
  R.v55151 (state s) (inputs i) = Zmod.unsigned (N.v55151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55151 s i)) at 1.
  unfold R.v55151, N.v55151.
  unfold R.v6, N.v6.
  rewrite ?node_8286.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55152 (s : N.State) (i : N.Inputs) :
  R.v55152 (state s) (inputs i) = Zmod.unsigned (N.v55152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55152 s i)) at 1.
  unfold R.v55152, N.v55152.
  unfold R.v6, N.v6.
  rewrite ?node_8290.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55153 (s : N.State) (i : N.Inputs) :
  R.v55153 (state s) (inputs i) = Zmod.unsigned (N.v55153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55153 s i)) at 1.
  unfold R.v55153, N.v55153.
  rewrite ?node_55150.
  rewrite ?node_55151.
  rewrite ?node_55152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55154 (s : N.State) (i : N.Inputs) :
  R.v55154 (state s) (inputs i) = Zmod.unsigned (N.v55154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55154 s i)) at 1.
  unfold R.v55154, N.v55154.
  rewrite ?node_55149.
  rewrite ?node_55153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55155 (s : N.State) (i : N.Inputs) :
  R.v55155 (state s) (inputs i) = Zmod.unsigned (N.v55155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55155 s i)) at 1.
  unfold R.v55155, N.v55155.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55156 (s : N.State) (i : N.Inputs) :
  R.v55156 (state s) (inputs i) = Zmod.unsigned (N.v55156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55156 s i)) at 1.
  unfold R.v55156, N.v55156.
  rewrite ?node_8156.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55157 (s : N.State) (i : N.Inputs) :
  R.v55157 (state s) (inputs i) = Zmod.unsigned (N.v55157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55157 s i)) at 1.
  unfold R.v55157, N.v55157.
  unfold R.v6, N.v6.
  rewrite ?node_8152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55158 (s : N.State) (i : N.Inputs) :
  R.v55158 (state s) (inputs i) = Zmod.unsigned (N.v55158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55158 s i)) at 1.
  unfold R.v55158, N.v55158.
  unfold R.v6, N.v6.
  rewrite ?node_8141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55159 (s : N.State) (i : N.Inputs) :
  R.v55159 (state s) (inputs i) = Zmod.unsigned (N.v55159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55159 s i)) at 1.
  unfold R.v55159, N.v55159.
  rewrite ?node_55157.
  rewrite ?node_55158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55160 (s : N.State) (i : N.Inputs) :
  R.v55160 (state s) (inputs i) = Zmod.unsigned (N.v55160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55160 s i)) at 1.
  unfold R.v55160, N.v55160.
  unfold R.v16484, N.v16484.
  rewrite ?node_55159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55161 (s : N.State) (i : N.Inputs) :
  R.v55161 (state s) (inputs i) = Zmod.unsigned (N.v55161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55161 s i)) at 1.
  unfold R.v55161, N.v55161.
  rewrite ?node_55156.
  rewrite ?node_55160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55162 (s : N.State) (i : N.Inputs) :
  R.v55162 (state s) (inputs i) = Zmod.unsigned (N.v55162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55162 s i)) at 1.
  unfold R.v55162, N.v55162.
  unfold R.v6, N.v6.
  rewrite ?node_55161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55163 (s : N.State) (i : N.Inputs) :
  R.v55163 (state s) (inputs i) = Zmod.unsigned (N.v55163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55163 s i)) at 1.
  unfold R.v55163, N.v55163.
  rewrite ?node_8157.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55164 (s : N.State) (i : N.Inputs) :
  R.v55164 (state s) (inputs i) = Zmod.unsigned (N.v55164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55164 s i)) at 1.
  unfold R.v55164, N.v55164.
  unfold R.v6, N.v6.
  rewrite ?node_8286.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55165 (s : N.State) (i : N.Inputs) :
  R.v55165 (state s) (inputs i) = Zmod.unsigned (N.v55165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55165 s i)) at 1.
  unfold R.v55165, N.v55165.
  rewrite ?node_55163.
  rewrite ?node_55164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55166 (s : N.State) (i : N.Inputs) :
  R.v55166 (state s) (inputs i) = Zmod.unsigned (N.v55166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55166 s i)) at 1.
  unfold R.v55166, N.v55166.
  rewrite ?node_55162.
  rewrite ?node_55165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55167 (s : N.State) (i : N.Inputs) :
  R.v55167 (state s) (inputs i) = Zmod.unsigned (N.v55167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55167 s i)) at 1.
  unfold R.v55167, N.v55167.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55168 (s : N.State) (i : N.Inputs) :
  R.v55168 (state s) (inputs i) = Zmod.unsigned (N.v55168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55168 s i)) at 1.
  unfold R.v55168, N.v55168.
  rewrite ?node_8164.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55169 (s : N.State) (i : N.Inputs) :
  R.v55169 (state s) (inputs i) = Zmod.unsigned (N.v55169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55169 s i)) at 1.
  unfold R.v55169, N.v55169.
  unfold R.v6, N.v6.
  rewrite ?node_8160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55170 (s : N.State) (i : N.Inputs) :
  R.v55170 (state s) (inputs i) = Zmod.unsigned (N.v55170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55170 s i)) at 1.
  unfold R.v55170, N.v55170.
  unfold R.v6, N.v6.
  rewrite ?node_8157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55171 (s : N.State) (i : N.Inputs) :
  R.v55171 (state s) (inputs i) = Zmod.unsigned (N.v55171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55171 s i)) at 1.
  unfold R.v55171, N.v55171.
  rewrite ?node_55169.
  rewrite ?node_55170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55172 (s : N.State) (i : N.Inputs) :
  R.v55172 (state s) (inputs i) = Zmod.unsigned (N.v55172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55172 s i)) at 1.
  unfold R.v55172, N.v55172.
  unfold R.v16484, N.v16484.
  rewrite ?node_55171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55173 (s : N.State) (i : N.Inputs) :
  R.v55173 (state s) (inputs i) = Zmod.unsigned (N.v55173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55173 s i)) at 1.
  unfold R.v55173, N.v55173.
  rewrite ?node_55168.
  rewrite ?node_55172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55174 (s : N.State) (i : N.Inputs) :
  R.v55174 (state s) (inputs i) = Zmod.unsigned (N.v55174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55174 s i)) at 1.
  unfold R.v55174, N.v55174.
  unfold R.v6, N.v6.
  rewrite ?node_55173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55175 (s : N.State) (i : N.Inputs) :
  R.v55175 (state s) (inputs i) = Zmod.unsigned (N.v55175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55175 s i)) at 1.
  unfold R.v55175, N.v55175.
  rewrite ?node_8165.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55176 (s : N.State) (i : N.Inputs) :
  R.v55176 (state s) (inputs i) = Zmod.unsigned (N.v55176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55176 s i)) at 1.
  unfold R.v55176, N.v55176.
  unfold R.v6, N.v6.
  rewrite ?node_8290.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55177 (s : N.State) (i : N.Inputs) :
  R.v55177 (state s) (inputs i) = Zmod.unsigned (N.v55177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55177 s i)) at 1.
  unfold R.v55177, N.v55177.
  rewrite ?node_55175.
  rewrite ?node_55176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55178 (s : N.State) (i : N.Inputs) :
  R.v55178 (state s) (inputs i) = Zmod.unsigned (N.v55178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55178 s i)) at 1.
  unfold R.v55178, N.v55178.
  rewrite ?node_55174.
  rewrite ?node_55177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55179 (s : N.State) (i : N.Inputs) :
  R.v55179 (state s) (inputs i) = Zmod.unsigned (N.v55179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55179 s i)) at 1.
  unfold R.v55179, N.v55179.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55180 (s : N.State) (i : N.Inputs) :
  R.v55180 (state s) (inputs i) = Zmod.unsigned (N.v55180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55180 s i)) at 1.
  unfold R.v55180, N.v55180.
  rewrite ?node_8286.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55181 (s : N.State) (i : N.Inputs) :
  R.v55181 (state s) (inputs i) = Zmod.unsigned (N.v55181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55181 s i)) at 1.
  unfold R.v55181, N.v55181.
  rewrite ?node_8282.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55182 (s : N.State) (i : N.Inputs) :
  R.v55182 (state s) (inputs i) = Zmod.unsigned (N.v55182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55182 s i)) at 1.
  unfold R.v55182, N.v55182.
  rewrite ?node_8278.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55183 (s : N.State) (i : N.Inputs) :
  R.v55183 (state s) (inputs i) = Zmod.unsigned (N.v55183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55183 s i)) at 1.
  unfold R.v55183, N.v55183.
  unfold R.v6, N.v6.
  rewrite ?node_8274.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55184 (s : N.State) (i : N.Inputs) :
  R.v55184 (state s) (inputs i) = Zmod.unsigned (N.v55184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55184 s i)) at 1.
  unfold R.v55184, N.v55184.
  unfold R.v6, N.v6.
  rewrite ?node_8263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55185 (s : N.State) (i : N.Inputs) :
  R.v55185 (state s) (inputs i) = Zmod.unsigned (N.v55185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55185 s i)) at 1.
  unfold R.v55185, N.v55185.
  rewrite ?node_55183.
  rewrite ?node_55184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55186 (s : N.State) (i : N.Inputs) :
  R.v55186 (state s) (inputs i) = Zmod.unsigned (N.v55186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55186 s i)) at 1.
  unfold R.v55186, N.v55186.
  unfold R.v16484, N.v16484.
  rewrite ?node_55185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55187 (s : N.State) (i : N.Inputs) :
  R.v55187 (state s) (inputs i) = Zmod.unsigned (N.v55187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55187 s i)) at 1.
  unfold R.v55187, N.v55187.
  rewrite ?node_55180.
  rewrite ?node_55181.
  rewrite ?node_55182.
  rewrite ?node_55186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55188 (s : N.State) (i : N.Inputs) :
  R.v55188 (state s) (inputs i) = Zmod.unsigned (N.v55188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55188 s i)) at 1.
  unfold R.v55188, N.v55188.
  unfold R.v6, N.v6.
  rewrite ?node_55187.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55189 (s : N.State) (i : N.Inputs) :
  R.v55189 (state s) (inputs i) = Zmod.unsigned (N.v55189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55189 s i)) at 1.
  unfold R.v55189, N.v55189.
  rewrite ?node_8287.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55190 (s : N.State) (i : N.Inputs) :
  R.v55190 (state s) (inputs i) = Zmod.unsigned (N.v55190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55190 s i)) at 1.
  unfold R.v55190, N.v55190.
  unfold R.v6, N.v6.
  rewrite ?node_8411.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55191 (s : N.State) (i : N.Inputs) :
  R.v55191 (state s) (inputs i) = Zmod.unsigned (N.v55191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55191 s i)) at 1.
  unfold R.v55191, N.v55191.
  unfold R.v6, N.v6.
  rewrite ?node_8415.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55192 (s : N.State) (i : N.Inputs) :
  R.v55192 (state s) (inputs i) = Zmod.unsigned (N.v55192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55192 s i)) at 1.
  unfold R.v55192, N.v55192.
  rewrite ?node_55189.
  rewrite ?node_55190.
  rewrite ?node_55191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55193 (s : N.State) (i : N.Inputs) :
  R.v55193 (state s) (inputs i) = Zmod.unsigned (N.v55193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55193 s i)) at 1.
  unfold R.v55193, N.v55193.
  rewrite ?node_55188.
  rewrite ?node_55192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55194 (s : N.State) (i : N.Inputs) :
  R.v55194 (state s) (inputs i) = Zmod.unsigned (N.v55194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55194 s i)) at 1.
  unfold R.v55194, N.v55194.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55195 (s : N.State) (i : N.Inputs) :
  R.v55195 (state s) (inputs i) = Zmod.unsigned (N.v55195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55195 s i)) at 1.
  unfold R.v55195, N.v55195.
  rewrite ?node_8278.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55196 (s : N.State) (i : N.Inputs) :
  R.v55196 (state s) (inputs i) = Zmod.unsigned (N.v55196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55196 s i)) at 1.
  unfold R.v55196, N.v55196.
  unfold R.v6, N.v6.
  rewrite ?node_8274.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55197 (s : N.State) (i : N.Inputs) :
  R.v55197 (state s) (inputs i) = Zmod.unsigned (N.v55197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55197 s i)) at 1.
  unfold R.v55197, N.v55197.
  unfold R.v6, N.v6.
  rewrite ?node_8263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55198 (s : N.State) (i : N.Inputs) :
  R.v55198 (state s) (inputs i) = Zmod.unsigned (N.v55198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55198 s i)) at 1.
  unfold R.v55198, N.v55198.
  rewrite ?node_55196.
  rewrite ?node_55197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55199 (s : N.State) (i : N.Inputs) :
  R.v55199 (state s) (inputs i) = Zmod.unsigned (N.v55199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55199 s i)) at 1.
  unfold R.v55199, N.v55199.
  unfold R.v16484, N.v16484.
  rewrite ?node_55198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55200 (s : N.State) (i : N.Inputs) :
  R.v55200 (state s) (inputs i) = Zmod.unsigned (N.v55200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55200 s i)) at 1.
  unfold R.v55200, N.v55200.
  rewrite ?node_55195.
  rewrite ?node_55199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55201 (s : N.State) (i : N.Inputs) :
  R.v55201 (state s) (inputs i) = Zmod.unsigned (N.v55201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55201 s i)) at 1.
  unfold R.v55201, N.v55201.
  unfold R.v6, N.v6.
  rewrite ?node_55200.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55202 (s : N.State) (i : N.Inputs) :
  R.v55202 (state s) (inputs i) = Zmod.unsigned (N.v55202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55202 s i)) at 1.
  unfold R.v55202, N.v55202.
  rewrite ?node_8279.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55203 (s : N.State) (i : N.Inputs) :
  R.v55203 (state s) (inputs i) = Zmod.unsigned (N.v55203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55203 s i)) at 1.
  unfold R.v55203, N.v55203.
  unfold R.v6, N.v6.
  rewrite ?node_8411.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55204 (s : N.State) (i : N.Inputs) :
  R.v55204 (state s) (inputs i) = Zmod.unsigned (N.v55204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55204 s i)) at 1.
  unfold R.v55204, N.v55204.
  rewrite ?node_55202.
  rewrite ?node_55203.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55205 (s : N.State) (i : N.Inputs) :
  R.v55205 (state s) (inputs i) = Zmod.unsigned (N.v55205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55205 s i)) at 1.
  unfold R.v55205, N.v55205.
  rewrite ?node_55201.
  rewrite ?node_55204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55206 (s : N.State) (i : N.Inputs) :
  R.v55206 (state s) (inputs i) = Zmod.unsigned (N.v55206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55206 s i)) at 1.
  unfold R.v55206, N.v55206.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55207 (s : N.State) (i : N.Inputs) :
  R.v55207 (state s) (inputs i) = Zmod.unsigned (N.v55207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55207 s i)) at 1.
  unfold R.v55207, N.v55207.
  rewrite ?node_8286.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55208 (s : N.State) (i : N.Inputs) :
  R.v55208 (state s) (inputs i) = Zmod.unsigned (N.v55208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55208 s i)) at 1.
  unfold R.v55208, N.v55208.
  unfold R.v6, N.v6.
  rewrite ?node_8282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55209 (s : N.State) (i : N.Inputs) :
  R.v55209 (state s) (inputs i) = Zmod.unsigned (N.v55209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55209 s i)) at 1.
  unfold R.v55209, N.v55209.
  unfold R.v6, N.v6.
  rewrite ?node_8279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55210 (s : N.State) (i : N.Inputs) :
  R.v55210 (state s) (inputs i) = Zmod.unsigned (N.v55210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55210 s i)) at 1.
  unfold R.v55210, N.v55210.
  rewrite ?node_55208.
  rewrite ?node_55209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55211 (s : N.State) (i : N.Inputs) :
  R.v55211 (state s) (inputs i) = Zmod.unsigned (N.v55211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55211 s i)) at 1.
  unfold R.v55211, N.v55211.
  unfold R.v16484, N.v16484.
  rewrite ?node_55210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55212 (s : N.State) (i : N.Inputs) :
  R.v55212 (state s) (inputs i) = Zmod.unsigned (N.v55212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55212 s i)) at 1.
  unfold R.v55212, N.v55212.
  rewrite ?node_55207.
  rewrite ?node_55211.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55213 (s : N.State) (i : N.Inputs) :
  R.v55213 (state s) (inputs i) = Zmod.unsigned (N.v55213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55213 s i)) at 1.
  unfold R.v55213, N.v55213.
  unfold R.v6, N.v6.
  rewrite ?node_55212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55214 (s : N.State) (i : N.Inputs) :
  R.v55214 (state s) (inputs i) = Zmod.unsigned (N.v55214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55214 s i)) at 1.
  unfold R.v55214, N.v55214.
  rewrite ?node_8287.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55215 (s : N.State) (i : N.Inputs) :
  R.v55215 (state s) (inputs i) = Zmod.unsigned (N.v55215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55215 s i)) at 1.
  unfold R.v55215, N.v55215.
  unfold R.v6, N.v6.
  rewrite ?node_8415.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55216 (s : N.State) (i : N.Inputs) :
  R.v55216 (state s) (inputs i) = Zmod.unsigned (N.v55216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55216 s i)) at 1.
  unfold R.v55216, N.v55216.
  rewrite ?node_55214.
  rewrite ?node_55215.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55217 (s : N.State) (i : N.Inputs) :
  R.v55217 (state s) (inputs i) = Zmod.unsigned (N.v55217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55217 s i)) at 1.
  unfold R.v55217, N.v55217.
  rewrite ?node_55213.
  rewrite ?node_55216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55218 (s : N.State) (i : N.Inputs) :
  R.v55218 (state s) (inputs i) = Zmod.unsigned (N.v55218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55218 s i)) at 1.
  unfold R.v55218, N.v55218.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55219 (s : N.State) (i : N.Inputs) :
  R.v55219 (state s) (inputs i) = Zmod.unsigned (N.v55219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55219 s i)) at 1.
  unfold R.v55219, N.v55219.
  rewrite ?node_8411.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55220 (s : N.State) (i : N.Inputs) :
  R.v55220 (state s) (inputs i) = Zmod.unsigned (N.v55220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55220 s i)) at 1.
  unfold R.v55220, N.v55220.
  rewrite ?node_8407.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55221 (s : N.State) (i : N.Inputs) :
  R.v55221 (state s) (inputs i) = Zmod.unsigned (N.v55221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55221 s i)) at 1.
  unfold R.v55221, N.v55221.
  rewrite ?node_8403.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55222 (s : N.State) (i : N.Inputs) :
  R.v55222 (state s) (inputs i) = Zmod.unsigned (N.v55222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55222 s i)) at 1.
  unfold R.v55222, N.v55222.
  unfold R.v6, N.v6.
  rewrite ?node_8399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55223 (s : N.State) (i : N.Inputs) :
  R.v55223 (state s) (inputs i) = Zmod.unsigned (N.v55223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55223 s i)) at 1.
  unfold R.v55223, N.v55223.
  unfold R.v6, N.v6.
  rewrite ?node_8386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55224 (s : N.State) (i : N.Inputs) :
  R.v55224 (state s) (inputs i) = Zmod.unsigned (N.v55224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55224 s i)) at 1.
  unfold R.v55224, N.v55224.
  rewrite ?node_55222.
  rewrite ?node_55223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55225 (s : N.State) (i : N.Inputs) :
  R.v55225 (state s) (inputs i) = Zmod.unsigned (N.v55225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55225 s i)) at 1.
  unfold R.v55225, N.v55225.
  unfold R.v16484, N.v16484.
  rewrite ?node_55224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55226 (s : N.State) (i : N.Inputs) :
  R.v55226 (state s) (inputs i) = Zmod.unsigned (N.v55226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55226 s i)) at 1.
  unfold R.v55226, N.v55226.
  rewrite ?node_55219.
  rewrite ?node_55220.
  rewrite ?node_55221.
  rewrite ?node_55225.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55227 (s : N.State) (i : N.Inputs) :
  R.v55227 (state s) (inputs i) = Zmod.unsigned (N.v55227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55227 s i)) at 1.
  unfold R.v55227, N.v55227.
  unfold R.v6, N.v6.
  rewrite ?node_55226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55228 (s : N.State) (i : N.Inputs) :
  R.v55228 (state s) (inputs i) = Zmod.unsigned (N.v55228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55228 s i)) at 1.
  unfold R.v55228, N.v55228.
  rewrite ?node_8412.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55229 (s : N.State) (i : N.Inputs) :
  R.v55229 (state s) (inputs i) = Zmod.unsigned (N.v55229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55229 s i)) at 1.
  unfold R.v55229, N.v55229.
  unfold R.v6, N.v6.
  rewrite ?node_8540.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55230 (s : N.State) (i : N.Inputs) :
  R.v55230 (state s) (inputs i) = Zmod.unsigned (N.v55230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55230 s i)) at 1.
  unfold R.v55230, N.v55230.
  unfold R.v6, N.v6.
  rewrite ?node_8544.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55231 (s : N.State) (i : N.Inputs) :
  R.v55231 (state s) (inputs i) = Zmod.unsigned (N.v55231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55231 s i)) at 1.
  unfold R.v55231, N.v55231.
  rewrite ?node_55228.
  rewrite ?node_55229.
  rewrite ?node_55230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55232 (s : N.State) (i : N.Inputs) :
  R.v55232 (state s) (inputs i) = Zmod.unsigned (N.v55232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55232 s i)) at 1.
  unfold R.v55232, N.v55232.
  rewrite ?node_55227.
  rewrite ?node_55231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55233 (s : N.State) (i : N.Inputs) :
  R.v55233 (state s) (inputs i) = Zmod.unsigned (N.v55233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55233 s i)) at 1.
  unfold R.v55233, N.v55233.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55234 (s : N.State) (i : N.Inputs) :
  R.v55234 (state s) (inputs i) = Zmod.unsigned (N.v55234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55234 s i)) at 1.
  unfold R.v55234, N.v55234.
  rewrite ?node_8403.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55235 (s : N.State) (i : N.Inputs) :
  R.v55235 (state s) (inputs i) = Zmod.unsigned (N.v55235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55235 s i)) at 1.
  unfold R.v55235, N.v55235.
  unfold R.v6, N.v6.
  rewrite ?node_8399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55236 (s : N.State) (i : N.Inputs) :
  R.v55236 (state s) (inputs i) = Zmod.unsigned (N.v55236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55236 s i)) at 1.
  unfold R.v55236, N.v55236.
  unfold R.v6, N.v6.
  rewrite ?node_8386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55237 (s : N.State) (i : N.Inputs) :
  R.v55237 (state s) (inputs i) = Zmod.unsigned (N.v55237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55237 s i)) at 1.
  unfold R.v55237, N.v55237.
  rewrite ?node_55235.
  rewrite ?node_55236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55238 (s : N.State) (i : N.Inputs) :
  R.v55238 (state s) (inputs i) = Zmod.unsigned (N.v55238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55238 s i)) at 1.
  unfold R.v55238, N.v55238.
  unfold R.v16484, N.v16484.
  rewrite ?node_55237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55239 (s : N.State) (i : N.Inputs) :
  R.v55239 (state s) (inputs i) = Zmod.unsigned (N.v55239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55239 s i)) at 1.
  unfold R.v55239, N.v55239.
  rewrite ?node_55234.
  rewrite ?node_55238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55240 (s : N.State) (i : N.Inputs) :
  R.v55240 (state s) (inputs i) = Zmod.unsigned (N.v55240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55240 s i)) at 1.
  unfold R.v55240, N.v55240.
  unfold R.v6, N.v6.
  rewrite ?node_55239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55241 (s : N.State) (i : N.Inputs) :
  R.v55241 (state s) (inputs i) = Zmod.unsigned (N.v55241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55241 s i)) at 1.
  unfold R.v55241, N.v55241.
  rewrite ?node_8404.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55242 (s : N.State) (i : N.Inputs) :
  R.v55242 (state s) (inputs i) = Zmod.unsigned (N.v55242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55242 s i)) at 1.
  unfold R.v55242, N.v55242.
  unfold R.v6, N.v6.
  rewrite ?node_8540.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55243 (s : N.State) (i : N.Inputs) :
  R.v55243 (state s) (inputs i) = Zmod.unsigned (N.v55243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55243 s i)) at 1.
  unfold R.v55243, N.v55243.
  rewrite ?node_55241.
  rewrite ?node_55242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55244 (s : N.State) (i : N.Inputs) :
  R.v55244 (state s) (inputs i) = Zmod.unsigned (N.v55244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55244 s i)) at 1.
  unfold R.v55244, N.v55244.
  rewrite ?node_55240.
  rewrite ?node_55243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55245 (s : N.State) (i : N.Inputs) :
  R.v55245 (state s) (inputs i) = Zmod.unsigned (N.v55245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55245 s i)) at 1.
  unfold R.v55245, N.v55245.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55246 (s : N.State) (i : N.Inputs) :
  R.v55246 (state s) (inputs i) = Zmod.unsigned (N.v55246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55246 s i)) at 1.
  unfold R.v55246, N.v55246.
  rewrite ?node_8411.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55247 (s : N.State) (i : N.Inputs) :
  R.v55247 (state s) (inputs i) = Zmod.unsigned (N.v55247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55247 s i)) at 1.
  unfold R.v55247, N.v55247.
  unfold R.v6, N.v6.
  rewrite ?node_8407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55248 (s : N.State) (i : N.Inputs) :
  R.v55248 (state s) (inputs i) = Zmod.unsigned (N.v55248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55248 s i)) at 1.
  unfold R.v55248, N.v55248.
  unfold R.v6, N.v6.
  rewrite ?node_8404.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55249 (s : N.State) (i : N.Inputs) :
  R.v55249 (state s) (inputs i) = Zmod.unsigned (N.v55249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55249 s i)) at 1.
  unfold R.v55249, N.v55249.
  rewrite ?node_55247.
  rewrite ?node_55248.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55250 (s : N.State) (i : N.Inputs) :
  R.v55250 (state s) (inputs i) = Zmod.unsigned (N.v55250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55250 s i)) at 1.
  unfold R.v55250, N.v55250.
  unfold R.v16484, N.v16484.
  rewrite ?node_55249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55251 (s : N.State) (i : N.Inputs) :
  R.v55251 (state s) (inputs i) = Zmod.unsigned (N.v55251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55251 s i)) at 1.
  unfold R.v55251, N.v55251.
  rewrite ?node_55246.
  rewrite ?node_55250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55252 (s : N.State) (i : N.Inputs) :
  R.v55252 (state s) (inputs i) = Zmod.unsigned (N.v55252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55252 s i)) at 1.
  unfold R.v55252, N.v55252.
  unfold R.v6, N.v6.
  rewrite ?node_55251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55253 (s : N.State) (i : N.Inputs) :
  R.v55253 (state s) (inputs i) = Zmod.unsigned (N.v55253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55253 s i)) at 1.
  unfold R.v55253, N.v55253.
  rewrite ?node_8412.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55254 (s : N.State) (i : N.Inputs) :
  R.v55254 (state s) (inputs i) = Zmod.unsigned (N.v55254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55254 s i)) at 1.
  unfold R.v55254, N.v55254.
  unfold R.v6, N.v6.
  rewrite ?node_8544.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55255 (s : N.State) (i : N.Inputs) :
  R.v55255 (state s) (inputs i) = Zmod.unsigned (N.v55255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55255 s i)) at 1.
  unfold R.v55255, N.v55255.
  rewrite ?node_55253.
  rewrite ?node_55254.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55256 (s : N.State) (i : N.Inputs) :
  R.v55256 (state s) (inputs i) = Zmod.unsigned (N.v55256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55256 s i)) at 1.
  unfold R.v55256, N.v55256.
  rewrite ?node_55252.
  rewrite ?node_55255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55257 (s : N.State) (i : N.Inputs) :
  R.v55257 (state s) (inputs i) = Zmod.unsigned (N.v55257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55257 s i)) at 1.
  unfold R.v55257, N.v55257.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55258 (s : N.State) (i : N.Inputs) :
  R.v55258 (state s) (inputs i) = Zmod.unsigned (N.v55258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55258 s i)) at 1.
  unfold R.v55258, N.v55258.
  rewrite ?node_8540.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55259 (s : N.State) (i : N.Inputs) :
  R.v55259 (state s) (inputs i) = Zmod.unsigned (N.v55259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55259 s i)) at 1.
  unfold R.v55259, N.v55259.
  rewrite ?node_8536.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55260 (s : N.State) (i : N.Inputs) :
  R.v55260 (state s) (inputs i) = Zmod.unsigned (N.v55260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55260 s i)) at 1.
  unfold R.v55260, N.v55260.
  rewrite ?node_8534.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55261 (s : N.State) (i : N.Inputs) :
  R.v55261 (state s) (inputs i) = Zmod.unsigned (N.v55261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55261 s i)) at 1.
  unfold R.v55261, N.v55261.
  unfold R.v6, N.v6.
  rewrite ?node_8530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55262 (s : N.State) (i : N.Inputs) :
  R.v55262 (state s) (inputs i) = Zmod.unsigned (N.v55262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55262 s i)) at 1.
  unfold R.v55262, N.v55262.
  unfold R.v6, N.v6.
  rewrite ?node_8513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55263 (s : N.State) (i : N.Inputs) :
  R.v55263 (state s) (inputs i) = Zmod.unsigned (N.v55263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55263 s i)) at 1.
  unfold R.v55263, N.v55263.
  rewrite ?node_55261.
  rewrite ?node_55262.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55264 (s : N.State) (i : N.Inputs) :
  R.v55264 (state s) (inputs i) = Zmod.unsigned (N.v55264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55264 s i)) at 1.
  unfold R.v55264, N.v55264.
  unfold R.v16484, N.v16484.
  rewrite ?node_55263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55265 (s : N.State) (i : N.Inputs) :
  R.v55265 (state s) (inputs i) = Zmod.unsigned (N.v55265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55265 s i)) at 1.
  unfold R.v55265, N.v55265.
  rewrite ?node_55258.
  rewrite ?node_55259.
  rewrite ?node_55260.
  rewrite ?node_55264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55266 (s : N.State) (i : N.Inputs) :
  R.v55266 (state s) (inputs i) = Zmod.unsigned (N.v55266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55266 s i)) at 1.
  unfold R.v55266, N.v55266.
  unfold R.v6, N.v6.
  rewrite ?node_55265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55267 (s : N.State) (i : N.Inputs) :
  R.v55267 (state s) (inputs i) = Zmod.unsigned (N.v55267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55267 s i)) at 1.
  unfold R.v55267, N.v55267.
  rewrite ?node_8541.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55268 (s : N.State) (i : N.Inputs) :
  R.v55268 (state s) (inputs i) = Zmod.unsigned (N.v55268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55268 s i)) at 1.
  unfold R.v55268, N.v55268.
  unfold R.v6, N.v6.
  rewrite ?node_8672.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55269 (s : N.State) (i : N.Inputs) :
  R.v55269 (state s) (inputs i) = Zmod.unsigned (N.v55269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55269 s i)) at 1.
  unfold R.v55269, N.v55269.
  unfold R.v6, N.v6.
  rewrite ?node_8676.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55270 (s : N.State) (i : N.Inputs) :
  R.v55270 (state s) (inputs i) = Zmod.unsigned (N.v55270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55270 s i)) at 1.
  unfold R.v55270, N.v55270.
  rewrite ?node_55267.
  rewrite ?node_55268.
  rewrite ?node_55269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55271 (s : N.State) (i : N.Inputs) :
  R.v55271 (state s) (inputs i) = Zmod.unsigned (N.v55271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55271 s i)) at 1.
  unfold R.v55271, N.v55271.
  rewrite ?node_55266.
  rewrite ?node_55270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55272 (s : N.State) (i : N.Inputs) :
  R.v55272 (state s) (inputs i) = Zmod.unsigned (N.v55272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55272 s i)) at 1.
  unfold R.v55272, N.v55272.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55273 (s : N.State) (i : N.Inputs) :
  R.v55273 (state s) (inputs i) = Zmod.unsigned (N.v55273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55273 s i)) at 1.
  unfold R.v55273, N.v55273.
  rewrite ?node_8534.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55274 (s : N.State) (i : N.Inputs) :
  R.v55274 (state s) (inputs i) = Zmod.unsigned (N.v55274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55274 s i)) at 1.
  unfold R.v55274, N.v55274.
  unfold R.v6, N.v6.
  rewrite ?node_8530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55275 (s : N.State) (i : N.Inputs) :
  R.v55275 (state s) (inputs i) = Zmod.unsigned (N.v55275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55275 s i)) at 1.
  unfold R.v55275, N.v55275.
  unfold R.v6, N.v6.
  rewrite ?node_8513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55276 (s : N.State) (i : N.Inputs) :
  R.v55276 (state s) (inputs i) = Zmod.unsigned (N.v55276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55276 s i)) at 1.
  unfold R.v55276, N.v55276.
  rewrite ?node_55274.
  rewrite ?node_55275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55277 (s : N.State) (i : N.Inputs) :
  R.v55277 (state s) (inputs i) = Zmod.unsigned (N.v55277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55277 s i)) at 1.
  unfold R.v55277, N.v55277.
  unfold R.v16484, N.v16484.
  rewrite ?node_55276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55278 (s : N.State) (i : N.Inputs) :
  R.v55278 (state s) (inputs i) = Zmod.unsigned (N.v55278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55278 s i)) at 1.
  unfold R.v55278, N.v55278.
  rewrite ?node_55273.
  rewrite ?node_55277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55279 (s : N.State) (i : N.Inputs) :
  R.v55279 (state s) (inputs i) = Zmod.unsigned (N.v55279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55279 s i)) at 1.
  unfold R.v55279, N.v55279.
  unfold R.v6, N.v6.
  rewrite ?node_55278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55280 (s : N.State) (i : N.Inputs) :
  R.v55280 (state s) (inputs i) = Zmod.unsigned (N.v55280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55280 s i)) at 1.
  unfold R.v55280, N.v55280.
  rewrite ?node_8535.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55281 (s : N.State) (i : N.Inputs) :
  R.v55281 (state s) (inputs i) = Zmod.unsigned (N.v55281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55281 s i)) at 1.
  unfold R.v55281, N.v55281.
  unfold R.v6, N.v6.
  rewrite ?node_8672.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55282 (s : N.State) (i : N.Inputs) :
  R.v55282 (state s) (inputs i) = Zmod.unsigned (N.v55282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55282 s i)) at 1.
  unfold R.v55282, N.v55282.
  rewrite ?node_55280.
  rewrite ?node_55281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55283 (s : N.State) (i : N.Inputs) :
  R.v55283 (state s) (inputs i) = Zmod.unsigned (N.v55283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55283 s i)) at 1.
  unfold R.v55283, N.v55283.
  rewrite ?node_55279.
  rewrite ?node_55282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55284 (s : N.State) (i : N.Inputs) :
  R.v55284 (state s) (inputs i) = Zmod.unsigned (N.v55284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55284 s i)) at 1.
  unfold R.v55284, N.v55284.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55285 (s : N.State) (i : N.Inputs) :
  R.v55285 (state s) (inputs i) = Zmod.unsigned (N.v55285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55285 s i)) at 1.
  unfold R.v55285, N.v55285.
  rewrite ?node_8540.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55286 (s : N.State) (i : N.Inputs) :
  R.v55286 (state s) (inputs i) = Zmod.unsigned (N.v55286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55286 s i)) at 1.
  unfold R.v55286, N.v55286.
  unfold R.v6, N.v6.
  rewrite ?node_8536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55287 (s : N.State) (i : N.Inputs) :
  R.v55287 (state s) (inputs i) = Zmod.unsigned (N.v55287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55287 s i)) at 1.
  unfold R.v55287, N.v55287.
  unfold R.v6, N.v6.
  rewrite ?node_8535.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55288 (s : N.State) (i : N.Inputs) :
  R.v55288 (state s) (inputs i) = Zmod.unsigned (N.v55288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55288 s i)) at 1.
  unfold R.v55288, N.v55288.
  rewrite ?node_55286.
  rewrite ?node_55287.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55289 (s : N.State) (i : N.Inputs) :
  R.v55289 (state s) (inputs i) = Zmod.unsigned (N.v55289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55289 s i)) at 1.
  unfold R.v55289, N.v55289.
  unfold R.v16484, N.v16484.
  rewrite ?node_55288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55290 (s : N.State) (i : N.Inputs) :
  R.v55290 (state s) (inputs i) = Zmod.unsigned (N.v55290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55290 s i)) at 1.
  unfold R.v55290, N.v55290.
  rewrite ?node_55285.
  rewrite ?node_55289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55291 (s : N.State) (i : N.Inputs) :
  R.v55291 (state s) (inputs i) = Zmod.unsigned (N.v55291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55291 s i)) at 1.
  unfold R.v55291, N.v55291.
  unfold R.v6, N.v6.
  rewrite ?node_55290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55292 (s : N.State) (i : N.Inputs) :
  R.v55292 (state s) (inputs i) = Zmod.unsigned (N.v55292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55292 s i)) at 1.
  unfold R.v55292, N.v55292.
  rewrite ?node_8541.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55293 (s : N.State) (i : N.Inputs) :
  R.v55293 (state s) (inputs i) = Zmod.unsigned (N.v55293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55293 s i)) at 1.
  unfold R.v55293, N.v55293.
  unfold R.v6, N.v6.
  rewrite ?node_8676.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55294 (s : N.State) (i : N.Inputs) :
  R.v55294 (state s) (inputs i) = Zmod.unsigned (N.v55294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55294 s i)) at 1.
  unfold R.v55294, N.v55294.
  rewrite ?node_55292.
  rewrite ?node_55293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55295 (s : N.State) (i : N.Inputs) :
  R.v55295 (state s) (inputs i) = Zmod.unsigned (N.v55295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55295 s i)) at 1.
  unfold R.v55295, N.v55295.
  rewrite ?node_55291.
  rewrite ?node_55294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55296 (s : N.State) (i : N.Inputs) :
  R.v55296 (state s) (inputs i) = Zmod.unsigned (N.v55296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55296 s i)) at 1.
  unfold R.v55296, N.v55296.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55297 (s : N.State) (i : N.Inputs) :
  R.v55297 (state s) (inputs i) = Zmod.unsigned (N.v55297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55297 s i)) at 1.
  unfold R.v55297, N.v55297.
  rewrite ?node_8672.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55298 (s : N.State) (i : N.Inputs) :
  R.v55298 (state s) (inputs i) = Zmod.unsigned (N.v55298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55298 s i)) at 1.
  unfold R.v55298, N.v55298.
  rewrite ?node_8668.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55299 (s : N.State) (i : N.Inputs) :
  R.v55299 (state s) (inputs i) = Zmod.unsigned (N.v55299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55299 s i)) at 1.
  unfold R.v55299, N.v55299.
  rewrite ?node_8664.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55300 (s : N.State) (i : N.Inputs) :
  R.v55300 (state s) (inputs i) = Zmod.unsigned (N.v55300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55300 s i)) at 1.
  unfold R.v55300, N.v55300.
  unfold R.v6, N.v6.
  rewrite ?node_8660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55301 (s : N.State) (i : N.Inputs) :
  R.v55301 (state s) (inputs i) = Zmod.unsigned (N.v55301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55301 s i)) at 1.
  unfold R.v55301, N.v55301.
  unfold R.v6, N.v6.
  rewrite ?node_8643.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55302 (s : N.State) (i : N.Inputs) :
  R.v55302 (state s) (inputs i) = Zmod.unsigned (N.v55302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55302 s i)) at 1.
  unfold R.v55302, N.v55302.
  rewrite ?node_55300.
  rewrite ?node_55301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55303 (s : N.State) (i : N.Inputs) :
  R.v55303 (state s) (inputs i) = Zmod.unsigned (N.v55303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55303 s i)) at 1.
  unfold R.v55303, N.v55303.
  unfold R.v16484, N.v16484.
  rewrite ?node_55302.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55304 (s : N.State) (i : N.Inputs) :
  R.v55304 (state s) (inputs i) = Zmod.unsigned (N.v55304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55304 s i)) at 1.
  unfold R.v55304, N.v55304.
  rewrite ?node_55297.
  rewrite ?node_55298.
  rewrite ?node_55299.
  rewrite ?node_55303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55305 (s : N.State) (i : N.Inputs) :
  R.v55305 (state s) (inputs i) = Zmod.unsigned (N.v55305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55305 s i)) at 1.
  unfold R.v55305, N.v55305.
  unfold R.v6, N.v6.
  rewrite ?node_55304.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55306 (s : N.State) (i : N.Inputs) :
  R.v55306 (state s) (inputs i) = Zmod.unsigned (N.v55306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55306 s i)) at 1.
  unfold R.v55306, N.v55306.
  rewrite ?node_8673.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55307 (s : N.State) (i : N.Inputs) :
  R.v55307 (state s) (inputs i) = Zmod.unsigned (N.v55307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55307 s i)) at 1.
  unfold R.v55307, N.v55307.
  unfold R.v6, N.v6.
  rewrite ?node_8806.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55308 (s : N.State) (i : N.Inputs) :
  R.v55308 (state s) (inputs i) = Zmod.unsigned (N.v55308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55308 s i)) at 1.
  unfold R.v55308, N.v55308.
  unfold R.v6, N.v6.
  rewrite ?node_8810.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55309 (s : N.State) (i : N.Inputs) :
  R.v55309 (state s) (inputs i) = Zmod.unsigned (N.v55309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55309 s i)) at 1.
  unfold R.v55309, N.v55309.
  rewrite ?node_55306.
  rewrite ?node_55307.
  rewrite ?node_55308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55310 (s : N.State) (i : N.Inputs) :
  R.v55310 (state s) (inputs i) = Zmod.unsigned (N.v55310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55310 s i)) at 1.
  unfold R.v55310, N.v55310.
  rewrite ?node_55305.
  rewrite ?node_55309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55311 (s : N.State) (i : N.Inputs) :
  R.v55311 (state s) (inputs i) = Zmod.unsigned (N.v55311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55311 s i)) at 1.
  unfold R.v55311, N.v55311.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55312 (s : N.State) (i : N.Inputs) :
  R.v55312 (state s) (inputs i) = Zmod.unsigned (N.v55312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55312 s i)) at 1.
  unfold R.v55312, N.v55312.
  rewrite ?node_8664.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55313 (s : N.State) (i : N.Inputs) :
  R.v55313 (state s) (inputs i) = Zmod.unsigned (N.v55313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55313 s i)) at 1.
  unfold R.v55313, N.v55313.
  unfold R.v6, N.v6.
  rewrite ?node_8660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55314 (s : N.State) (i : N.Inputs) :
  R.v55314 (state s) (inputs i) = Zmod.unsigned (N.v55314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55314 s i)) at 1.
  unfold R.v55314, N.v55314.
  unfold R.v6, N.v6.
  rewrite ?node_8643.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55315 (s : N.State) (i : N.Inputs) :
  R.v55315 (state s) (inputs i) = Zmod.unsigned (N.v55315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55315 s i)) at 1.
  unfold R.v55315, N.v55315.
  rewrite ?node_55313.
  rewrite ?node_55314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55316 (s : N.State) (i : N.Inputs) :
  R.v55316 (state s) (inputs i) = Zmod.unsigned (N.v55316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55316 s i)) at 1.
  unfold R.v55316, N.v55316.
  unfold R.v16484, N.v16484.
  rewrite ?node_55315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55317 (s : N.State) (i : N.Inputs) :
  R.v55317 (state s) (inputs i) = Zmod.unsigned (N.v55317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55317 s i)) at 1.
  unfold R.v55317, N.v55317.
  rewrite ?node_55312.
  rewrite ?node_55316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55318 (s : N.State) (i : N.Inputs) :
  R.v55318 (state s) (inputs i) = Zmod.unsigned (N.v55318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55318 s i)) at 1.
  unfold R.v55318, N.v55318.
  unfold R.v6, N.v6.
  rewrite ?node_55317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55319 (s : N.State) (i : N.Inputs) :
  R.v55319 (state s) (inputs i) = Zmod.unsigned (N.v55319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55319 s i)) at 1.
  unfold R.v55319, N.v55319.
  rewrite ?node_8665.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55320 (s : N.State) (i : N.Inputs) :
  R.v55320 (state s) (inputs i) = Zmod.unsigned (N.v55320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55320 s i)) at 1.
  unfold R.v55320, N.v55320.
  unfold R.v6, N.v6.
  rewrite ?node_8806.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55321 (s : N.State) (i : N.Inputs) :
  R.v55321 (state s) (inputs i) = Zmod.unsigned (N.v55321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55321 s i)) at 1.
  unfold R.v55321, N.v55321.
  rewrite ?node_55319.
  rewrite ?node_55320.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55322 (s : N.State) (i : N.Inputs) :
  R.v55322 (state s) (inputs i) = Zmod.unsigned (N.v55322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55322 s i)) at 1.
  unfold R.v55322, N.v55322.
  rewrite ?node_55318.
  rewrite ?node_55321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55323 (s : N.State) (i : N.Inputs) :
  R.v55323 (state s) (inputs i) = Zmod.unsigned (N.v55323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55323 s i)) at 1.
  unfold R.v55323, N.v55323.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55324 (s : N.State) (i : N.Inputs) :
  R.v55324 (state s) (inputs i) = Zmod.unsigned (N.v55324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55324 s i)) at 1.
  unfold R.v55324, N.v55324.
  rewrite ?node_8672.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55325 (s : N.State) (i : N.Inputs) :
  R.v55325 (state s) (inputs i) = Zmod.unsigned (N.v55325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55325 s i)) at 1.
  unfold R.v55325, N.v55325.
  unfold R.v6, N.v6.
  rewrite ?node_8668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55326 (s : N.State) (i : N.Inputs) :
  R.v55326 (state s) (inputs i) = Zmod.unsigned (N.v55326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55326 s i)) at 1.
  unfold R.v55326, N.v55326.
  unfold R.v6, N.v6.
  rewrite ?node_8665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55327 (s : N.State) (i : N.Inputs) :
  R.v55327 (state s) (inputs i) = Zmod.unsigned (N.v55327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55327 s i)) at 1.
  unfold R.v55327, N.v55327.
  rewrite ?node_55325.
  rewrite ?node_55326.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55328 (s : N.State) (i : N.Inputs) :
  R.v55328 (state s) (inputs i) = Zmod.unsigned (N.v55328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55328 s i)) at 1.
  unfold R.v55328, N.v55328.
  unfold R.v16484, N.v16484.
  rewrite ?node_55327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55329 (s : N.State) (i : N.Inputs) :
  R.v55329 (state s) (inputs i) = Zmod.unsigned (N.v55329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55329 s i)) at 1.
  unfold R.v55329, N.v55329.
  rewrite ?node_55324.
  rewrite ?node_55328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55330 (s : N.State) (i : N.Inputs) :
  R.v55330 (state s) (inputs i) = Zmod.unsigned (N.v55330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55330 s i)) at 1.
  unfold R.v55330, N.v55330.
  unfold R.v6, N.v6.
  rewrite ?node_55329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55331 (s : N.State) (i : N.Inputs) :
  R.v55331 (state s) (inputs i) = Zmod.unsigned (N.v55331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55331 s i)) at 1.
  unfold R.v55331, N.v55331.
  rewrite ?node_8673.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55332 (s : N.State) (i : N.Inputs) :
  R.v55332 (state s) (inputs i) = Zmod.unsigned (N.v55332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55332 s i)) at 1.
  unfold R.v55332, N.v55332.
  unfold R.v6, N.v6.
  rewrite ?node_8810.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55333 (s : N.State) (i : N.Inputs) :
  R.v55333 (state s) (inputs i) = Zmod.unsigned (N.v55333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55333 s i)) at 1.
  unfold R.v55333, N.v55333.
  rewrite ?node_55331.
  rewrite ?node_55332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55334 (s : N.State) (i : N.Inputs) :
  R.v55334 (state s) (inputs i) = Zmod.unsigned (N.v55334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55334 s i)) at 1.
  unfold R.v55334, N.v55334.
  rewrite ?node_55330.
  rewrite ?node_55333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55335 (s : N.State) (i : N.Inputs) :
  R.v55335 (state s) (inputs i) = Zmod.unsigned (N.v55335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55335 s i)) at 1.
  unfold R.v55335, N.v55335.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55336 (s : N.State) (i : N.Inputs) :
  R.v55336 (state s) (inputs i) = Zmod.unsigned (N.v55336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55336 s i)) at 1.
  unfold R.v55336, N.v55336.
  rewrite ?node_8806.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55337 (s : N.State) (i : N.Inputs) :
  R.v55337 (state s) (inputs i) = Zmod.unsigned (N.v55337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55337 s i)) at 1.
  unfold R.v55337, N.v55337.
  rewrite ?node_8802.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55338 (s : N.State) (i : N.Inputs) :
  R.v55338 (state s) (inputs i) = Zmod.unsigned (N.v55338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55338 s i)) at 1.
  unfold R.v55338, N.v55338.
  rewrite ?node_8798.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55339 (s : N.State) (i : N.Inputs) :
  R.v55339 (state s) (inputs i) = Zmod.unsigned (N.v55339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55339 s i)) at 1.
  unfold R.v55339, N.v55339.
  unfold R.v6, N.v6.
  rewrite ?node_8794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55340 (s : N.State) (i : N.Inputs) :
  R.v55340 (state s) (inputs i) = Zmod.unsigned (N.v55340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55340 s i)) at 1.
  unfold R.v55340, N.v55340.
  unfold R.v6, N.v6.
  rewrite ?node_8777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55341 (s : N.State) (i : N.Inputs) :
  R.v55341 (state s) (inputs i) = Zmod.unsigned (N.v55341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55341 s i)) at 1.
  unfold R.v55341, N.v55341.
  rewrite ?node_55339.
  rewrite ?node_55340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55342 (s : N.State) (i : N.Inputs) :
  R.v55342 (state s) (inputs i) = Zmod.unsigned (N.v55342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55342 s i)) at 1.
  unfold R.v55342, N.v55342.
  unfold R.v16484, N.v16484.
  rewrite ?node_55341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55343 (s : N.State) (i : N.Inputs) :
  R.v55343 (state s) (inputs i) = Zmod.unsigned (N.v55343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55343 s i)) at 1.
  unfold R.v55343, N.v55343.
  rewrite ?node_55336.
  rewrite ?node_55337.
  rewrite ?node_55338.
  rewrite ?node_55342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55344 (s : N.State) (i : N.Inputs) :
  R.v55344 (state s) (inputs i) = Zmod.unsigned (N.v55344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55344 s i)) at 1.
  unfold R.v55344, N.v55344.
  unfold R.v6, N.v6.
  rewrite ?node_55343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55345 (s : N.State) (i : N.Inputs) :
  R.v55345 (state s) (inputs i) = Zmod.unsigned (N.v55345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55345 s i)) at 1.
  unfold R.v55345, N.v55345.
  rewrite ?node_8807.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55346 (s : N.State) (i : N.Inputs) :
  R.v55346 (state s) (inputs i) = Zmod.unsigned (N.v55346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55346 s i)) at 1.
  unfold R.v55346, N.v55346.
  unfold R.v6, N.v6.
  rewrite ?node_8943.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55347 (s : N.State) (i : N.Inputs) :
  R.v55347 (state s) (inputs i) = Zmod.unsigned (N.v55347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55347 s i)) at 1.
  unfold R.v55347, N.v55347.
  unfold R.v6, N.v6.
  rewrite ?node_8947.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55348 (s : N.State) (i : N.Inputs) :
  R.v55348 (state s) (inputs i) = Zmod.unsigned (N.v55348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55348 s i)) at 1.
  unfold R.v55348, N.v55348.
  rewrite ?node_55345.
  rewrite ?node_55346.
  rewrite ?node_55347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55349 (s : N.State) (i : N.Inputs) :
  R.v55349 (state s) (inputs i) = Zmod.unsigned (N.v55349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55349 s i)) at 1.
  unfold R.v55349, N.v55349.
  rewrite ?node_55344.
  rewrite ?node_55348.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55350 (s : N.State) (i : N.Inputs) :
  R.v55350 (state s) (inputs i) = Zmod.unsigned (N.v55350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55350 s i)) at 1.
  unfold R.v55350, N.v55350.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55351 (s : N.State) (i : N.Inputs) :
  R.v55351 (state s) (inputs i) = Zmod.unsigned (N.v55351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55351 s i)) at 1.
  unfold R.v55351, N.v55351.
  rewrite ?node_8798.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55352 (s : N.State) (i : N.Inputs) :
  R.v55352 (state s) (inputs i) = Zmod.unsigned (N.v55352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55352 s i)) at 1.
  unfold R.v55352, N.v55352.
  unfold R.v6, N.v6.
  rewrite ?node_8794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55353 (s : N.State) (i : N.Inputs) :
  R.v55353 (state s) (inputs i) = Zmod.unsigned (N.v55353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55353 s i)) at 1.
  unfold R.v55353, N.v55353.
  unfold R.v6, N.v6.
  rewrite ?node_8777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55354 (s : N.State) (i : N.Inputs) :
  R.v55354 (state s) (inputs i) = Zmod.unsigned (N.v55354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55354 s i)) at 1.
  unfold R.v55354, N.v55354.
  rewrite ?node_55352.
  rewrite ?node_55353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55355 (s : N.State) (i : N.Inputs) :
  R.v55355 (state s) (inputs i) = Zmod.unsigned (N.v55355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55355 s i)) at 1.
  unfold R.v55355, N.v55355.
  unfold R.v16484, N.v16484.
  rewrite ?node_55354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55356 (s : N.State) (i : N.Inputs) :
  R.v55356 (state s) (inputs i) = Zmod.unsigned (N.v55356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55356 s i)) at 1.
  unfold R.v55356, N.v55356.
  rewrite ?node_55351.
  rewrite ?node_55355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55357 (s : N.State) (i : N.Inputs) :
  R.v55357 (state s) (inputs i) = Zmod.unsigned (N.v55357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55357 s i)) at 1.
  unfold R.v55357, N.v55357.
  unfold R.v6, N.v6.
  rewrite ?node_55356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55358 (s : N.State) (i : N.Inputs) :
  R.v55358 (state s) (inputs i) = Zmod.unsigned (N.v55358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55358 s i)) at 1.
  unfold R.v55358, N.v55358.
  rewrite ?node_8799.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55359 (s : N.State) (i : N.Inputs) :
  R.v55359 (state s) (inputs i) = Zmod.unsigned (N.v55359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55359 s i)) at 1.
  unfold R.v55359, N.v55359.
  unfold R.v6, N.v6.
  rewrite ?node_8943.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55360 (s : N.State) (i : N.Inputs) :
  R.v55360 (state s) (inputs i) = Zmod.unsigned (N.v55360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55360 s i)) at 1.
  unfold R.v55360, N.v55360.
  rewrite ?node_55358.
  rewrite ?node_55359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55361 (s : N.State) (i : N.Inputs) :
  R.v55361 (state s) (inputs i) = Zmod.unsigned (N.v55361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55361 s i)) at 1.
  unfold R.v55361, N.v55361.
  rewrite ?node_55357.
  rewrite ?node_55360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55362 (s : N.State) (i : N.Inputs) :
  R.v55362 (state s) (inputs i) = Zmod.unsigned (N.v55362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55362 s i)) at 1.
  unfold R.v55362, N.v55362.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55363 (s : N.State) (i : N.Inputs) :
  R.v55363 (state s) (inputs i) = Zmod.unsigned (N.v55363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55363 s i)) at 1.
  unfold R.v55363, N.v55363.
  rewrite ?node_8806.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55364 (s : N.State) (i : N.Inputs) :
  R.v55364 (state s) (inputs i) = Zmod.unsigned (N.v55364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55364 s i)) at 1.
  unfold R.v55364, N.v55364.
  unfold R.v6, N.v6.
  rewrite ?node_8802.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55365 (s : N.State) (i : N.Inputs) :
  R.v55365 (state s) (inputs i) = Zmod.unsigned (N.v55365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55365 s i)) at 1.
  unfold R.v55365, N.v55365.
  unfold R.v6, N.v6.
  rewrite ?node_8799.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55366 (s : N.State) (i : N.Inputs) :
  R.v55366 (state s) (inputs i) = Zmod.unsigned (N.v55366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55366 s i)) at 1.
  unfold R.v55366, N.v55366.
  rewrite ?node_55364.
  rewrite ?node_55365.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55367 (s : N.State) (i : N.Inputs) :
  R.v55367 (state s) (inputs i) = Zmod.unsigned (N.v55367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55367 s i)) at 1.
  unfold R.v55367, N.v55367.
  unfold R.v16484, N.v16484.
  rewrite ?node_55366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55368 (s : N.State) (i : N.Inputs) :
  R.v55368 (state s) (inputs i) = Zmod.unsigned (N.v55368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55368 s i)) at 1.
  unfold R.v55368, N.v55368.
  rewrite ?node_55363.
  rewrite ?node_55367.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55369 (s : N.State) (i : N.Inputs) :
  R.v55369 (state s) (inputs i) = Zmod.unsigned (N.v55369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55369 s i)) at 1.
  unfold R.v55369, N.v55369.
  unfold R.v6, N.v6.
  rewrite ?node_55368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55370 (s : N.State) (i : N.Inputs) :
  R.v55370 (state s) (inputs i) = Zmod.unsigned (N.v55370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55370 s i)) at 1.
  unfold R.v55370, N.v55370.
  rewrite ?node_8807.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55371 (s : N.State) (i : N.Inputs) :
  R.v55371 (state s) (inputs i) = Zmod.unsigned (N.v55371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55371 s i)) at 1.
  unfold R.v55371, N.v55371.
  unfold R.v6, N.v6.
  rewrite ?node_8947.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55372 (s : N.State) (i : N.Inputs) :
  R.v55372 (state s) (inputs i) = Zmod.unsigned (N.v55372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55372 s i)) at 1.
  unfold R.v55372, N.v55372.
  rewrite ?node_55370.
  rewrite ?node_55371.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55373 (s : N.State) (i : N.Inputs) :
  R.v55373 (state s) (inputs i) = Zmod.unsigned (N.v55373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55373 s i)) at 1.
  unfold R.v55373, N.v55373.
  rewrite ?node_55369.
  rewrite ?node_55372.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55374 (s : N.State) (i : N.Inputs) :
  R.v55374 (state s) (inputs i) = Zmod.unsigned (N.v55374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55374 s i)) at 1.
  unfold R.v55374, N.v55374.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55375 (s : N.State) (i : N.Inputs) :
  R.v55375 (state s) (inputs i) = Zmod.unsigned (N.v55375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55375 s i)) at 1.
  unfold R.v55375, N.v55375.
  rewrite ?node_8943.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55376 (s : N.State) (i : N.Inputs) :
  R.v55376 (state s) (inputs i) = Zmod.unsigned (N.v55376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55376 s i)) at 1.
  unfold R.v55376, N.v55376.
  rewrite ?node_8939.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55377 (s : N.State) (i : N.Inputs) :
  R.v55377 (state s) (inputs i) = Zmod.unsigned (N.v55377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55377 s i)) at 1.
  unfold R.v55377, N.v55377.
  rewrite ?node_8935.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55378 (s : N.State) (i : N.Inputs) :
  R.v55378 (state s) (inputs i) = Zmod.unsigned (N.v55378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55378 s i)) at 1.
  unfold R.v55378, N.v55378.
  unfold R.v6, N.v6.
  rewrite ?node_8931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55379 (s : N.State) (i : N.Inputs) :
  R.v55379 (state s) (inputs i) = Zmod.unsigned (N.v55379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55379 s i)) at 1.
  unfold R.v55379, N.v55379.
  unfold R.v6, N.v6.
  rewrite ?node_8914.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55380 (s : N.State) (i : N.Inputs) :
  R.v55380 (state s) (inputs i) = Zmod.unsigned (N.v55380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55380 s i)) at 1.
  unfold R.v55380, N.v55380.
  rewrite ?node_55378.
  rewrite ?node_55379.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55381 (s : N.State) (i : N.Inputs) :
  R.v55381 (state s) (inputs i) = Zmod.unsigned (N.v55381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55381 s i)) at 1.
  unfold R.v55381, N.v55381.
  unfold R.v16484, N.v16484.
  rewrite ?node_55380.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55382 (s : N.State) (i : N.Inputs) :
  R.v55382 (state s) (inputs i) = Zmod.unsigned (N.v55382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55382 s i)) at 1.
  unfold R.v55382, N.v55382.
  rewrite ?node_55375.
  rewrite ?node_55376.
  rewrite ?node_55377.
  rewrite ?node_55381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55383 (s : N.State) (i : N.Inputs) :
  R.v55383 (state s) (inputs i) = Zmod.unsigned (N.v55383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55383 s i)) at 1.
  unfold R.v55383, N.v55383.
  unfold R.v6, N.v6.
  rewrite ?node_55382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55384 (s : N.State) (i : N.Inputs) :
  R.v55384 (state s) (inputs i) = Zmod.unsigned (N.v55384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55384 s i)) at 1.
  unfold R.v55384, N.v55384.
  rewrite ?node_8944.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55385 (s : N.State) (i : N.Inputs) :
  R.v55385 (state s) (inputs i) = Zmod.unsigned (N.v55385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55385 s i)) at 1.
  unfold R.v55385, N.v55385.
  unfold R.v6, N.v6.
  rewrite ?node_9082.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55386 (s : N.State) (i : N.Inputs) :
  R.v55386 (state s) (inputs i) = Zmod.unsigned (N.v55386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55386 s i)) at 1.
  unfold R.v55386, N.v55386.
  unfold R.v6, N.v6.
  rewrite ?node_9086.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55387 (s : N.State) (i : N.Inputs) :
  R.v55387 (state s) (inputs i) = Zmod.unsigned (N.v55387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55387 s i)) at 1.
  unfold R.v55387, N.v55387.
  rewrite ?node_55384.
  rewrite ?node_55385.
  rewrite ?node_55386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55388 (s : N.State) (i : N.Inputs) :
  R.v55388 (state s) (inputs i) = Zmod.unsigned (N.v55388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55388 s i)) at 1.
  unfold R.v55388, N.v55388.
  rewrite ?node_55383.
  rewrite ?node_55387.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55389 (s : N.State) (i : N.Inputs) :
  R.v55389 (state s) (inputs i) = Zmod.unsigned (N.v55389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55389 s i)) at 1.
  unfold R.v55389, N.v55389.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55390 (s : N.State) (i : N.Inputs) :
  R.v55390 (state s) (inputs i) = Zmod.unsigned (N.v55390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55390 s i)) at 1.
  unfold R.v55390, N.v55390.
  rewrite ?node_8935.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55391 (s : N.State) (i : N.Inputs) :
  R.v55391 (state s) (inputs i) = Zmod.unsigned (N.v55391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55391 s i)) at 1.
  unfold R.v55391, N.v55391.
  unfold R.v6, N.v6.
  rewrite ?node_8931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55392 (s : N.State) (i : N.Inputs) :
  R.v55392 (state s) (inputs i) = Zmod.unsigned (N.v55392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55392 s i)) at 1.
  unfold R.v55392, N.v55392.
  unfold R.v6, N.v6.
  rewrite ?node_8914.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55393 (s : N.State) (i : N.Inputs) :
  R.v55393 (state s) (inputs i) = Zmod.unsigned (N.v55393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55393 s i)) at 1.
  unfold R.v55393, N.v55393.
  rewrite ?node_55391.
  rewrite ?node_55392.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55394 (s : N.State) (i : N.Inputs) :
  R.v55394 (state s) (inputs i) = Zmod.unsigned (N.v55394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55394 s i)) at 1.
  unfold R.v55394, N.v55394.
  unfold R.v16484, N.v16484.
  rewrite ?node_55393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55395 (s : N.State) (i : N.Inputs) :
  R.v55395 (state s) (inputs i) = Zmod.unsigned (N.v55395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55395 s i)) at 1.
  unfold R.v55395, N.v55395.
  rewrite ?node_55390.
  rewrite ?node_55394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55396 (s : N.State) (i : N.Inputs) :
  R.v55396 (state s) (inputs i) = Zmod.unsigned (N.v55396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55396 s i)) at 1.
  unfold R.v55396, N.v55396.
  unfold R.v6, N.v6.
  rewrite ?node_55395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55397 (s : N.State) (i : N.Inputs) :
  R.v55397 (state s) (inputs i) = Zmod.unsigned (N.v55397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55397 s i)) at 1.
  unfold R.v55397, N.v55397.
  rewrite ?node_8936.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55398 (s : N.State) (i : N.Inputs) :
  R.v55398 (state s) (inputs i) = Zmod.unsigned (N.v55398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55398 s i)) at 1.
  unfold R.v55398, N.v55398.
  unfold R.v6, N.v6.
  rewrite ?node_9082.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55399 (s : N.State) (i : N.Inputs) :
  R.v55399 (state s) (inputs i) = Zmod.unsigned (N.v55399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55399 s i)) at 1.
  unfold R.v55399, N.v55399.
  rewrite ?node_55397.
  rewrite ?node_55398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55400 (s : N.State) (i : N.Inputs) :
  R.v55400 (state s) (inputs i) = Zmod.unsigned (N.v55400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55400 s i)) at 1.
  unfold R.v55400, N.v55400.
  rewrite ?node_55396.
  rewrite ?node_55399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55401 (s : N.State) (i : N.Inputs) :
  R.v55401 (state s) (inputs i) = Zmod.unsigned (N.v55401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55401 s i)) at 1.
  unfold R.v55401, N.v55401.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55402 (s : N.State) (i : N.Inputs) :
  R.v55402 (state s) (inputs i) = Zmod.unsigned (N.v55402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55402 s i)) at 1.
  unfold R.v55402, N.v55402.
  rewrite ?node_8943.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55403 (s : N.State) (i : N.Inputs) :
  R.v55403 (state s) (inputs i) = Zmod.unsigned (N.v55403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55403 s i)) at 1.
  unfold R.v55403, N.v55403.
  unfold R.v6, N.v6.
  rewrite ?node_8939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55404 (s : N.State) (i : N.Inputs) :
  R.v55404 (state s) (inputs i) = Zmod.unsigned (N.v55404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55404 s i)) at 1.
  unfold R.v55404, N.v55404.
  unfold R.v6, N.v6.
  rewrite ?node_8936.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55405 (s : N.State) (i : N.Inputs) :
  R.v55405 (state s) (inputs i) = Zmod.unsigned (N.v55405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55405 s i)) at 1.
  unfold R.v55405, N.v55405.
  rewrite ?node_55403.
  rewrite ?node_55404.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55406 (s : N.State) (i : N.Inputs) :
  R.v55406 (state s) (inputs i) = Zmod.unsigned (N.v55406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55406 s i)) at 1.
  unfold R.v55406, N.v55406.
  unfold R.v16484, N.v16484.
  rewrite ?node_55405.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55407 (s : N.State) (i : N.Inputs) :
  R.v55407 (state s) (inputs i) = Zmod.unsigned (N.v55407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55407 s i)) at 1.
  unfold R.v55407, N.v55407.
  rewrite ?node_55402.
  rewrite ?node_55406.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55408 (s : N.State) (i : N.Inputs) :
  R.v55408 (state s) (inputs i) = Zmod.unsigned (N.v55408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55408 s i)) at 1.
  unfold R.v55408, N.v55408.
  unfold R.v6, N.v6.
  rewrite ?node_55407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55409 (s : N.State) (i : N.Inputs) :
  R.v55409 (state s) (inputs i) = Zmod.unsigned (N.v55409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55409 s i)) at 1.
  unfold R.v55409, N.v55409.
  rewrite ?node_8944.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55410 (s : N.State) (i : N.Inputs) :
  R.v55410 (state s) (inputs i) = Zmod.unsigned (N.v55410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55410 s i)) at 1.
  unfold R.v55410, N.v55410.
  unfold R.v6, N.v6.
  rewrite ?node_9086.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55411 (s : N.State) (i : N.Inputs) :
  R.v55411 (state s) (inputs i) = Zmod.unsigned (N.v55411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55411 s i)) at 1.
  unfold R.v55411, N.v55411.
  rewrite ?node_55409.
  rewrite ?node_55410.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55412 (s : N.State) (i : N.Inputs) :
  R.v55412 (state s) (inputs i) = Zmod.unsigned (N.v55412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55412 s i)) at 1.
  unfold R.v55412, N.v55412.
  rewrite ?node_55408.
  rewrite ?node_55411.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55413 (s : N.State) (i : N.Inputs) :
  R.v55413 (state s) (inputs i) = Zmod.unsigned (N.v55413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55413 s i)) at 1.
  unfold R.v55413, N.v55413.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55414 (s : N.State) (i : N.Inputs) :
  R.v55414 (state s) (inputs i) = Zmod.unsigned (N.v55414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55414 s i)) at 1.
  unfold R.v55414, N.v55414.
  rewrite ?node_9082.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55415 (s : N.State) (i : N.Inputs) :
  R.v55415 (state s) (inputs i) = Zmod.unsigned (N.v55415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55415 s i)) at 1.
  unfold R.v55415, N.v55415.
  rewrite ?node_9078.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55416 (s : N.State) (i : N.Inputs) :
  R.v55416 (state s) (inputs i) = Zmod.unsigned (N.v55416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55416 s i)) at 1.
  unfold R.v55416, N.v55416.
  rewrite ?node_9074.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55417 (s : N.State) (i : N.Inputs) :
  R.v55417 (state s) (inputs i) = Zmod.unsigned (N.v55417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55417 s i)) at 1.
  unfold R.v55417, N.v55417.
  unfold R.v6, N.v6.
  rewrite ?node_9070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55418 (s : N.State) (i : N.Inputs) :
  R.v55418 (state s) (inputs i) = Zmod.unsigned (N.v55418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55418 s i)) at 1.
  unfold R.v55418, N.v55418.
  unfold R.v6, N.v6.
  rewrite ?node_9051.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55419 (s : N.State) (i : N.Inputs) :
  R.v55419 (state s) (inputs i) = Zmod.unsigned (N.v55419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55419 s i)) at 1.
  unfold R.v55419, N.v55419.
  rewrite ?node_55417.
  rewrite ?node_55418.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55420 (s : N.State) (i : N.Inputs) :
  R.v55420 (state s) (inputs i) = Zmod.unsigned (N.v55420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55420 s i)) at 1.
  unfold R.v55420, N.v55420.
  unfold R.v16484, N.v16484.
  rewrite ?node_55419.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55421 (s : N.State) (i : N.Inputs) :
  R.v55421 (state s) (inputs i) = Zmod.unsigned (N.v55421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55421 s i)) at 1.
  unfold R.v55421, N.v55421.
  rewrite ?node_55414.
  rewrite ?node_55415.
  rewrite ?node_55416.
  rewrite ?node_55420.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55422 (s : N.State) (i : N.Inputs) :
  R.v55422 (state s) (inputs i) = Zmod.unsigned (N.v55422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55422 s i)) at 1.
  unfold R.v55422, N.v55422.
  unfold R.v6, N.v6.
  rewrite ?node_55421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55423 (s : N.State) (i : N.Inputs) :
  R.v55423 (state s) (inputs i) = Zmod.unsigned (N.v55423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55423 s i)) at 1.
  unfold R.v55423, N.v55423.
  rewrite ?node_9083.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55424 (s : N.State) (i : N.Inputs) :
  R.v55424 (state s) (inputs i) = Zmod.unsigned (N.v55424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55424 s i)) at 1.
  unfold R.v55424, N.v55424.
  unfold R.v6, N.v6.
  rewrite ?node_9222.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55425 (s : N.State) (i : N.Inputs) :
  R.v55425 (state s) (inputs i) = Zmod.unsigned (N.v55425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55425 s i)) at 1.
  unfold R.v55425, N.v55425.
  unfold R.v6, N.v6.
  rewrite ?node_9226.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55426 (s : N.State) (i : N.Inputs) :
  R.v55426 (state s) (inputs i) = Zmod.unsigned (N.v55426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55426 s i)) at 1.
  unfold R.v55426, N.v55426.
  rewrite ?node_55423.
  rewrite ?node_55424.
  rewrite ?node_55425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55427 (s : N.State) (i : N.Inputs) :
  R.v55427 (state s) (inputs i) = Zmod.unsigned (N.v55427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55427 s i)) at 1.
  unfold R.v55427, N.v55427.
  rewrite ?node_55422.
  rewrite ?node_55426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55428 (s : N.State) (i : N.Inputs) :
  R.v55428 (state s) (inputs i) = Zmod.unsigned (N.v55428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55428 s i)) at 1.
  unfold R.v55428, N.v55428.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55429 (s : N.State) (i : N.Inputs) :
  R.v55429 (state s) (inputs i) = Zmod.unsigned (N.v55429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55429 s i)) at 1.
  unfold R.v55429, N.v55429.
  rewrite ?node_9074.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55430 (s : N.State) (i : N.Inputs) :
  R.v55430 (state s) (inputs i) = Zmod.unsigned (N.v55430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55430 s i)) at 1.
  unfold R.v55430, N.v55430.
  unfold R.v6, N.v6.
  rewrite ?node_9070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55431 (s : N.State) (i : N.Inputs) :
  R.v55431 (state s) (inputs i) = Zmod.unsigned (N.v55431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55431 s i)) at 1.
  unfold R.v55431, N.v55431.
  unfold R.v6, N.v6.
  rewrite ?node_9051.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55432 (s : N.State) (i : N.Inputs) :
  R.v55432 (state s) (inputs i) = Zmod.unsigned (N.v55432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55432 s i)) at 1.
  unfold R.v55432, N.v55432.
  rewrite ?node_55430.
  rewrite ?node_55431.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55433 (s : N.State) (i : N.Inputs) :
  R.v55433 (state s) (inputs i) = Zmod.unsigned (N.v55433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55433 s i)) at 1.
  unfold R.v55433, N.v55433.
  unfold R.v16484, N.v16484.
  rewrite ?node_55432.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55434 (s : N.State) (i : N.Inputs) :
  R.v55434 (state s) (inputs i) = Zmod.unsigned (N.v55434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55434 s i)) at 1.
  unfold R.v55434, N.v55434.
  rewrite ?node_55429.
  rewrite ?node_55433.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55435 (s : N.State) (i : N.Inputs) :
  R.v55435 (state s) (inputs i) = Zmod.unsigned (N.v55435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55435 s i)) at 1.
  unfold R.v55435, N.v55435.
  unfold R.v6, N.v6.
  rewrite ?node_55434.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55436 (s : N.State) (i : N.Inputs) :
  R.v55436 (state s) (inputs i) = Zmod.unsigned (N.v55436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55436 s i)) at 1.
  unfold R.v55436, N.v55436.
  rewrite ?node_9075.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55437 (s : N.State) (i : N.Inputs) :
  R.v55437 (state s) (inputs i) = Zmod.unsigned (N.v55437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55437 s i)) at 1.
  unfold R.v55437, N.v55437.
  unfold R.v6, N.v6.
  rewrite ?node_9222.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55438 (s : N.State) (i : N.Inputs) :
  R.v55438 (state s) (inputs i) = Zmod.unsigned (N.v55438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55438 s i)) at 1.
  unfold R.v55438, N.v55438.
  rewrite ?node_55436.
  rewrite ?node_55437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55439 (s : N.State) (i : N.Inputs) :
  R.v55439 (state s) (inputs i) = Zmod.unsigned (N.v55439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55439 s i)) at 1.
  unfold R.v55439, N.v55439.
  rewrite ?node_55435.
  rewrite ?node_55438.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55440 (s : N.State) (i : N.Inputs) :
  R.v55440 (state s) (inputs i) = Zmod.unsigned (N.v55440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55440 s i)) at 1.
  unfold R.v55440, N.v55440.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55441 (s : N.State) (i : N.Inputs) :
  R.v55441 (state s) (inputs i) = Zmod.unsigned (N.v55441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55441 s i)) at 1.
  unfold R.v55441, N.v55441.
  rewrite ?node_9082.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55442 (s : N.State) (i : N.Inputs) :
  R.v55442 (state s) (inputs i) = Zmod.unsigned (N.v55442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55442 s i)) at 1.
  unfold R.v55442, N.v55442.
  unfold R.v6, N.v6.
  rewrite ?node_9078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55443 (s : N.State) (i : N.Inputs) :
  R.v55443 (state s) (inputs i) = Zmod.unsigned (N.v55443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55443 s i)) at 1.
  unfold R.v55443, N.v55443.
  unfold R.v6, N.v6.
  rewrite ?node_9075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55444 (s : N.State) (i : N.Inputs) :
  R.v55444 (state s) (inputs i) = Zmod.unsigned (N.v55444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55444 s i)) at 1.
  unfold R.v55444, N.v55444.
  rewrite ?node_55442.
  rewrite ?node_55443.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55445 (s : N.State) (i : N.Inputs) :
  R.v55445 (state s) (inputs i) = Zmod.unsigned (N.v55445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55445 s i)) at 1.
  unfold R.v55445, N.v55445.
  unfold R.v16484, N.v16484.
  rewrite ?node_55444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55446 (s : N.State) (i : N.Inputs) :
  R.v55446 (state s) (inputs i) = Zmod.unsigned (N.v55446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55446 s i)) at 1.
  unfold R.v55446, N.v55446.
  rewrite ?node_55441.
  rewrite ?node_55445.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55447 (s : N.State) (i : N.Inputs) :
  R.v55447 (state s) (inputs i) = Zmod.unsigned (N.v55447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55447 s i)) at 1.
  unfold R.v55447, N.v55447.
  unfold R.v6, N.v6.
  rewrite ?node_55446.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55448 (s : N.State) (i : N.Inputs) :
  R.v55448 (state s) (inputs i) = Zmod.unsigned (N.v55448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55448 s i)) at 1.
  unfold R.v55448, N.v55448.
  rewrite ?node_9083.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55449 (s : N.State) (i : N.Inputs) :
  R.v55449 (state s) (inputs i) = Zmod.unsigned (N.v55449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55449 s i)) at 1.
  unfold R.v55449, N.v55449.
  unfold R.v6, N.v6.
  rewrite ?node_9226.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55450 (s : N.State) (i : N.Inputs) :
  R.v55450 (state s) (inputs i) = Zmod.unsigned (N.v55450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55450 s i)) at 1.
  unfold R.v55450, N.v55450.
  rewrite ?node_55448.
  rewrite ?node_55449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55451 (s : N.State) (i : N.Inputs) :
  R.v55451 (state s) (inputs i) = Zmod.unsigned (N.v55451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55451 s i)) at 1.
  unfold R.v55451, N.v55451.
  rewrite ?node_55447.
  rewrite ?node_55450.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55452 (s : N.State) (i : N.Inputs) :
  R.v55452 (state s) (inputs i) = Zmod.unsigned (N.v55452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55452 s i)) at 1.
  unfold R.v55452, N.v55452.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55453 (s : N.State) (i : N.Inputs) :
  R.v55453 (state s) (inputs i) = Zmod.unsigned (N.v55453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55453 s i)) at 1.
  unfold R.v55453, N.v55453.
  rewrite ?node_9222.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55454 (s : N.State) (i : N.Inputs) :
  R.v55454 (state s) (inputs i) = Zmod.unsigned (N.v55454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55454 s i)) at 1.
  unfold R.v55454, N.v55454.
  rewrite ?node_9218.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55455 (s : N.State) (i : N.Inputs) :
  R.v55455 (state s) (inputs i) = Zmod.unsigned (N.v55455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55455 s i)) at 1.
  unfold R.v55455, N.v55455.
  rewrite ?node_9214.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55456 (s : N.State) (i : N.Inputs) :
  R.v55456 (state s) (inputs i) = Zmod.unsigned (N.v55456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55456 s i)) at 1.
  unfold R.v55456, N.v55456.
  unfold R.v6, N.v6.
  rewrite ?node_9210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55457 (s : N.State) (i : N.Inputs) :
  R.v55457 (state s) (inputs i) = Zmod.unsigned (N.v55457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55457 s i)) at 1.
  unfold R.v55457, N.v55457.
  unfold R.v6, N.v6.
  rewrite ?node_9191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55458 (s : N.State) (i : N.Inputs) :
  R.v55458 (state s) (inputs i) = Zmod.unsigned (N.v55458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55458 s i)) at 1.
  unfold R.v55458, N.v55458.
  rewrite ?node_55456.
  rewrite ?node_55457.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55459 (s : N.State) (i : N.Inputs) :
  R.v55459 (state s) (inputs i) = Zmod.unsigned (N.v55459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55459 s i)) at 1.
  unfold R.v55459, N.v55459.
  unfold R.v16484, N.v16484.
  rewrite ?node_55458.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55460 (s : N.State) (i : N.Inputs) :
  R.v55460 (state s) (inputs i) = Zmod.unsigned (N.v55460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55460 s i)) at 1.
  unfold R.v55460, N.v55460.
  rewrite ?node_55453.
  rewrite ?node_55454.
  rewrite ?node_55455.
  rewrite ?node_55459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55461 (s : N.State) (i : N.Inputs) :
  R.v55461 (state s) (inputs i) = Zmod.unsigned (N.v55461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55461 s i)) at 1.
  unfold R.v55461, N.v55461.
  unfold R.v6, N.v6.
  rewrite ?node_55460.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55462 (s : N.State) (i : N.Inputs) :
  R.v55462 (state s) (inputs i) = Zmod.unsigned (N.v55462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55462 s i)) at 1.
  unfold R.v55462, N.v55462.
  rewrite ?node_9223.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55463 (s : N.State) (i : N.Inputs) :
  R.v55463 (state s) (inputs i) = Zmod.unsigned (N.v55463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55463 s i)) at 1.
  unfold R.v55463, N.v55463.
  unfold R.v6, N.v6.
  rewrite ?node_9364.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55464 (s : N.State) (i : N.Inputs) :
  R.v55464 (state s) (inputs i) = Zmod.unsigned (N.v55464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55464 s i)) at 1.
  unfold R.v55464, N.v55464.
  unfold R.v6, N.v6.
  rewrite ?node_9368.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55465 (s : N.State) (i : N.Inputs) :
  R.v55465 (state s) (inputs i) = Zmod.unsigned (N.v55465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55465 s i)) at 1.
  unfold R.v55465, N.v55465.
  rewrite ?node_55462.
  rewrite ?node_55463.
  rewrite ?node_55464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55466 (s : N.State) (i : N.Inputs) :
  R.v55466 (state s) (inputs i) = Zmod.unsigned (N.v55466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55466 s i)) at 1.
  unfold R.v55466, N.v55466.
  rewrite ?node_55461.
  rewrite ?node_55465.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55467 (s : N.State) (i : N.Inputs) :
  R.v55467 (state s) (inputs i) = Zmod.unsigned (N.v55467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55467 s i)) at 1.
  unfold R.v55467, N.v55467.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55468 (s : N.State) (i : N.Inputs) :
  R.v55468 (state s) (inputs i) = Zmod.unsigned (N.v55468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55468 s i)) at 1.
  unfold R.v55468, N.v55468.
  rewrite ?node_9214.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55469 (s : N.State) (i : N.Inputs) :
  R.v55469 (state s) (inputs i) = Zmod.unsigned (N.v55469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55469 s i)) at 1.
  unfold R.v55469, N.v55469.
  unfold R.v6, N.v6.
  rewrite ?node_9210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55470 (s : N.State) (i : N.Inputs) :
  R.v55470 (state s) (inputs i) = Zmod.unsigned (N.v55470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55470 s i)) at 1.
  unfold R.v55470, N.v55470.
  unfold R.v6, N.v6.
  rewrite ?node_9191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55471 (s : N.State) (i : N.Inputs) :
  R.v55471 (state s) (inputs i) = Zmod.unsigned (N.v55471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55471 s i)) at 1.
  unfold R.v55471, N.v55471.
  rewrite ?node_55469.
  rewrite ?node_55470.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55472 (s : N.State) (i : N.Inputs) :
  R.v55472 (state s) (inputs i) = Zmod.unsigned (N.v55472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55472 s i)) at 1.
  unfold R.v55472, N.v55472.
  unfold R.v16484, N.v16484.
  rewrite ?node_55471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55473 (s : N.State) (i : N.Inputs) :
  R.v55473 (state s) (inputs i) = Zmod.unsigned (N.v55473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55473 s i)) at 1.
  unfold R.v55473, N.v55473.
  rewrite ?node_55468.
  rewrite ?node_55472.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55474 (s : N.State) (i : N.Inputs) :
  R.v55474 (state s) (inputs i) = Zmod.unsigned (N.v55474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55474 s i)) at 1.
  unfold R.v55474, N.v55474.
  unfold R.v6, N.v6.
  rewrite ?node_55473.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55475 (s : N.State) (i : N.Inputs) :
  R.v55475 (state s) (inputs i) = Zmod.unsigned (N.v55475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55475 s i)) at 1.
  unfold R.v55475, N.v55475.
  rewrite ?node_9215.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55476 (s : N.State) (i : N.Inputs) :
  R.v55476 (state s) (inputs i) = Zmod.unsigned (N.v55476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55476 s i)) at 1.
  unfold R.v55476, N.v55476.
  unfold R.v6, N.v6.
  rewrite ?node_9364.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55477 (s : N.State) (i : N.Inputs) :
  R.v55477 (state s) (inputs i) = Zmod.unsigned (N.v55477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55477 s i)) at 1.
  unfold R.v55477, N.v55477.
  rewrite ?node_55475.
  rewrite ?node_55476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55478 (s : N.State) (i : N.Inputs) :
  R.v55478 (state s) (inputs i) = Zmod.unsigned (N.v55478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55478 s i)) at 1.
  unfold R.v55478, N.v55478.
  rewrite ?node_55474.
  rewrite ?node_55477.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55479 (s : N.State) (i : N.Inputs) :
  R.v55479 (state s) (inputs i) = Zmod.unsigned (N.v55479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55479 s i)) at 1.
  unfold R.v55479, N.v55479.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55480 (s : N.State) (i : N.Inputs) :
  R.v55480 (state s) (inputs i) = Zmod.unsigned (N.v55480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55480 s i)) at 1.
  unfold R.v55480, N.v55480.
  rewrite ?node_9222.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55481 (s : N.State) (i : N.Inputs) :
  R.v55481 (state s) (inputs i) = Zmod.unsigned (N.v55481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55481 s i)) at 1.
  unfold R.v55481, N.v55481.
  unfold R.v6, N.v6.
  rewrite ?node_9218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55482 (s : N.State) (i : N.Inputs) :
  R.v55482 (state s) (inputs i) = Zmod.unsigned (N.v55482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55482 s i)) at 1.
  unfold R.v55482, N.v55482.
  unfold R.v6, N.v6.
  rewrite ?node_9215.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55483 (s : N.State) (i : N.Inputs) :
  R.v55483 (state s) (inputs i) = Zmod.unsigned (N.v55483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55483 s i)) at 1.
  unfold R.v55483, N.v55483.
  rewrite ?node_55481.
  rewrite ?node_55482.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55484 (s : N.State) (i : N.Inputs) :
  R.v55484 (state s) (inputs i) = Zmod.unsigned (N.v55484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55484 s i)) at 1.
  unfold R.v55484, N.v55484.
  unfold R.v16484, N.v16484.
  rewrite ?node_55483.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55485 (s : N.State) (i : N.Inputs) :
  R.v55485 (state s) (inputs i) = Zmod.unsigned (N.v55485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55485 s i)) at 1.
  unfold R.v55485, N.v55485.
  rewrite ?node_55480.
  rewrite ?node_55484.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55486 (s : N.State) (i : N.Inputs) :
  R.v55486 (state s) (inputs i) = Zmod.unsigned (N.v55486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55486 s i)) at 1.
  unfold R.v55486, N.v55486.
  unfold R.v6, N.v6.
  rewrite ?node_55485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55487 (s : N.State) (i : N.Inputs) :
  R.v55487 (state s) (inputs i) = Zmod.unsigned (N.v55487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55487 s i)) at 1.
  unfold R.v55487, N.v55487.
  rewrite ?node_9223.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55488 (s : N.State) (i : N.Inputs) :
  R.v55488 (state s) (inputs i) = Zmod.unsigned (N.v55488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55488 s i)) at 1.
  unfold R.v55488, N.v55488.
  unfold R.v6, N.v6.
  rewrite ?node_9368.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55489 (s : N.State) (i : N.Inputs) :
  R.v55489 (state s) (inputs i) = Zmod.unsigned (N.v55489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55489 s i)) at 1.
  unfold R.v55489, N.v55489.
  rewrite ?node_55487.
  rewrite ?node_55488.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55490 (s : N.State) (i : N.Inputs) :
  R.v55490 (state s) (inputs i) = Zmod.unsigned (N.v55490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55490 s i)) at 1.
  unfold R.v55490, N.v55490.
  rewrite ?node_55486.
  rewrite ?node_55489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55491 (s : N.State) (i : N.Inputs) :
  R.v55491 (state s) (inputs i) = Zmod.unsigned (N.v55491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55491 s i)) at 1.
  unfold R.v55491, N.v55491.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55492 (s : N.State) (i : N.Inputs) :
  R.v55492 (state s) (inputs i) = Zmod.unsigned (N.v55492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55492 s i)) at 1.
  unfold R.v55492, N.v55492.
  rewrite ?node_9364.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55493 (s : N.State) (i : N.Inputs) :
  R.v55493 (state s) (inputs i) = Zmod.unsigned (N.v55493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55493 s i)) at 1.
  unfold R.v55493, N.v55493.
  rewrite ?node_9360.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55494 (s : N.State) (i : N.Inputs) :
  R.v55494 (state s) (inputs i) = Zmod.unsigned (N.v55494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55494 s i)) at 1.
  unfold R.v55494, N.v55494.
  rewrite ?node_9356.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55495 (s : N.State) (i : N.Inputs) :
  R.v55495 (state s) (inputs i) = Zmod.unsigned (N.v55495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55495 s i)) at 1.
  unfold R.v55495, N.v55495.
  unfold R.v6, N.v6.
  rewrite ?node_9352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55496 (s : N.State) (i : N.Inputs) :
  R.v55496 (state s) (inputs i) = Zmod.unsigned (N.v55496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55496 s i)) at 1.
  unfold R.v55496, N.v55496.
  unfold R.v6, N.v6.
  rewrite ?node_9333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55497 (s : N.State) (i : N.Inputs) :
  R.v55497 (state s) (inputs i) = Zmod.unsigned (N.v55497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55497 s i)) at 1.
  unfold R.v55497, N.v55497.
  rewrite ?node_55495.
  rewrite ?node_55496.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55498 (s : N.State) (i : N.Inputs) :
  R.v55498 (state s) (inputs i) = Zmod.unsigned (N.v55498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55498 s i)) at 1.
  unfold R.v55498, N.v55498.
  unfold R.v16484, N.v16484.
  rewrite ?node_55497.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55499 (s : N.State) (i : N.Inputs) :
  R.v55499 (state s) (inputs i) = Zmod.unsigned (N.v55499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55499 s i)) at 1.
  unfold R.v55499, N.v55499.
  rewrite ?node_55492.
  rewrite ?node_55493.
  rewrite ?node_55494.
  rewrite ?node_55498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55500 (s : N.State) (i : N.Inputs) :
  R.v55500 (state s) (inputs i) = Zmod.unsigned (N.v55500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55500 s i)) at 1.
  unfold R.v55500, N.v55500.
  unfold R.v6, N.v6.
  rewrite ?node_55499.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55501 (s : N.State) (i : N.Inputs) :
  R.v55501 (state s) (inputs i) = Zmod.unsigned (N.v55501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55501 s i)) at 1.
  unfold R.v55501, N.v55501.
  rewrite ?node_9365.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55502 (s : N.State) (i : N.Inputs) :
  R.v55502 (state s) (inputs i) = Zmod.unsigned (N.v55502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55502 s i)) at 1.
  unfold R.v55502, N.v55502.
  unfold R.v6, N.v6.
  rewrite ?node_9509.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55503 (s : N.State) (i : N.Inputs) :
  R.v55503 (state s) (inputs i) = Zmod.unsigned (N.v55503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55503 s i)) at 1.
  unfold R.v55503, N.v55503.
  unfold R.v6, N.v6.
  rewrite ?node_9513.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55504 (s : N.State) (i : N.Inputs) :
  R.v55504 (state s) (inputs i) = Zmod.unsigned (N.v55504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55504 s i)) at 1.
  unfold R.v55504, N.v55504.
  rewrite ?node_55501.
  rewrite ?node_55502.
  rewrite ?node_55503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55505 (s : N.State) (i : N.Inputs) :
  R.v55505 (state s) (inputs i) = Zmod.unsigned (N.v55505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55505 s i)) at 1.
  unfold R.v55505, N.v55505.
  rewrite ?node_55500.
  rewrite ?node_55504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55506 (s : N.State) (i : N.Inputs) :
  R.v55506 (state s) (inputs i) = Zmod.unsigned (N.v55506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55506 s i)) at 1.
  unfold R.v55506, N.v55506.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55507 (s : N.State) (i : N.Inputs) :
  R.v55507 (state s) (inputs i) = Zmod.unsigned (N.v55507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55507 s i)) at 1.
  unfold R.v55507, N.v55507.
  rewrite ?node_9356.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55508 (s : N.State) (i : N.Inputs) :
  R.v55508 (state s) (inputs i) = Zmod.unsigned (N.v55508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55508 s i)) at 1.
  unfold R.v55508, N.v55508.
  unfold R.v6, N.v6.
  rewrite ?node_9352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55509 (s : N.State) (i : N.Inputs) :
  R.v55509 (state s) (inputs i) = Zmod.unsigned (N.v55509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55509 s i)) at 1.
  unfold R.v55509, N.v55509.
  unfold R.v6, N.v6.
  rewrite ?node_9333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55510 (s : N.State) (i : N.Inputs) :
  R.v55510 (state s) (inputs i) = Zmod.unsigned (N.v55510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55510 s i)) at 1.
  unfold R.v55510, N.v55510.
  rewrite ?node_55508.
  rewrite ?node_55509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55511 (s : N.State) (i : N.Inputs) :
  R.v55511 (state s) (inputs i) = Zmod.unsigned (N.v55511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55511 s i)) at 1.
  unfold R.v55511, N.v55511.
  unfold R.v16484, N.v16484.
  rewrite ?node_55510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55512 (s : N.State) (i : N.Inputs) :
  R.v55512 (state s) (inputs i) = Zmod.unsigned (N.v55512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55512 s i)) at 1.
  unfold R.v55512, N.v55512.
  rewrite ?node_55507.
  rewrite ?node_55511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55513 (s : N.State) (i : N.Inputs) :
  R.v55513 (state s) (inputs i) = Zmod.unsigned (N.v55513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55513 s i)) at 1.
  unfold R.v55513, N.v55513.
  unfold R.v6, N.v6.
  rewrite ?node_55512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55514 (s : N.State) (i : N.Inputs) :
  R.v55514 (state s) (inputs i) = Zmod.unsigned (N.v55514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55514 s i)) at 1.
  unfold R.v55514, N.v55514.
  rewrite ?node_9357.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55515 (s : N.State) (i : N.Inputs) :
  R.v55515 (state s) (inputs i) = Zmod.unsigned (N.v55515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55515 s i)) at 1.
  unfold R.v55515, N.v55515.
  unfold R.v6, N.v6.
  rewrite ?node_9509.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55516 (s : N.State) (i : N.Inputs) :
  R.v55516 (state s) (inputs i) = Zmod.unsigned (N.v55516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55516 s i)) at 1.
  unfold R.v55516, N.v55516.
  rewrite ?node_55514.
  rewrite ?node_55515.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55517 (s : N.State) (i : N.Inputs) :
  R.v55517 (state s) (inputs i) = Zmod.unsigned (N.v55517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55517 s i)) at 1.
  unfold R.v55517, N.v55517.
  rewrite ?node_55513.
  rewrite ?node_55516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55518 (s : N.State) (i : N.Inputs) :
  R.v55518 (state s) (inputs i) = Zmod.unsigned (N.v55518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55518 s i)) at 1.
  unfold R.v55518, N.v55518.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55519 (s : N.State) (i : N.Inputs) :
  R.v55519 (state s) (inputs i) = Zmod.unsigned (N.v55519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55519 s i)) at 1.
  unfold R.v55519, N.v55519.
  rewrite ?node_9364.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55520 (s : N.State) (i : N.Inputs) :
  R.v55520 (state s) (inputs i) = Zmod.unsigned (N.v55520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55520 s i)) at 1.
  unfold R.v55520, N.v55520.
  unfold R.v6, N.v6.
  rewrite ?node_9360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55521 (s : N.State) (i : N.Inputs) :
  R.v55521 (state s) (inputs i) = Zmod.unsigned (N.v55521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55521 s i)) at 1.
  unfold R.v55521, N.v55521.
  unfold R.v6, N.v6.
  rewrite ?node_9357.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55522 (s : N.State) (i : N.Inputs) :
  R.v55522 (state s) (inputs i) = Zmod.unsigned (N.v55522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55522 s i)) at 1.
  unfold R.v55522, N.v55522.
  rewrite ?node_55520.
  rewrite ?node_55521.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55523 (s : N.State) (i : N.Inputs) :
  R.v55523 (state s) (inputs i) = Zmod.unsigned (N.v55523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55523 s i)) at 1.
  unfold R.v55523, N.v55523.
  unfold R.v16484, N.v16484.
  rewrite ?node_55522.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55524 (s : N.State) (i : N.Inputs) :
  R.v55524 (state s) (inputs i) = Zmod.unsigned (N.v55524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55524 s i)) at 1.
  unfold R.v55524, N.v55524.
  rewrite ?node_55519.
  rewrite ?node_55523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55525 (s : N.State) (i : N.Inputs) :
  R.v55525 (state s) (inputs i) = Zmod.unsigned (N.v55525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55525 s i)) at 1.
  unfold R.v55525, N.v55525.
  unfold R.v6, N.v6.
  rewrite ?node_55524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55526 (s : N.State) (i : N.Inputs) :
  R.v55526 (state s) (inputs i) = Zmod.unsigned (N.v55526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55526 s i)) at 1.
  unfold R.v55526, N.v55526.
  rewrite ?node_9365.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55527 (s : N.State) (i : N.Inputs) :
  R.v55527 (state s) (inputs i) = Zmod.unsigned (N.v55527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55527 s i)) at 1.
  unfold R.v55527, N.v55527.
  unfold R.v6, N.v6.
  rewrite ?node_9513.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55528 (s : N.State) (i : N.Inputs) :
  R.v55528 (state s) (inputs i) = Zmod.unsigned (N.v55528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55528 s i)) at 1.
  unfold R.v55528, N.v55528.
  rewrite ?node_55526.
  rewrite ?node_55527.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55529 (s : N.State) (i : N.Inputs) :
  R.v55529 (state s) (inputs i) = Zmod.unsigned (N.v55529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55529 s i)) at 1.
  unfold R.v55529, N.v55529.
  rewrite ?node_55525.
  rewrite ?node_55528.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55530 (s : N.State) (i : N.Inputs) :
  R.v55530 (state s) (inputs i) = Zmod.unsigned (N.v55530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55530 s i)) at 1.
  unfold R.v55530, N.v55530.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55531 (s : N.State) (i : N.Inputs) :
  R.v55531 (state s) (inputs i) = Zmod.unsigned (N.v55531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55531 s i)) at 1.
  unfold R.v55531, N.v55531.
  rewrite ?node_9509.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55532 (s : N.State) (i : N.Inputs) :
  R.v55532 (state s) (inputs i) = Zmod.unsigned (N.v55532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55532 s i)) at 1.
  unfold R.v55532, N.v55532.
  rewrite ?node_9505.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55533 (s : N.State) (i : N.Inputs) :
  R.v55533 (state s) (inputs i) = Zmod.unsigned (N.v55533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55533 s i)) at 1.
  unfold R.v55533, N.v55533.
  rewrite ?node_9501.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55534 (s : N.State) (i : N.Inputs) :
  R.v55534 (state s) (inputs i) = Zmod.unsigned (N.v55534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55534 s i)) at 1.
  unfold R.v55534, N.v55534.
  unfold R.v6, N.v6.
  rewrite ?node_9497.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55535 (s : N.State) (i : N.Inputs) :
  R.v55535 (state s) (inputs i) = Zmod.unsigned (N.v55535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55535 s i)) at 1.
  unfold R.v55535, N.v55535.
  unfold R.v6, N.v6.
  rewrite ?node_9480.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55536 (s : N.State) (i : N.Inputs) :
  R.v55536 (state s) (inputs i) = Zmod.unsigned (N.v55536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55536 s i)) at 1.
  unfold R.v55536, N.v55536.
  rewrite ?node_55534.
  rewrite ?node_55535.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55537 (s : N.State) (i : N.Inputs) :
  R.v55537 (state s) (inputs i) = Zmod.unsigned (N.v55537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55537 s i)) at 1.
  unfold R.v55537, N.v55537.
  unfold R.v16484, N.v16484.
  rewrite ?node_55536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55538 (s : N.State) (i : N.Inputs) :
  R.v55538 (state s) (inputs i) = Zmod.unsigned (N.v55538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55538 s i)) at 1.
  unfold R.v55538, N.v55538.
  rewrite ?node_55531.
  rewrite ?node_55532.
  rewrite ?node_55533.
  rewrite ?node_55537.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55539 (s : N.State) (i : N.Inputs) :
  R.v55539 (state s) (inputs i) = Zmod.unsigned (N.v55539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55539 s i)) at 1.
  unfold R.v55539, N.v55539.
  unfold R.v6, N.v6.
  rewrite ?node_55538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55540 (s : N.State) (i : N.Inputs) :
  R.v55540 (state s) (inputs i) = Zmod.unsigned (N.v55540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55540 s i)) at 1.
  unfold R.v55540, N.v55540.
  rewrite ?node_9510.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55541 (s : N.State) (i : N.Inputs) :
  R.v55541 (state s) (inputs i) = Zmod.unsigned (N.v55541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55541 s i)) at 1.
  unfold R.v55541, N.v55541.
  unfold R.v6, N.v6.
  rewrite ?node_9658.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55542 (s : N.State) (i : N.Inputs) :
  R.v55542 (state s) (inputs i) = Zmod.unsigned (N.v55542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55542 s i)) at 1.
  unfold R.v55542, N.v55542.
  unfold R.v6, N.v6.
  rewrite ?node_9662.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55543 (s : N.State) (i : N.Inputs) :
  R.v55543 (state s) (inputs i) = Zmod.unsigned (N.v55543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55543 s i)) at 1.
  unfold R.v55543, N.v55543.
  rewrite ?node_55540.
  rewrite ?node_55541.
  rewrite ?node_55542.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55544 (s : N.State) (i : N.Inputs) :
  R.v55544 (state s) (inputs i) = Zmod.unsigned (N.v55544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55544 s i)) at 1.
  unfold R.v55544, N.v55544.
  rewrite ?node_55539.
  rewrite ?node_55543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55545 (s : N.State) (i : N.Inputs) :
  R.v55545 (state s) (inputs i) = Zmod.unsigned (N.v55545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55545 s i)) at 1.
  unfold R.v55545, N.v55545.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55546 (s : N.State) (i : N.Inputs) :
  R.v55546 (state s) (inputs i) = Zmod.unsigned (N.v55546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55546 s i)) at 1.
  unfold R.v55546, N.v55546.
  rewrite ?node_9501.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55547 (s : N.State) (i : N.Inputs) :
  R.v55547 (state s) (inputs i) = Zmod.unsigned (N.v55547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55547 s i)) at 1.
  unfold R.v55547, N.v55547.
  unfold R.v6, N.v6.
  rewrite ?node_9497.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55548 (s : N.State) (i : N.Inputs) :
  R.v55548 (state s) (inputs i) = Zmod.unsigned (N.v55548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55548 s i)) at 1.
  unfold R.v55548, N.v55548.
  unfold R.v6, N.v6.
  rewrite ?node_9480.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55549 (s : N.State) (i : N.Inputs) :
  R.v55549 (state s) (inputs i) = Zmod.unsigned (N.v55549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55549 s i)) at 1.
  unfold R.v55549, N.v55549.
  rewrite ?node_55547.
  rewrite ?node_55548.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55550 (s : N.State) (i : N.Inputs) :
  R.v55550 (state s) (inputs i) = Zmod.unsigned (N.v55550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55550 s i)) at 1.
  unfold R.v55550, N.v55550.
  unfold R.v16484, N.v16484.
  rewrite ?node_55549.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55551 (s : N.State) (i : N.Inputs) :
  R.v55551 (state s) (inputs i) = Zmod.unsigned (N.v55551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55551 s i)) at 1.
  unfold R.v55551, N.v55551.
  rewrite ?node_55546.
  rewrite ?node_55550.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55552 (s : N.State) (i : N.Inputs) :
  R.v55552 (state s) (inputs i) = Zmod.unsigned (N.v55552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55552 s i)) at 1.
  unfold R.v55552, N.v55552.
  unfold R.v6, N.v6.
  rewrite ?node_55551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55553 (s : N.State) (i : N.Inputs) :
  R.v55553 (state s) (inputs i) = Zmod.unsigned (N.v55553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55553 s i)) at 1.
  unfold R.v55553, N.v55553.
  rewrite ?node_9502.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55554 (s : N.State) (i : N.Inputs) :
  R.v55554 (state s) (inputs i) = Zmod.unsigned (N.v55554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55554 s i)) at 1.
  unfold R.v55554, N.v55554.
  unfold R.v6, N.v6.
  rewrite ?node_9658.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55555 (s : N.State) (i : N.Inputs) :
  R.v55555 (state s) (inputs i) = Zmod.unsigned (N.v55555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55555 s i)) at 1.
  unfold R.v55555, N.v55555.
  rewrite ?node_55553.
  rewrite ?node_55554.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55556 (s : N.State) (i : N.Inputs) :
  R.v55556 (state s) (inputs i) = Zmod.unsigned (N.v55556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55556 s i)) at 1.
  unfold R.v55556, N.v55556.
  rewrite ?node_55552.
  rewrite ?node_55555.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55557 (s : N.State) (i : N.Inputs) :
  R.v55557 (state s) (inputs i) = Zmod.unsigned (N.v55557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55557 s i)) at 1.
  unfold R.v55557, N.v55557.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55558 (s : N.State) (i : N.Inputs) :
  R.v55558 (state s) (inputs i) = Zmod.unsigned (N.v55558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55558 s i)) at 1.
  unfold R.v55558, N.v55558.
  rewrite ?node_9509.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55559 (s : N.State) (i : N.Inputs) :
  R.v55559 (state s) (inputs i) = Zmod.unsigned (N.v55559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55559 s i)) at 1.
  unfold R.v55559, N.v55559.
  unfold R.v6, N.v6.
  rewrite ?node_9505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55560 (s : N.State) (i : N.Inputs) :
  R.v55560 (state s) (inputs i) = Zmod.unsigned (N.v55560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55560 s i)) at 1.
  unfold R.v55560, N.v55560.
  unfold R.v6, N.v6.
  rewrite ?node_9502.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55561 (s : N.State) (i : N.Inputs) :
  R.v55561 (state s) (inputs i) = Zmod.unsigned (N.v55561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55561 s i)) at 1.
  unfold R.v55561, N.v55561.
  rewrite ?node_55559.
  rewrite ?node_55560.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55562 (s : N.State) (i : N.Inputs) :
  R.v55562 (state s) (inputs i) = Zmod.unsigned (N.v55562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55562 s i)) at 1.
  unfold R.v55562, N.v55562.
  unfold R.v16484, N.v16484.
  rewrite ?node_55561.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55563 (s : N.State) (i : N.Inputs) :
  R.v55563 (state s) (inputs i) = Zmod.unsigned (N.v55563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55563 s i)) at 1.
  unfold R.v55563, N.v55563.
  rewrite ?node_55558.
  rewrite ?node_55562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55564 (s : N.State) (i : N.Inputs) :
  R.v55564 (state s) (inputs i) = Zmod.unsigned (N.v55564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55564 s i)) at 1.
  unfold R.v55564, N.v55564.
  unfold R.v6, N.v6.
  rewrite ?node_55563.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55565 (s : N.State) (i : N.Inputs) :
  R.v55565 (state s) (inputs i) = Zmod.unsigned (N.v55565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55565 s i)) at 1.
  unfold R.v55565, N.v55565.
  rewrite ?node_9510.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55566 (s : N.State) (i : N.Inputs) :
  R.v55566 (state s) (inputs i) = Zmod.unsigned (N.v55566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55566 s i)) at 1.
  unfold R.v55566, N.v55566.
  unfold R.v6, N.v6.
  rewrite ?node_9662.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55567 (s : N.State) (i : N.Inputs) :
  R.v55567 (state s) (inputs i) = Zmod.unsigned (N.v55567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55567 s i)) at 1.
  unfold R.v55567, N.v55567.
  rewrite ?node_55565.
  rewrite ?node_55566.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55568 (s : N.State) (i : N.Inputs) :
  R.v55568 (state s) (inputs i) = Zmod.unsigned (N.v55568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55568 s i)) at 1.
  unfold R.v55568, N.v55568.
  rewrite ?node_55564.
  rewrite ?node_55567.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55569 (s : N.State) (i : N.Inputs) :
  R.v55569 (state s) (inputs i) = Zmod.unsigned (N.v55569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55569 s i)) at 1.
  unfold R.v55569, N.v55569.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55570 (s : N.State) (i : N.Inputs) :
  R.v55570 (state s) (inputs i) = Zmod.unsigned (N.v55570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55570 s i)) at 1.
  unfold R.v55570, N.v55570.
  rewrite ?node_9658.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55571 (s : N.State) (i : N.Inputs) :
  R.v55571 (state s) (inputs i) = Zmod.unsigned (N.v55571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55571 s i)) at 1.
  unfold R.v55571, N.v55571.
  rewrite ?node_9654.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55572 (s : N.State) (i : N.Inputs) :
  R.v55572 (state s) (inputs i) = Zmod.unsigned (N.v55572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55572 s i)) at 1.
  unfold R.v55572, N.v55572.
  rewrite ?node_9650.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55573 (s : N.State) (i : N.Inputs) :
  R.v55573 (state s) (inputs i) = Zmod.unsigned (N.v55573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55573 s i)) at 1.
  unfold R.v55573, N.v55573.
  unfold R.v6, N.v6.
  rewrite ?node_9646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55574 (s : N.State) (i : N.Inputs) :
  R.v55574 (state s) (inputs i) = Zmod.unsigned (N.v55574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55574 s i)) at 1.
  unfold R.v55574, N.v55574.
  unfold R.v6, N.v6.
  rewrite ?node_9627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55575 (s : N.State) (i : N.Inputs) :
  R.v55575 (state s) (inputs i) = Zmod.unsigned (N.v55575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55575 s i)) at 1.
  unfold R.v55575, N.v55575.
  rewrite ?node_55573.
  rewrite ?node_55574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55576 (s : N.State) (i : N.Inputs) :
  R.v55576 (state s) (inputs i) = Zmod.unsigned (N.v55576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55576 s i)) at 1.
  unfold R.v55576, N.v55576.
  unfold R.v16484, N.v16484.
  rewrite ?node_55575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55577 (s : N.State) (i : N.Inputs) :
  R.v55577 (state s) (inputs i) = Zmod.unsigned (N.v55577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55577 s i)) at 1.
  unfold R.v55577, N.v55577.
  rewrite ?node_55570.
  rewrite ?node_55571.
  rewrite ?node_55572.
  rewrite ?node_55576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55578 (s : N.State) (i : N.Inputs) :
  R.v55578 (state s) (inputs i) = Zmod.unsigned (N.v55578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55578 s i)) at 1.
  unfold R.v55578, N.v55578.
  unfold R.v6, N.v6.
  rewrite ?node_55577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55579 (s : N.State) (i : N.Inputs) :
  R.v55579 (state s) (inputs i) = Zmod.unsigned (N.v55579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55579 s i)) at 1.
  unfold R.v55579, N.v55579.
  rewrite ?node_9659.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55580 (s : N.State) (i : N.Inputs) :
  R.v55580 (state s) (inputs i) = Zmod.unsigned (N.v55580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55580 s i)) at 1.
  unfold R.v55580, N.v55580.
  unfold R.v6, N.v6.
  rewrite ?node_9808.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55581 (s : N.State) (i : N.Inputs) :
  R.v55581 (state s) (inputs i) = Zmod.unsigned (N.v55581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55581 s i)) at 1.
  unfold R.v55581, N.v55581.
  unfold R.v6, N.v6.
  rewrite ?node_9812.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55582 (s : N.State) (i : N.Inputs) :
  R.v55582 (state s) (inputs i) = Zmod.unsigned (N.v55582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55582 s i)) at 1.
  unfold R.v55582, N.v55582.
  rewrite ?node_55579.
  rewrite ?node_55580.
  rewrite ?node_55581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55583 (s : N.State) (i : N.Inputs) :
  R.v55583 (state s) (inputs i) = Zmod.unsigned (N.v55583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55583 s i)) at 1.
  unfold R.v55583, N.v55583.
  rewrite ?node_55578.
  rewrite ?node_55582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55584 (s : N.State) (i : N.Inputs) :
  R.v55584 (state s) (inputs i) = Zmod.unsigned (N.v55584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55584 s i)) at 1.
  unfold R.v55584, N.v55584.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55585 (s : N.State) (i : N.Inputs) :
  R.v55585 (state s) (inputs i) = Zmod.unsigned (N.v55585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55585 s i)) at 1.
  unfold R.v55585, N.v55585.
  rewrite ?node_9650.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55586 (s : N.State) (i : N.Inputs) :
  R.v55586 (state s) (inputs i) = Zmod.unsigned (N.v55586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55586 s i)) at 1.
  unfold R.v55586, N.v55586.
  unfold R.v6, N.v6.
  rewrite ?node_9646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55587 (s : N.State) (i : N.Inputs) :
  R.v55587 (state s) (inputs i) = Zmod.unsigned (N.v55587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55587 s i)) at 1.
  unfold R.v55587, N.v55587.
  unfold R.v6, N.v6.
  rewrite ?node_9627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55588 (s : N.State) (i : N.Inputs) :
  R.v55588 (state s) (inputs i) = Zmod.unsigned (N.v55588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55588 s i)) at 1.
  unfold R.v55588, N.v55588.
  rewrite ?node_55586.
  rewrite ?node_55587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55589 (s : N.State) (i : N.Inputs) :
  R.v55589 (state s) (inputs i) = Zmod.unsigned (N.v55589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55589 s i)) at 1.
  unfold R.v55589, N.v55589.
  unfold R.v16484, N.v16484.
  rewrite ?node_55588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55590 (s : N.State) (i : N.Inputs) :
  R.v55590 (state s) (inputs i) = Zmod.unsigned (N.v55590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55590 s i)) at 1.
  unfold R.v55590, N.v55590.
  rewrite ?node_55585.
  rewrite ?node_55589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55591 (s : N.State) (i : N.Inputs) :
  R.v55591 (state s) (inputs i) = Zmod.unsigned (N.v55591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55591 s i)) at 1.
  unfold R.v55591, N.v55591.
  unfold R.v6, N.v6.
  rewrite ?node_55590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55592 (s : N.State) (i : N.Inputs) :
  R.v55592 (state s) (inputs i) = Zmod.unsigned (N.v55592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55592 s i)) at 1.
  unfold R.v55592, N.v55592.
  rewrite ?node_9651.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55593 (s : N.State) (i : N.Inputs) :
  R.v55593 (state s) (inputs i) = Zmod.unsigned (N.v55593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55593 s i)) at 1.
  unfold R.v55593, N.v55593.
  unfold R.v6, N.v6.
  rewrite ?node_9808.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55594 (s : N.State) (i : N.Inputs) :
  R.v55594 (state s) (inputs i) = Zmod.unsigned (N.v55594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55594 s i)) at 1.
  unfold R.v55594, N.v55594.
  rewrite ?node_55592.
  rewrite ?node_55593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55595 (s : N.State) (i : N.Inputs) :
  R.v55595 (state s) (inputs i) = Zmod.unsigned (N.v55595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55595 s i)) at 1.
  unfold R.v55595, N.v55595.
  rewrite ?node_55591.
  rewrite ?node_55594.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55596 (s : N.State) (i : N.Inputs) :
  R.v55596 (state s) (inputs i) = Zmod.unsigned (N.v55596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55596 s i)) at 1.
  unfold R.v55596, N.v55596.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55597 (s : N.State) (i : N.Inputs) :
  R.v55597 (state s) (inputs i) = Zmod.unsigned (N.v55597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55597 s i)) at 1.
  unfold R.v55597, N.v55597.
  rewrite ?node_9658.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55598 (s : N.State) (i : N.Inputs) :
  R.v55598 (state s) (inputs i) = Zmod.unsigned (N.v55598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55598 s i)) at 1.
  unfold R.v55598, N.v55598.
  unfold R.v6, N.v6.
  rewrite ?node_9654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55599 (s : N.State) (i : N.Inputs) :
  R.v55599 (state s) (inputs i) = Zmod.unsigned (N.v55599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55599 s i)) at 1.
  unfold R.v55599, N.v55599.
  unfold R.v6, N.v6.
  rewrite ?node_9651.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55600 (s : N.State) (i : N.Inputs) :
  R.v55600 (state s) (inputs i) = Zmod.unsigned (N.v55600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55600 s i)) at 1.
  unfold R.v55600, N.v55600.
  rewrite ?node_55598.
  rewrite ?node_55599.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55601 (s : N.State) (i : N.Inputs) :
  R.v55601 (state s) (inputs i) = Zmod.unsigned (N.v55601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55601 s i)) at 1.
  unfold R.v55601, N.v55601.
  unfold R.v16484, N.v16484.
  rewrite ?node_55600.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55602 (s : N.State) (i : N.Inputs) :
  R.v55602 (state s) (inputs i) = Zmod.unsigned (N.v55602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55602 s i)) at 1.
  unfold R.v55602, N.v55602.
  rewrite ?node_55597.
  rewrite ?node_55601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55603 (s : N.State) (i : N.Inputs) :
  R.v55603 (state s) (inputs i) = Zmod.unsigned (N.v55603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55603 s i)) at 1.
  unfold R.v55603, N.v55603.
  unfold R.v6, N.v6.
  rewrite ?node_55602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55604 (s : N.State) (i : N.Inputs) :
  R.v55604 (state s) (inputs i) = Zmod.unsigned (N.v55604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55604 s i)) at 1.
  unfold R.v55604, N.v55604.
  rewrite ?node_9659.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55605 (s : N.State) (i : N.Inputs) :
  R.v55605 (state s) (inputs i) = Zmod.unsigned (N.v55605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55605 s i)) at 1.
  unfold R.v55605, N.v55605.
  unfold R.v6, N.v6.
  rewrite ?node_9812.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55606 (s : N.State) (i : N.Inputs) :
  R.v55606 (state s) (inputs i) = Zmod.unsigned (N.v55606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55606 s i)) at 1.
  unfold R.v55606, N.v55606.
  rewrite ?node_55604.
  rewrite ?node_55605.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55607 (s : N.State) (i : N.Inputs) :
  R.v55607 (state s) (inputs i) = Zmod.unsigned (N.v55607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55607 s i)) at 1.
  unfold R.v55607, N.v55607.
  rewrite ?node_55603.
  rewrite ?node_55606.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55608 (s : N.State) (i : N.Inputs) :
  R.v55608 (state s) (inputs i) = Zmod.unsigned (N.v55608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55608 s i)) at 1.
  unfold R.v55608, N.v55608.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55609 (s : N.State) (i : N.Inputs) :
  R.v55609 (state s) (inputs i) = Zmod.unsigned (N.v55609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55609 s i)) at 1.
  unfold R.v55609, N.v55609.
  rewrite ?node_9808.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55610 (s : N.State) (i : N.Inputs) :
  R.v55610 (state s) (inputs i) = Zmod.unsigned (N.v55610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55610 s i)) at 1.
  unfold R.v55610, N.v55610.
  rewrite ?node_9804.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55611 (s : N.State) (i : N.Inputs) :
  R.v55611 (state s) (inputs i) = Zmod.unsigned (N.v55611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55611 s i)) at 1.
  unfold R.v55611, N.v55611.
  rewrite ?node_9800.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55612 (s : N.State) (i : N.Inputs) :
  R.v55612 (state s) (inputs i) = Zmod.unsigned (N.v55612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55612 s i)) at 1.
  unfold R.v55612, N.v55612.
  unfold R.v6, N.v6.
  rewrite ?node_9796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55613 (s : N.State) (i : N.Inputs) :
  R.v55613 (state s) (inputs i) = Zmod.unsigned (N.v55613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55613 s i)) at 1.
  unfold R.v55613, N.v55613.
  unfold R.v6, N.v6.
  rewrite ?node_9777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55614 (s : N.State) (i : N.Inputs) :
  R.v55614 (state s) (inputs i) = Zmod.unsigned (N.v55614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55614 s i)) at 1.
  unfold R.v55614, N.v55614.
  rewrite ?node_55612.
  rewrite ?node_55613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55615 (s : N.State) (i : N.Inputs) :
  R.v55615 (state s) (inputs i) = Zmod.unsigned (N.v55615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55615 s i)) at 1.
  unfold R.v55615, N.v55615.
  unfold R.v16484, N.v16484.
  rewrite ?node_55614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55616 (s : N.State) (i : N.Inputs) :
  R.v55616 (state s) (inputs i) = Zmod.unsigned (N.v55616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55616 s i)) at 1.
  unfold R.v55616, N.v55616.
  rewrite ?node_55609.
  rewrite ?node_55610.
  rewrite ?node_55611.
  rewrite ?node_55615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55617 (s : N.State) (i : N.Inputs) :
  R.v55617 (state s) (inputs i) = Zmod.unsigned (N.v55617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55617 s i)) at 1.
  unfold R.v55617, N.v55617.
  unfold R.v6, N.v6.
  rewrite ?node_55616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55618 (s : N.State) (i : N.Inputs) :
  R.v55618 (state s) (inputs i) = Zmod.unsigned (N.v55618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55618 s i)) at 1.
  unfold R.v55618, N.v55618.
  rewrite ?node_9809.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55619 (s : N.State) (i : N.Inputs) :
  R.v55619 (state s) (inputs i) = Zmod.unsigned (N.v55619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55619 s i)) at 1.
  unfold R.v55619, N.v55619.
  unfold R.v6, N.v6.
  rewrite ?node_9960.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55620 (s : N.State) (i : N.Inputs) :
  R.v55620 (state s) (inputs i) = Zmod.unsigned (N.v55620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55620 s i)) at 1.
  unfold R.v55620, N.v55620.
  unfold R.v6, N.v6.
  rewrite ?node_9964.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55621 (s : N.State) (i : N.Inputs) :
  R.v55621 (state s) (inputs i) = Zmod.unsigned (N.v55621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55621 s i)) at 1.
  unfold R.v55621, N.v55621.
  rewrite ?node_55618.
  rewrite ?node_55619.
  rewrite ?node_55620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55622 (s : N.State) (i : N.Inputs) :
  R.v55622 (state s) (inputs i) = Zmod.unsigned (N.v55622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55622 s i)) at 1.
  unfold R.v55622, N.v55622.
  rewrite ?node_55617.
  rewrite ?node_55621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55623 (s : N.State) (i : N.Inputs) :
  R.v55623 (state s) (inputs i) = Zmod.unsigned (N.v55623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55623 s i)) at 1.
  unfold R.v55623, N.v55623.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55624 (s : N.State) (i : N.Inputs) :
  R.v55624 (state s) (inputs i) = Zmod.unsigned (N.v55624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55624 s i)) at 1.
  unfold R.v55624, N.v55624.
  rewrite ?node_9800.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55625 (s : N.State) (i : N.Inputs) :
  R.v55625 (state s) (inputs i) = Zmod.unsigned (N.v55625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55625 s i)) at 1.
  unfold R.v55625, N.v55625.
  unfold R.v6, N.v6.
  rewrite ?node_9796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55626 (s : N.State) (i : N.Inputs) :
  R.v55626 (state s) (inputs i) = Zmod.unsigned (N.v55626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55626 s i)) at 1.
  unfold R.v55626, N.v55626.
  unfold R.v6, N.v6.
  rewrite ?node_9777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55627 (s : N.State) (i : N.Inputs) :
  R.v55627 (state s) (inputs i) = Zmod.unsigned (N.v55627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55627 s i)) at 1.
  unfold R.v55627, N.v55627.
  rewrite ?node_55625.
  rewrite ?node_55626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55628 (s : N.State) (i : N.Inputs) :
  R.v55628 (state s) (inputs i) = Zmod.unsigned (N.v55628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55628 s i)) at 1.
  unfold R.v55628, N.v55628.
  unfold R.v16484, N.v16484.
  rewrite ?node_55627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55629 (s : N.State) (i : N.Inputs) :
  R.v55629 (state s) (inputs i) = Zmod.unsigned (N.v55629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55629 s i)) at 1.
  unfold R.v55629, N.v55629.
  rewrite ?node_55624.
  rewrite ?node_55628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55630 (s : N.State) (i : N.Inputs) :
  R.v55630 (state s) (inputs i) = Zmod.unsigned (N.v55630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55630 s i)) at 1.
  unfold R.v55630, N.v55630.
  unfold R.v6, N.v6.
  rewrite ?node_55629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55631 (s : N.State) (i : N.Inputs) :
  R.v55631 (state s) (inputs i) = Zmod.unsigned (N.v55631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55631 s i)) at 1.
  unfold R.v55631, N.v55631.
  rewrite ?node_9801.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55632 (s : N.State) (i : N.Inputs) :
  R.v55632 (state s) (inputs i) = Zmod.unsigned (N.v55632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55632 s i)) at 1.
  unfold R.v55632, N.v55632.
  unfold R.v6, N.v6.
  rewrite ?node_9960.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55633 (s : N.State) (i : N.Inputs) :
  R.v55633 (state s) (inputs i) = Zmod.unsigned (N.v55633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55633 s i)) at 1.
  unfold R.v55633, N.v55633.
  rewrite ?node_55631.
  rewrite ?node_55632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55634 (s : N.State) (i : N.Inputs) :
  R.v55634 (state s) (inputs i) = Zmod.unsigned (N.v55634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55634 s i)) at 1.
  unfold R.v55634, N.v55634.
  rewrite ?node_55630.
  rewrite ?node_55633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55635 (s : N.State) (i : N.Inputs) :
  R.v55635 (state s) (inputs i) = Zmod.unsigned (N.v55635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55635 s i)) at 1.
  unfold R.v55635, N.v55635.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55636 (s : N.State) (i : N.Inputs) :
  R.v55636 (state s) (inputs i) = Zmod.unsigned (N.v55636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55636 s i)) at 1.
  unfold R.v55636, N.v55636.
  rewrite ?node_9808.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55637 (s : N.State) (i : N.Inputs) :
  R.v55637 (state s) (inputs i) = Zmod.unsigned (N.v55637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55637 s i)) at 1.
  unfold R.v55637, N.v55637.
  unfold R.v6, N.v6.
  rewrite ?node_9804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55638 (s : N.State) (i : N.Inputs) :
  R.v55638 (state s) (inputs i) = Zmod.unsigned (N.v55638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55638 s i)) at 1.
  unfold R.v55638, N.v55638.
  unfold R.v6, N.v6.
  rewrite ?node_9801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55639 (s : N.State) (i : N.Inputs) :
  R.v55639 (state s) (inputs i) = Zmod.unsigned (N.v55639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55639 s i)) at 1.
  unfold R.v55639, N.v55639.
  rewrite ?node_55637.
  rewrite ?node_55638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55640 (s : N.State) (i : N.Inputs) :
  R.v55640 (state s) (inputs i) = Zmod.unsigned (N.v55640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55640 s i)) at 1.
  unfold R.v55640, N.v55640.
  unfold R.v16484, N.v16484.
  rewrite ?node_55639.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55641 (s : N.State) (i : N.Inputs) :
  R.v55641 (state s) (inputs i) = Zmod.unsigned (N.v55641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55641 s i)) at 1.
  unfold R.v55641, N.v55641.
  rewrite ?node_55636.
  rewrite ?node_55640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55642 (s : N.State) (i : N.Inputs) :
  R.v55642 (state s) (inputs i) = Zmod.unsigned (N.v55642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55642 s i)) at 1.
  unfold R.v55642, N.v55642.
  unfold R.v6, N.v6.
  rewrite ?node_55641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55643 (s : N.State) (i : N.Inputs) :
  R.v55643 (state s) (inputs i) = Zmod.unsigned (N.v55643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55643 s i)) at 1.
  unfold R.v55643, N.v55643.
  rewrite ?node_9809.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55644 (s : N.State) (i : N.Inputs) :
  R.v55644 (state s) (inputs i) = Zmod.unsigned (N.v55644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55644 s i)) at 1.
  unfold R.v55644, N.v55644.
  unfold R.v6, N.v6.
  rewrite ?node_9964.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55645 (s : N.State) (i : N.Inputs) :
  R.v55645 (state s) (inputs i) = Zmod.unsigned (N.v55645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55645 s i)) at 1.
  unfold R.v55645, N.v55645.
  rewrite ?node_55643.
  rewrite ?node_55644.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55646 (s : N.State) (i : N.Inputs) :
  R.v55646 (state s) (inputs i) = Zmod.unsigned (N.v55646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55646 s i)) at 1.
  unfold R.v55646, N.v55646.
  rewrite ?node_55642.
  rewrite ?node_55645.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55647 (s : N.State) (i : N.Inputs) :
  R.v55647 (state s) (inputs i) = Zmod.unsigned (N.v55647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55647 s i)) at 1.
  unfold R.v55647, N.v55647.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55648 (s : N.State) (i : N.Inputs) :
  R.v55648 (state s) (inputs i) = Zmod.unsigned (N.v55648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55648 s i)) at 1.
  unfold R.v55648, N.v55648.
  rewrite ?node_9960.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55649 (s : N.State) (i : N.Inputs) :
  R.v55649 (state s) (inputs i) = Zmod.unsigned (N.v55649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55649 s i)) at 1.
  unfold R.v55649, N.v55649.
  rewrite ?node_9956.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55650 (s : N.State) (i : N.Inputs) :
  R.v55650 (state s) (inputs i) = Zmod.unsigned (N.v55650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55650 s i)) at 1.
  unfold R.v55650, N.v55650.
  rewrite ?node_9952.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55651 (s : N.State) (i : N.Inputs) :
  R.v55651 (state s) (inputs i) = Zmod.unsigned (N.v55651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55651 s i)) at 1.
  unfold R.v55651, N.v55651.
  unfold R.v6, N.v6.
  rewrite ?node_9948.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55652 (s : N.State) (i : N.Inputs) :
  R.v55652 (state s) (inputs i) = Zmod.unsigned (N.v55652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55652 s i)) at 1.
  unfold R.v55652, N.v55652.
  unfold R.v6, N.v6.
  rewrite ?node_9929.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55653 (s : N.State) (i : N.Inputs) :
  R.v55653 (state s) (inputs i) = Zmod.unsigned (N.v55653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55653 s i)) at 1.
  unfold R.v55653, N.v55653.
  rewrite ?node_55651.
  rewrite ?node_55652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55654 (s : N.State) (i : N.Inputs) :
  R.v55654 (state s) (inputs i) = Zmod.unsigned (N.v55654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55654 s i)) at 1.
  unfold R.v55654, N.v55654.
  unfold R.v16484, N.v16484.
  rewrite ?node_55653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55655 (s : N.State) (i : N.Inputs) :
  R.v55655 (state s) (inputs i) = Zmod.unsigned (N.v55655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55655 s i)) at 1.
  unfold R.v55655, N.v55655.
  rewrite ?node_55648.
  rewrite ?node_55649.
  rewrite ?node_55650.
  rewrite ?node_55654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55656 (s : N.State) (i : N.Inputs) :
  R.v55656 (state s) (inputs i) = Zmod.unsigned (N.v55656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55656 s i)) at 1.
  unfold R.v55656, N.v55656.
  unfold R.v6, N.v6.
  rewrite ?node_55655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55657 (s : N.State) (i : N.Inputs) :
  R.v55657 (state s) (inputs i) = Zmod.unsigned (N.v55657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55657 s i)) at 1.
  unfold R.v55657, N.v55657.
  rewrite ?node_9961.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55658 (s : N.State) (i : N.Inputs) :
  R.v55658 (state s) (inputs i) = Zmod.unsigned (N.v55658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55658 s i)) at 1.
  unfold R.v55658, N.v55658.
  unfold R.v6, N.v6.
  rewrite ?node_10111.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55659 (s : N.State) (i : N.Inputs) :
  R.v55659 (state s) (inputs i) = Zmod.unsigned (N.v55659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55659 s i)) at 1.
  unfold R.v55659, N.v55659.
  unfold R.v6, N.v6.
  rewrite ?node_10119.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55660 (s : N.State) (i : N.Inputs) :
  R.v55660 (state s) (inputs i) = Zmod.unsigned (N.v55660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55660 s i)) at 1.
  unfold R.v55660, N.v55660.
  rewrite ?node_55657.
  rewrite ?node_55658.
  rewrite ?node_55659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55661 (s : N.State) (i : N.Inputs) :
  R.v55661 (state s) (inputs i) = Zmod.unsigned (N.v55661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55661 s i)) at 1.
  unfold R.v55661, N.v55661.
  rewrite ?node_55656.
  rewrite ?node_55660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55662 (s : N.State) (i : N.Inputs) :
  R.v55662 (state s) (inputs i) = Zmod.unsigned (N.v55662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55662 s i)) at 1.
  unfold R.v55662, N.v55662.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55663 (s : N.State) (i : N.Inputs) :
  R.v55663 (state s) (inputs i) = Zmod.unsigned (N.v55663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55663 s i)) at 1.
  unfold R.v55663, N.v55663.
  rewrite ?node_9952.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55664 (s : N.State) (i : N.Inputs) :
  R.v55664 (state s) (inputs i) = Zmod.unsigned (N.v55664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55664 s i)) at 1.
  unfold R.v55664, N.v55664.
  unfold R.v6, N.v6.
  rewrite ?node_9948.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55665 (s : N.State) (i : N.Inputs) :
  R.v55665 (state s) (inputs i) = Zmod.unsigned (N.v55665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55665 s i)) at 1.
  unfold R.v55665, N.v55665.
  unfold R.v6, N.v6.
  rewrite ?node_9929.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55666 (s : N.State) (i : N.Inputs) :
  R.v55666 (state s) (inputs i) = Zmod.unsigned (N.v55666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55666 s i)) at 1.
  unfold R.v55666, N.v55666.
  rewrite ?node_55664.
  rewrite ?node_55665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55667 (s : N.State) (i : N.Inputs) :
  R.v55667 (state s) (inputs i) = Zmod.unsigned (N.v55667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55667 s i)) at 1.
  unfold R.v55667, N.v55667.
  unfold R.v16484, N.v16484.
  rewrite ?node_55666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55668 (s : N.State) (i : N.Inputs) :
  R.v55668 (state s) (inputs i) = Zmod.unsigned (N.v55668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55668 s i)) at 1.
  unfold R.v55668, N.v55668.
  rewrite ?node_55663.
  rewrite ?node_55667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55669 (s : N.State) (i : N.Inputs) :
  R.v55669 (state s) (inputs i) = Zmod.unsigned (N.v55669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55669 s i)) at 1.
  unfold R.v55669, N.v55669.
  unfold R.v6, N.v6.
  rewrite ?node_55668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55670 (s : N.State) (i : N.Inputs) :
  R.v55670 (state s) (inputs i) = Zmod.unsigned (N.v55670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55670 s i)) at 1.
  unfold R.v55670, N.v55670.
  rewrite ?node_9953.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55671 (s : N.State) (i : N.Inputs) :
  R.v55671 (state s) (inputs i) = Zmod.unsigned (N.v55671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55671 s i)) at 1.
  unfold R.v55671, N.v55671.
  unfold R.v6, N.v6.
  rewrite ?node_10111.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55672 (s : N.State) (i : N.Inputs) :
  R.v55672 (state s) (inputs i) = Zmod.unsigned (N.v55672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55672 s i)) at 1.
  unfold R.v55672, N.v55672.
  rewrite ?node_55670.
  rewrite ?node_55671.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55673 (s : N.State) (i : N.Inputs) :
  R.v55673 (state s) (inputs i) = Zmod.unsigned (N.v55673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55673 s i)) at 1.
  unfold R.v55673, N.v55673.
  rewrite ?node_55669.
  rewrite ?node_55672.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55674 (s : N.State) (i : N.Inputs) :
  R.v55674 (state s) (inputs i) = Zmod.unsigned (N.v55674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55674 s i)) at 1.
  unfold R.v55674, N.v55674.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55675 (s : N.State) (i : N.Inputs) :
  R.v55675 (state s) (inputs i) = Zmod.unsigned (N.v55675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55675 s i)) at 1.
  unfold R.v55675, N.v55675.
  rewrite ?node_9960.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55676 (s : N.State) (i : N.Inputs) :
  R.v55676 (state s) (inputs i) = Zmod.unsigned (N.v55676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55676 s i)) at 1.
  unfold R.v55676, N.v55676.
  unfold R.v6, N.v6.
  rewrite ?node_9956.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55677 (s : N.State) (i : N.Inputs) :
  R.v55677 (state s) (inputs i) = Zmod.unsigned (N.v55677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55677 s i)) at 1.
  unfold R.v55677, N.v55677.
  unfold R.v6, N.v6.
  rewrite ?node_9953.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55678 (s : N.State) (i : N.Inputs) :
  R.v55678 (state s) (inputs i) = Zmod.unsigned (N.v55678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55678 s i)) at 1.
  unfold R.v55678, N.v55678.
  rewrite ?node_55676.
  rewrite ?node_55677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55679 (s : N.State) (i : N.Inputs) :
  R.v55679 (state s) (inputs i) = Zmod.unsigned (N.v55679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55679 s i)) at 1.
  unfold R.v55679, N.v55679.
  unfold R.v16484, N.v16484.
  rewrite ?node_55678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55680 (s : N.State) (i : N.Inputs) :
  R.v55680 (state s) (inputs i) = Zmod.unsigned (N.v55680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55680 s i)) at 1.
  unfold R.v55680, N.v55680.
  rewrite ?node_55675.
  rewrite ?node_55679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55681 (s : N.State) (i : N.Inputs) :
  R.v55681 (state s) (inputs i) = Zmod.unsigned (N.v55681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55681 s i)) at 1.
  unfold R.v55681, N.v55681.
  unfold R.v6, N.v6.
  rewrite ?node_55680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55682 (s : N.State) (i : N.Inputs) :
  R.v55682 (state s) (inputs i) = Zmod.unsigned (N.v55682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55682 s i)) at 1.
  unfold R.v55682, N.v55682.
  rewrite ?node_9961.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55683 (s : N.State) (i : N.Inputs) :
  R.v55683 (state s) (inputs i) = Zmod.unsigned (N.v55683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55683 s i)) at 1.
  unfold R.v55683, N.v55683.
  unfold R.v6, N.v6.
  rewrite ?node_10119.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55684 (s : N.State) (i : N.Inputs) :
  R.v55684 (state s) (inputs i) = Zmod.unsigned (N.v55684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55684 s i)) at 1.
  unfold R.v55684, N.v55684.
  rewrite ?node_55682.
  rewrite ?node_55683.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55685 (s : N.State) (i : N.Inputs) :
  R.v55685 (state s) (inputs i) = Zmod.unsigned (N.v55685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55685 s i)) at 1.
  unfold R.v55685, N.v55685.
  rewrite ?node_55681.
  rewrite ?node_55684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55686 (s : N.State) (i : N.Inputs) :
  R.v55686 (state s) (inputs i) = Zmod.unsigned (N.v55686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55686 s i)) at 1.
  unfold R.v55686, N.v55686.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55687 (s : N.State) (i : N.Inputs) :
  R.v55687 (state s) (inputs i) = Zmod.unsigned (N.v55687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55687 s i)) at 1.
  unfold R.v55687, N.v55687.
  rewrite ?node_10111.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55688 (s : N.State) (i : N.Inputs) :
  R.v55688 (state s) (inputs i) = Zmod.unsigned (N.v55688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55688 s i)) at 1.
  unfold R.v55688, N.v55688.
  rewrite ?node_10107.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55689 (s : N.State) (i : N.Inputs) :
  R.v55689 (state s) (inputs i) = Zmod.unsigned (N.v55689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55689 s i)) at 1.
  unfold R.v55689, N.v55689.
  rewrite ?node_10103.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55690 (s : N.State) (i : N.Inputs) :
  R.v55690 (state s) (inputs i) = Zmod.unsigned (N.v55690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55690 s i)) at 1.
  unfold R.v55690, N.v55690.
  unfold R.v6, N.v6.
  rewrite ?node_10099.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55691 (s : N.State) (i : N.Inputs) :
  R.v55691 (state s) (inputs i) = Zmod.unsigned (N.v55691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55691 s i)) at 1.
  unfold R.v55691, N.v55691.
  unfold R.v6, N.v6.
  rewrite ?node_10080.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55692 (s : N.State) (i : N.Inputs) :
  R.v55692 (state s) (inputs i) = Zmod.unsigned (N.v55692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55692 s i)) at 1.
  unfold R.v55692, N.v55692.
  rewrite ?node_55690.
  rewrite ?node_55691.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55693 (s : N.State) (i : N.Inputs) :
  R.v55693 (state s) (inputs i) = Zmod.unsigned (N.v55693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55693 s i)) at 1.
  unfold R.v55693, N.v55693.
  unfold R.v16484, N.v16484.
  rewrite ?node_55692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55694 (s : N.State) (i : N.Inputs) :
  R.v55694 (state s) (inputs i) = Zmod.unsigned (N.v55694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55694 s i)) at 1.
  unfold R.v55694, N.v55694.
  rewrite ?node_55687.
  rewrite ?node_55688.
  rewrite ?node_55689.
  rewrite ?node_55693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55695 (s : N.State) (i : N.Inputs) :
  R.v55695 (state s) (inputs i) = Zmod.unsigned (N.v55695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55695 s i)) at 1.
  unfold R.v55695, N.v55695.
  unfold R.v6, N.v6.
  rewrite ?node_55694.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55696 (s : N.State) (i : N.Inputs) :
  R.v55696 (state s) (inputs i) = Zmod.unsigned (N.v55696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55696 s i)) at 1.
  unfold R.v55696, N.v55696.
  rewrite ?node_10112.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55697 (s : N.State) (i : N.Inputs) :
  R.v55697 (state s) (inputs i) = Zmod.unsigned (N.v55697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55697 s i)) at 1.
  unfold R.v55697, N.v55697.
  unfold R.v6, N.v6.
  rewrite ?node_10266.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55698 (s : N.State) (i : N.Inputs) :
  R.v55698 (state s) (inputs i) = Zmod.unsigned (N.v55698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55698 s i)) at 1.
  unfold R.v55698, N.v55698.
  unfold R.v6, N.v6.
  rewrite ?node_10274.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55699 (s : N.State) (i : N.Inputs) :
  R.v55699 (state s) (inputs i) = Zmod.unsigned (N.v55699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55699 s i)) at 1.
  unfold R.v55699, N.v55699.
  rewrite ?node_55696.
  rewrite ?node_55697.
  rewrite ?node_55698.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55700 (s : N.State) (i : N.Inputs) :
  R.v55700 (state s) (inputs i) = Zmod.unsigned (N.v55700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55700 s i)) at 1.
  unfold R.v55700, N.v55700.
  rewrite ?node_55695.
  rewrite ?node_55699.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55701 (s : N.State) (i : N.Inputs) :
  R.v55701 (state s) (inputs i) = Zmod.unsigned (N.v55701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55701 s i)) at 1.
  unfold R.v55701, N.v55701.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55702 (s : N.State) (i : N.Inputs) :
  R.v55702 (state s) (inputs i) = Zmod.unsigned (N.v55702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55702 s i)) at 1.
  unfold R.v55702, N.v55702.
  rewrite ?node_10103.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55703 (s : N.State) (i : N.Inputs) :
  R.v55703 (state s) (inputs i) = Zmod.unsigned (N.v55703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55703 s i)) at 1.
  unfold R.v55703, N.v55703.
  unfold R.v6, N.v6.
  rewrite ?node_10099.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55704 (s : N.State) (i : N.Inputs) :
  R.v55704 (state s) (inputs i) = Zmod.unsigned (N.v55704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55704 s i)) at 1.
  unfold R.v55704, N.v55704.
  unfold R.v6, N.v6.
  rewrite ?node_10080.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55705 (s : N.State) (i : N.Inputs) :
  R.v55705 (state s) (inputs i) = Zmod.unsigned (N.v55705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55705 s i)) at 1.
  unfold R.v55705, N.v55705.
  rewrite ?node_55703.
  rewrite ?node_55704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55706 (s : N.State) (i : N.Inputs) :
  R.v55706 (state s) (inputs i) = Zmod.unsigned (N.v55706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55706 s i)) at 1.
  unfold R.v55706, N.v55706.
  unfold R.v16484, N.v16484.
  rewrite ?node_55705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55707 (s : N.State) (i : N.Inputs) :
  R.v55707 (state s) (inputs i) = Zmod.unsigned (N.v55707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55707 s i)) at 1.
  unfold R.v55707, N.v55707.
  rewrite ?node_55702.
  rewrite ?node_55706.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55708 (s : N.State) (i : N.Inputs) :
  R.v55708 (state s) (inputs i) = Zmod.unsigned (N.v55708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55708 s i)) at 1.
  unfold R.v55708, N.v55708.
  unfold R.v6, N.v6.
  rewrite ?node_55707.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55709 (s : N.State) (i : N.Inputs) :
  R.v55709 (state s) (inputs i) = Zmod.unsigned (N.v55709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55709 s i)) at 1.
  unfold R.v55709, N.v55709.
  rewrite ?node_10104.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55710 (s : N.State) (i : N.Inputs) :
  R.v55710 (state s) (inputs i) = Zmod.unsigned (N.v55710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55710 s i)) at 1.
  unfold R.v55710, N.v55710.
  unfold R.v6, N.v6.
  rewrite ?node_10266.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55711 (s : N.State) (i : N.Inputs) :
  R.v55711 (state s) (inputs i) = Zmod.unsigned (N.v55711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55711 s i)) at 1.
  unfold R.v55711, N.v55711.
  rewrite ?node_55709.
  rewrite ?node_55710.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55712 (s : N.State) (i : N.Inputs) :
  R.v55712 (state s) (inputs i) = Zmod.unsigned (N.v55712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55712 s i)) at 1.
  unfold R.v55712, N.v55712.
  rewrite ?node_55708.
  rewrite ?node_55711.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55713 (s : N.State) (i : N.Inputs) :
  R.v55713 (state s) (inputs i) = Zmod.unsigned (N.v55713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55713 s i)) at 1.
  unfold R.v55713, N.v55713.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55714 (s : N.State) (i : N.Inputs) :
  R.v55714 (state s) (inputs i) = Zmod.unsigned (N.v55714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55714 s i)) at 1.
  unfold R.v55714, N.v55714.
  rewrite ?node_10111.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55715 (s : N.State) (i : N.Inputs) :
  R.v55715 (state s) (inputs i) = Zmod.unsigned (N.v55715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55715 s i)) at 1.
  unfold R.v55715, N.v55715.
  unfold R.v6, N.v6.
  rewrite ?node_10107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55716 (s : N.State) (i : N.Inputs) :
  R.v55716 (state s) (inputs i) = Zmod.unsigned (N.v55716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55716 s i)) at 1.
  unfold R.v55716, N.v55716.
  unfold R.v6, N.v6.
  rewrite ?node_10104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55717 (s : N.State) (i : N.Inputs) :
  R.v55717 (state s) (inputs i) = Zmod.unsigned (N.v55717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55717 s i)) at 1.
  unfold R.v55717, N.v55717.
  rewrite ?node_55715.
  rewrite ?node_55716.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55718 (s : N.State) (i : N.Inputs) :
  R.v55718 (state s) (inputs i) = Zmod.unsigned (N.v55718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55718 s i)) at 1.
  unfold R.v55718, N.v55718.
  unfold R.v16484, N.v16484.
  rewrite ?node_55717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55719 (s : N.State) (i : N.Inputs) :
  R.v55719 (state s) (inputs i) = Zmod.unsigned (N.v55719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55719 s i)) at 1.
  unfold R.v55719, N.v55719.
  rewrite ?node_55714.
  rewrite ?node_55718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55720 (s : N.State) (i : N.Inputs) :
  R.v55720 (state s) (inputs i) = Zmod.unsigned (N.v55720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55720 s i)) at 1.
  unfold R.v55720, N.v55720.
  unfold R.v6, N.v6.
  rewrite ?node_55719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55721 (s : N.State) (i : N.Inputs) :
  R.v55721 (state s) (inputs i) = Zmod.unsigned (N.v55721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55721 s i)) at 1.
  unfold R.v55721, N.v55721.
  rewrite ?node_10112.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55722 (s : N.State) (i : N.Inputs) :
  R.v55722 (state s) (inputs i) = Zmod.unsigned (N.v55722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55722 s i)) at 1.
  unfold R.v55722, N.v55722.
  unfold R.v6, N.v6.
  rewrite ?node_10274.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55723 (s : N.State) (i : N.Inputs) :
  R.v55723 (state s) (inputs i) = Zmod.unsigned (N.v55723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55723 s i)) at 1.
  unfold R.v55723, N.v55723.
  rewrite ?node_55721.
  rewrite ?node_55722.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55724 (s : N.State) (i : N.Inputs) :
  R.v55724 (state s) (inputs i) = Zmod.unsigned (N.v55724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55724 s i)) at 1.
  unfold R.v55724, N.v55724.
  rewrite ?node_55720.
  rewrite ?node_55723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55725 (s : N.State) (i : N.Inputs) :
  R.v55725 (state s) (inputs i) = Zmod.unsigned (N.v55725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55725 s i)) at 1.
  unfold R.v55725, N.v55725.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55726 (s : N.State) (i : N.Inputs) :
  R.v55726 (state s) (inputs i) = Zmod.unsigned (N.v55726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55726 s i)) at 1.
  unfold R.v55726, N.v55726.
  rewrite ?node_10266.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55727 (s : N.State) (i : N.Inputs) :
  R.v55727 (state s) (inputs i) = Zmod.unsigned (N.v55727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55727 s i)) at 1.
  unfold R.v55727, N.v55727.
  rewrite ?node_10262.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55728 (s : N.State) (i : N.Inputs) :
  R.v55728 (state s) (inputs i) = Zmod.unsigned (N.v55728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55728 s i)) at 1.
  unfold R.v55728, N.v55728.
  rewrite ?node_10258.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55729 (s : N.State) (i : N.Inputs) :
  R.v55729 (state s) (inputs i) = Zmod.unsigned (N.v55729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55729 s i)) at 1.
  unfold R.v55729, N.v55729.
  unfold R.v6, N.v6.
  rewrite ?node_10254.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55730 (s : N.State) (i : N.Inputs) :
  R.v55730 (state s) (inputs i) = Zmod.unsigned (N.v55730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55730 s i)) at 1.
  unfold R.v55730, N.v55730.
  unfold R.v6, N.v6.
  rewrite ?node_10235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55731 (s : N.State) (i : N.Inputs) :
  R.v55731 (state s) (inputs i) = Zmod.unsigned (N.v55731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55731 s i)) at 1.
  unfold R.v55731, N.v55731.
  rewrite ?node_55729.
  rewrite ?node_55730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55732 (s : N.State) (i : N.Inputs) :
  R.v55732 (state s) (inputs i) = Zmod.unsigned (N.v55732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55732 s i)) at 1.
  unfold R.v55732, N.v55732.
  unfold R.v16484, N.v16484.
  rewrite ?node_55731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55733 (s : N.State) (i : N.Inputs) :
  R.v55733 (state s) (inputs i) = Zmod.unsigned (N.v55733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55733 s i)) at 1.
  unfold R.v55733, N.v55733.
  rewrite ?node_55726.
  rewrite ?node_55727.
  rewrite ?node_55728.
  rewrite ?node_55732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55734 (s : N.State) (i : N.Inputs) :
  R.v55734 (state s) (inputs i) = Zmod.unsigned (N.v55734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55734 s i)) at 1.
  unfold R.v55734, N.v55734.
  unfold R.v6, N.v6.
  rewrite ?node_55733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55735 (s : N.State) (i : N.Inputs) :
  R.v55735 (state s) (inputs i) = Zmod.unsigned (N.v55735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55735 s i)) at 1.
  unfold R.v55735, N.v55735.
  rewrite ?node_10267.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55736 (s : N.State) (i : N.Inputs) :
  R.v55736 (state s) (inputs i) = Zmod.unsigned (N.v55736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55736 s i)) at 1.
  unfold R.v55736, N.v55736.
  unfold R.v6, N.v6.
  rewrite ?node_10424.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55737 (s : N.State) (i : N.Inputs) :
  R.v55737 (state s) (inputs i) = Zmod.unsigned (N.v55737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55737 s i)) at 1.
  unfold R.v55737, N.v55737.
  unfold R.v6, N.v6.
  rewrite ?node_10432.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55738 (s : N.State) (i : N.Inputs) :
  R.v55738 (state s) (inputs i) = Zmod.unsigned (N.v55738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55738 s i)) at 1.
  unfold R.v55738, N.v55738.
  rewrite ?node_55735.
  rewrite ?node_55736.
  rewrite ?node_55737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55739 (s : N.State) (i : N.Inputs) :
  R.v55739 (state s) (inputs i) = Zmod.unsigned (N.v55739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55739 s i)) at 1.
  unfold R.v55739, N.v55739.
  rewrite ?node_55734.
  rewrite ?node_55738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55740 (s : N.State) (i : N.Inputs) :
  R.v55740 (state s) (inputs i) = Zmod.unsigned (N.v55740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55740 s i)) at 1.
  unfold R.v55740, N.v55740.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55741 (s : N.State) (i : N.Inputs) :
  R.v55741 (state s) (inputs i) = Zmod.unsigned (N.v55741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55741 s i)) at 1.
  unfold R.v55741, N.v55741.
  rewrite ?node_10258.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55742 (s : N.State) (i : N.Inputs) :
  R.v55742 (state s) (inputs i) = Zmod.unsigned (N.v55742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55742 s i)) at 1.
  unfold R.v55742, N.v55742.
  unfold R.v6, N.v6.
  rewrite ?node_10254.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55743 (s : N.State) (i : N.Inputs) :
  R.v55743 (state s) (inputs i) = Zmod.unsigned (N.v55743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55743 s i)) at 1.
  unfold R.v55743, N.v55743.
  unfold R.v6, N.v6.
  rewrite ?node_10235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55744 (s : N.State) (i : N.Inputs) :
  R.v55744 (state s) (inputs i) = Zmod.unsigned (N.v55744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55744 s i)) at 1.
  unfold R.v55744, N.v55744.
  rewrite ?node_55742.
  rewrite ?node_55743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55745 (s : N.State) (i : N.Inputs) :
  R.v55745 (state s) (inputs i) = Zmod.unsigned (N.v55745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55745 s i)) at 1.
  unfold R.v55745, N.v55745.
  unfold R.v16484, N.v16484.
  rewrite ?node_55744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55746 (s : N.State) (i : N.Inputs) :
  R.v55746 (state s) (inputs i) = Zmod.unsigned (N.v55746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55746 s i)) at 1.
  unfold R.v55746, N.v55746.
  rewrite ?node_55741.
  rewrite ?node_55745.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55747 (s : N.State) (i : N.Inputs) :
  R.v55747 (state s) (inputs i) = Zmod.unsigned (N.v55747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55747 s i)) at 1.
  unfold R.v55747, N.v55747.
  unfold R.v6, N.v6.
  rewrite ?node_55746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55748 (s : N.State) (i : N.Inputs) :
  R.v55748 (state s) (inputs i) = Zmod.unsigned (N.v55748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55748 s i)) at 1.
  unfold R.v55748, N.v55748.
  rewrite ?node_10259.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55749 (s : N.State) (i : N.Inputs) :
  R.v55749 (state s) (inputs i) = Zmod.unsigned (N.v55749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55749 s i)) at 1.
  unfold R.v55749, N.v55749.
  unfold R.v6, N.v6.
  rewrite ?node_10424.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55750 (s : N.State) (i : N.Inputs) :
  R.v55750 (state s) (inputs i) = Zmod.unsigned (N.v55750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55750 s i)) at 1.
  unfold R.v55750, N.v55750.
  rewrite ?node_55748.
  rewrite ?node_55749.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55751 (s : N.State) (i : N.Inputs) :
  R.v55751 (state s) (inputs i) = Zmod.unsigned (N.v55751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55751 s i)) at 1.
  unfold R.v55751, N.v55751.
  rewrite ?node_55747.
  rewrite ?node_55750.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55752 (s : N.State) (i : N.Inputs) :
  R.v55752 (state s) (inputs i) = Zmod.unsigned (N.v55752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55752 s i)) at 1.
  unfold R.v55752, N.v55752.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55753 (s : N.State) (i : N.Inputs) :
  R.v55753 (state s) (inputs i) = Zmod.unsigned (N.v55753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55753 s i)) at 1.
  unfold R.v55753, N.v55753.
  rewrite ?node_10266.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55754 (s : N.State) (i : N.Inputs) :
  R.v55754 (state s) (inputs i) = Zmod.unsigned (N.v55754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55754 s i)) at 1.
  unfold R.v55754, N.v55754.
  unfold R.v6, N.v6.
  rewrite ?node_10262.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55755 (s : N.State) (i : N.Inputs) :
  R.v55755 (state s) (inputs i) = Zmod.unsigned (N.v55755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55755 s i)) at 1.
  unfold R.v55755, N.v55755.
  unfold R.v6, N.v6.
  rewrite ?node_10259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55756 (s : N.State) (i : N.Inputs) :
  R.v55756 (state s) (inputs i) = Zmod.unsigned (N.v55756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55756 s i)) at 1.
  unfold R.v55756, N.v55756.
  rewrite ?node_55754.
  rewrite ?node_55755.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55757 (s : N.State) (i : N.Inputs) :
  R.v55757 (state s) (inputs i) = Zmod.unsigned (N.v55757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55757 s i)) at 1.
  unfold R.v55757, N.v55757.
  unfold R.v16484, N.v16484.
  rewrite ?node_55756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55758 (s : N.State) (i : N.Inputs) :
  R.v55758 (state s) (inputs i) = Zmod.unsigned (N.v55758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55758 s i)) at 1.
  unfold R.v55758, N.v55758.
  rewrite ?node_55753.
  rewrite ?node_55757.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55759 (s : N.State) (i : N.Inputs) :
  R.v55759 (state s) (inputs i) = Zmod.unsigned (N.v55759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55759 s i)) at 1.
  unfold R.v55759, N.v55759.
  unfold R.v6, N.v6.
  rewrite ?node_55758.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55760 (s : N.State) (i : N.Inputs) :
  R.v55760 (state s) (inputs i) = Zmod.unsigned (N.v55760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55760 s i)) at 1.
  unfold R.v55760, N.v55760.
  rewrite ?node_10267.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55761 (s : N.State) (i : N.Inputs) :
  R.v55761 (state s) (inputs i) = Zmod.unsigned (N.v55761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55761 s i)) at 1.
  unfold R.v55761, N.v55761.
  unfold R.v6, N.v6.
  rewrite ?node_10432.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55762 (s : N.State) (i : N.Inputs) :
  R.v55762 (state s) (inputs i) = Zmod.unsigned (N.v55762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55762 s i)) at 1.
  unfold R.v55762, N.v55762.
  rewrite ?node_55760.
  rewrite ?node_55761.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55763 (s : N.State) (i : N.Inputs) :
  R.v55763 (state s) (inputs i) = Zmod.unsigned (N.v55763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55763 s i)) at 1.
  unfold R.v55763, N.v55763.
  rewrite ?node_55759.
  rewrite ?node_55762.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55764 (s : N.State) (i : N.Inputs) :
  R.v55764 (state s) (inputs i) = Zmod.unsigned (N.v55764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55764 s i)) at 1.
  unfold R.v55764, N.v55764.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55765 (s : N.State) (i : N.Inputs) :
  R.v55765 (state s) (inputs i) = Zmod.unsigned (N.v55765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55765 s i)) at 1.
  unfold R.v55765, N.v55765.
  rewrite ?node_10424.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55766 (s : N.State) (i : N.Inputs) :
  R.v55766 (state s) (inputs i) = Zmod.unsigned (N.v55766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55766 s i)) at 1.
  unfold R.v55766, N.v55766.
  rewrite ?node_10420.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55767 (s : N.State) (i : N.Inputs) :
  R.v55767 (state s) (inputs i) = Zmod.unsigned (N.v55767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55767 s i)) at 1.
  unfold R.v55767, N.v55767.
  rewrite ?node_10416.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55768 (s : N.State) (i : N.Inputs) :
  R.v55768 (state s) (inputs i) = Zmod.unsigned (N.v55768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55768 s i)) at 1.
  unfold R.v55768, N.v55768.
  unfold R.v6, N.v6.
  rewrite ?node_10412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55769 (s : N.State) (i : N.Inputs) :
  R.v55769 (state s) (inputs i) = Zmod.unsigned (N.v55769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55769 s i)) at 1.
  unfold R.v55769, N.v55769.
  unfold R.v6, N.v6.
  rewrite ?node_10393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55770 (s : N.State) (i : N.Inputs) :
  R.v55770 (state s) (inputs i) = Zmod.unsigned (N.v55770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55770 s i)) at 1.
  unfold R.v55770, N.v55770.
  rewrite ?node_55768.
  rewrite ?node_55769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55771 (s : N.State) (i : N.Inputs) :
  R.v55771 (state s) (inputs i) = Zmod.unsigned (N.v55771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55771 s i)) at 1.
  unfold R.v55771, N.v55771.
  unfold R.v16484, N.v16484.
  rewrite ?node_55770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55772 (s : N.State) (i : N.Inputs) :
  R.v55772 (state s) (inputs i) = Zmod.unsigned (N.v55772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55772 s i)) at 1.
  unfold R.v55772, N.v55772.
  rewrite ?node_55765.
  rewrite ?node_55766.
  rewrite ?node_55767.
  rewrite ?node_55771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55773 (s : N.State) (i : N.Inputs) :
  R.v55773 (state s) (inputs i) = Zmod.unsigned (N.v55773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55773 s i)) at 1.
  unfold R.v55773, N.v55773.
  unfold R.v6, N.v6.
  rewrite ?node_55772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55774 (s : N.State) (i : N.Inputs) :
  R.v55774 (state s) (inputs i) = Zmod.unsigned (N.v55774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55774 s i)) at 1.
  unfold R.v55774, N.v55774.
  rewrite ?node_10425.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55775 (s : N.State) (i : N.Inputs) :
  R.v55775 (state s) (inputs i) = Zmod.unsigned (N.v55775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55775 s i)) at 1.
  unfold R.v55775, N.v55775.
  unfold R.v6, N.v6.
  rewrite ?node_10584.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55776 (s : N.State) (i : N.Inputs) :
  R.v55776 (state s) (inputs i) = Zmod.unsigned (N.v55776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55776 s i)) at 1.
  unfold R.v55776, N.v55776.
  unfold R.v6, N.v6.
  rewrite ?node_10592.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55777 (s : N.State) (i : N.Inputs) :
  R.v55777 (state s) (inputs i) = Zmod.unsigned (N.v55777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55777 s i)) at 1.
  unfold R.v55777, N.v55777.
  rewrite ?node_55774.
  rewrite ?node_55775.
  rewrite ?node_55776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55778 (s : N.State) (i : N.Inputs) :
  R.v55778 (state s) (inputs i) = Zmod.unsigned (N.v55778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55778 s i)) at 1.
  unfold R.v55778, N.v55778.
  rewrite ?node_55773.
  rewrite ?node_55777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55779 (s : N.State) (i : N.Inputs) :
  R.v55779 (state s) (inputs i) = Zmod.unsigned (N.v55779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55779 s i)) at 1.
  unfold R.v55779, N.v55779.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55780 (s : N.State) (i : N.Inputs) :
  R.v55780 (state s) (inputs i) = Zmod.unsigned (N.v55780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55780 s i)) at 1.
  unfold R.v55780, N.v55780.
  rewrite ?node_10416.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55781 (s : N.State) (i : N.Inputs) :
  R.v55781 (state s) (inputs i) = Zmod.unsigned (N.v55781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55781 s i)) at 1.
  unfold R.v55781, N.v55781.
  unfold R.v6, N.v6.
  rewrite ?node_10412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55782 (s : N.State) (i : N.Inputs) :
  R.v55782 (state s) (inputs i) = Zmod.unsigned (N.v55782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55782 s i)) at 1.
  unfold R.v55782, N.v55782.
  unfold R.v6, N.v6.
  rewrite ?node_10393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55783 (s : N.State) (i : N.Inputs) :
  R.v55783 (state s) (inputs i) = Zmod.unsigned (N.v55783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55783 s i)) at 1.
  unfold R.v55783, N.v55783.
  rewrite ?node_55781.
  rewrite ?node_55782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55784 (s : N.State) (i : N.Inputs) :
  R.v55784 (state s) (inputs i) = Zmod.unsigned (N.v55784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55784 s i)) at 1.
  unfold R.v55784, N.v55784.
  unfold R.v16484, N.v16484.
  rewrite ?node_55783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55785 (s : N.State) (i : N.Inputs) :
  R.v55785 (state s) (inputs i) = Zmod.unsigned (N.v55785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55785 s i)) at 1.
  unfold R.v55785, N.v55785.
  rewrite ?node_55780.
  rewrite ?node_55784.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55786 (s : N.State) (i : N.Inputs) :
  R.v55786 (state s) (inputs i) = Zmod.unsigned (N.v55786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55786 s i)) at 1.
  unfold R.v55786, N.v55786.
  unfold R.v6, N.v6.
  rewrite ?node_55785.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55787 (s : N.State) (i : N.Inputs) :
  R.v55787 (state s) (inputs i) = Zmod.unsigned (N.v55787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55787 s i)) at 1.
  unfold R.v55787, N.v55787.
  rewrite ?node_10417.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55788 (s : N.State) (i : N.Inputs) :
  R.v55788 (state s) (inputs i) = Zmod.unsigned (N.v55788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55788 s i)) at 1.
  unfold R.v55788, N.v55788.
  unfold R.v6, N.v6.
  rewrite ?node_10584.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55789 (s : N.State) (i : N.Inputs) :
  R.v55789 (state s) (inputs i) = Zmod.unsigned (N.v55789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55789 s i)) at 1.
  unfold R.v55789, N.v55789.
  rewrite ?node_55787.
  rewrite ?node_55788.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55790 (s : N.State) (i : N.Inputs) :
  R.v55790 (state s) (inputs i) = Zmod.unsigned (N.v55790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55790 s i)) at 1.
  unfold R.v55790, N.v55790.
  rewrite ?node_55786.
  rewrite ?node_55789.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55791 (s : N.State) (i : N.Inputs) :
  R.v55791 (state s) (inputs i) = Zmod.unsigned (N.v55791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55791 s i)) at 1.
  unfold R.v55791, N.v55791.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55792 (s : N.State) (i : N.Inputs) :
  R.v55792 (state s) (inputs i) = Zmod.unsigned (N.v55792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55792 s i)) at 1.
  unfold R.v55792, N.v55792.
  rewrite ?node_10424.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55793 (s : N.State) (i : N.Inputs) :
  R.v55793 (state s) (inputs i) = Zmod.unsigned (N.v55793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55793 s i)) at 1.
  unfold R.v55793, N.v55793.
  unfold R.v6, N.v6.
  rewrite ?node_10420.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55794 (s : N.State) (i : N.Inputs) :
  R.v55794 (state s) (inputs i) = Zmod.unsigned (N.v55794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55794 s i)) at 1.
  unfold R.v55794, N.v55794.
  unfold R.v6, N.v6.
  rewrite ?node_10417.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55795 (s : N.State) (i : N.Inputs) :
  R.v55795 (state s) (inputs i) = Zmod.unsigned (N.v55795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55795 s i)) at 1.
  unfold R.v55795, N.v55795.
  rewrite ?node_55793.
  rewrite ?node_55794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55796 (s : N.State) (i : N.Inputs) :
  R.v55796 (state s) (inputs i) = Zmod.unsigned (N.v55796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55796 s i)) at 1.
  unfold R.v55796, N.v55796.
  unfold R.v16484, N.v16484.
  rewrite ?node_55795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55797 (s : N.State) (i : N.Inputs) :
  R.v55797 (state s) (inputs i) = Zmod.unsigned (N.v55797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55797 s i)) at 1.
  unfold R.v55797, N.v55797.
  rewrite ?node_55792.
  rewrite ?node_55796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55798 (s : N.State) (i : N.Inputs) :
  R.v55798 (state s) (inputs i) = Zmod.unsigned (N.v55798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55798 s i)) at 1.
  unfold R.v55798, N.v55798.
  unfold R.v6, N.v6.
  rewrite ?node_55797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55799 (s : N.State) (i : N.Inputs) :
  R.v55799 (state s) (inputs i) = Zmod.unsigned (N.v55799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55799 s i)) at 1.
  unfold R.v55799, N.v55799.
  rewrite ?node_10425.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55800 (s : N.State) (i : N.Inputs) :
  R.v55800 (state s) (inputs i) = Zmod.unsigned (N.v55800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55800 s i)) at 1.
  unfold R.v55800, N.v55800.
  unfold R.v6, N.v6.
  rewrite ?node_10592.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55801 (s : N.State) (i : N.Inputs) :
  R.v55801 (state s) (inputs i) = Zmod.unsigned (N.v55801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55801 s i)) at 1.
  unfold R.v55801, N.v55801.
  rewrite ?node_55799.
  rewrite ?node_55800.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55802 (s : N.State) (i : N.Inputs) :
  R.v55802 (state s) (inputs i) = Zmod.unsigned (N.v55802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55802 s i)) at 1.
  unfold R.v55802, N.v55802.
  rewrite ?node_55798.
  rewrite ?node_55801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55803 (s : N.State) (i : N.Inputs) :
  R.v55803 (state s) (inputs i) = Zmod.unsigned (N.v55803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55803 s i)) at 1.
  unfold R.v55803, N.v55803.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55804 (s : N.State) (i : N.Inputs) :
  R.v55804 (state s) (inputs i) = Zmod.unsigned (N.v55804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55804 s i)) at 1.
  unfold R.v55804, N.v55804.
  rewrite ?node_10584.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55805 (s : N.State) (i : N.Inputs) :
  R.v55805 (state s) (inputs i) = Zmod.unsigned (N.v55805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55805 s i)) at 1.
  unfold R.v55805, N.v55805.
  rewrite ?node_10580.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55806 (s : N.State) (i : N.Inputs) :
  R.v55806 (state s) (inputs i) = Zmod.unsigned (N.v55806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55806 s i)) at 1.
  unfold R.v55806, N.v55806.
  rewrite ?node_10576.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55807 (s : N.State) (i : N.Inputs) :
  R.v55807 (state s) (inputs i) = Zmod.unsigned (N.v55807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55807 s i)) at 1.
  unfold R.v55807, N.v55807.
  unfold R.v6, N.v6.
  rewrite ?node_10572.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55808 (s : N.State) (i : N.Inputs) :
  R.v55808 (state s) (inputs i) = Zmod.unsigned (N.v55808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55808 s i)) at 1.
  unfold R.v55808, N.v55808.
  unfold R.v6, N.v6.
  rewrite ?node_10551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55809 (s : N.State) (i : N.Inputs) :
  R.v55809 (state s) (inputs i) = Zmod.unsigned (N.v55809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55809 s i)) at 1.
  unfold R.v55809, N.v55809.
  rewrite ?node_55807.
  rewrite ?node_55808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55810 (s : N.State) (i : N.Inputs) :
  R.v55810 (state s) (inputs i) = Zmod.unsigned (N.v55810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55810 s i)) at 1.
  unfold R.v55810, N.v55810.
  unfold R.v16484, N.v16484.
  rewrite ?node_55809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55811 (s : N.State) (i : N.Inputs) :
  R.v55811 (state s) (inputs i) = Zmod.unsigned (N.v55811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55811 s i)) at 1.
  unfold R.v55811, N.v55811.
  rewrite ?node_55804.
  rewrite ?node_55805.
  rewrite ?node_55806.
  rewrite ?node_55810.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55812 (s : N.State) (i : N.Inputs) :
  R.v55812 (state s) (inputs i) = Zmod.unsigned (N.v55812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55812 s i)) at 1.
  unfold R.v55812, N.v55812.
  unfold R.v6, N.v6.
  rewrite ?node_55811.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55813 (s : N.State) (i : N.Inputs) :
  R.v55813 (state s) (inputs i) = Zmod.unsigned (N.v55813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55813 s i)) at 1.
  unfold R.v55813, N.v55813.
  rewrite ?node_10585.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55814 (s : N.State) (i : N.Inputs) :
  R.v55814 (state s) (inputs i) = Zmod.unsigned (N.v55814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55814 s i)) at 1.
  unfold R.v55814, N.v55814.
  unfold R.v6, N.v6.
  rewrite ?node_10745.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55815 (s : N.State) (i : N.Inputs) :
  R.v55815 (state s) (inputs i) = Zmod.unsigned (N.v55815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55815 s i)) at 1.
  unfold R.v55815, N.v55815.
  unfold R.v6, N.v6.
  rewrite ?node_10753.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55816 (s : N.State) (i : N.Inputs) :
  R.v55816 (state s) (inputs i) = Zmod.unsigned (N.v55816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55816 s i)) at 1.
  unfold R.v55816, N.v55816.
  rewrite ?node_55813.
  rewrite ?node_55814.
  rewrite ?node_55815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55817 (s : N.State) (i : N.Inputs) :
  R.v55817 (state s) (inputs i) = Zmod.unsigned (N.v55817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55817 s i)) at 1.
  unfold R.v55817, N.v55817.
  rewrite ?node_55812.
  rewrite ?node_55816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55818 (s : N.State) (i : N.Inputs) :
  R.v55818 (state s) (inputs i) = Zmod.unsigned (N.v55818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55818 s i)) at 1.
  unfold R.v55818, N.v55818.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55819 (s : N.State) (i : N.Inputs) :
  R.v55819 (state s) (inputs i) = Zmod.unsigned (N.v55819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55819 s i)) at 1.
  unfold R.v55819, N.v55819.
  rewrite ?node_10576.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55820 (s : N.State) (i : N.Inputs) :
  R.v55820 (state s) (inputs i) = Zmod.unsigned (N.v55820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55820 s i)) at 1.
  unfold R.v55820, N.v55820.
  unfold R.v6, N.v6.
  rewrite ?node_10572.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55821 (s : N.State) (i : N.Inputs) :
  R.v55821 (state s) (inputs i) = Zmod.unsigned (N.v55821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55821 s i)) at 1.
  unfold R.v55821, N.v55821.
  unfold R.v6, N.v6.
  rewrite ?node_10551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55822 (s : N.State) (i : N.Inputs) :
  R.v55822 (state s) (inputs i) = Zmod.unsigned (N.v55822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55822 s i)) at 1.
  unfold R.v55822, N.v55822.
  rewrite ?node_55820.
  rewrite ?node_55821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55823 (s : N.State) (i : N.Inputs) :
  R.v55823 (state s) (inputs i) = Zmod.unsigned (N.v55823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55823 s i)) at 1.
  unfold R.v55823, N.v55823.
  unfold R.v16484, N.v16484.
  rewrite ?node_55822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55824 (s : N.State) (i : N.Inputs) :
  R.v55824 (state s) (inputs i) = Zmod.unsigned (N.v55824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55824 s i)) at 1.
  unfold R.v55824, N.v55824.
  rewrite ?node_55819.
  rewrite ?node_55823.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55825 (s : N.State) (i : N.Inputs) :
  R.v55825 (state s) (inputs i) = Zmod.unsigned (N.v55825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55825 s i)) at 1.
  unfold R.v55825, N.v55825.
  unfold R.v6, N.v6.
  rewrite ?node_55824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55826 (s : N.State) (i : N.Inputs) :
  R.v55826 (state s) (inputs i) = Zmod.unsigned (N.v55826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55826 s i)) at 1.
  unfold R.v55826, N.v55826.
  rewrite ?node_10577.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55827 (s : N.State) (i : N.Inputs) :
  R.v55827 (state s) (inputs i) = Zmod.unsigned (N.v55827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55827 s i)) at 1.
  unfold R.v55827, N.v55827.
  unfold R.v6, N.v6.
  rewrite ?node_10745.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55828 (s : N.State) (i : N.Inputs) :
  R.v55828 (state s) (inputs i) = Zmod.unsigned (N.v55828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55828 s i)) at 1.
  unfold R.v55828, N.v55828.
  rewrite ?node_55826.
  rewrite ?node_55827.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55829 (s : N.State) (i : N.Inputs) :
  R.v55829 (state s) (inputs i) = Zmod.unsigned (N.v55829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55829 s i)) at 1.
  unfold R.v55829, N.v55829.
  rewrite ?node_55825.
  rewrite ?node_55828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55830 (s : N.State) (i : N.Inputs) :
  R.v55830 (state s) (inputs i) = Zmod.unsigned (N.v55830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55830 s i)) at 1.
  unfold R.v55830, N.v55830.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55831 (s : N.State) (i : N.Inputs) :
  R.v55831 (state s) (inputs i) = Zmod.unsigned (N.v55831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55831 s i)) at 1.
  unfold R.v55831, N.v55831.
  rewrite ?node_10584.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55832 (s : N.State) (i : N.Inputs) :
  R.v55832 (state s) (inputs i) = Zmod.unsigned (N.v55832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55832 s i)) at 1.
  unfold R.v55832, N.v55832.
  unfold R.v6, N.v6.
  rewrite ?node_10580.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55833 (s : N.State) (i : N.Inputs) :
  R.v55833 (state s) (inputs i) = Zmod.unsigned (N.v55833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55833 s i)) at 1.
  unfold R.v55833, N.v55833.
  unfold R.v6, N.v6.
  rewrite ?node_10577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55834 (s : N.State) (i : N.Inputs) :
  R.v55834 (state s) (inputs i) = Zmod.unsigned (N.v55834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55834 s i)) at 1.
  unfold R.v55834, N.v55834.
  rewrite ?node_55832.
  rewrite ?node_55833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55835 (s : N.State) (i : N.Inputs) :
  R.v55835 (state s) (inputs i) = Zmod.unsigned (N.v55835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55835 s i)) at 1.
  unfold R.v55835, N.v55835.
  unfold R.v16484, N.v16484.
  rewrite ?node_55834.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55836 (s : N.State) (i : N.Inputs) :
  R.v55836 (state s) (inputs i) = Zmod.unsigned (N.v55836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55836 s i)) at 1.
  unfold R.v55836, N.v55836.
  rewrite ?node_55831.
  rewrite ?node_55835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55837 (s : N.State) (i : N.Inputs) :
  R.v55837 (state s) (inputs i) = Zmod.unsigned (N.v55837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55837 s i)) at 1.
  unfold R.v55837, N.v55837.
  unfold R.v6, N.v6.
  rewrite ?node_55836.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55838 (s : N.State) (i : N.Inputs) :
  R.v55838 (state s) (inputs i) = Zmod.unsigned (N.v55838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55838 s i)) at 1.
  unfold R.v55838, N.v55838.
  rewrite ?node_10585.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55839 (s : N.State) (i : N.Inputs) :
  R.v55839 (state s) (inputs i) = Zmod.unsigned (N.v55839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55839 s i)) at 1.
  unfold R.v55839, N.v55839.
  unfold R.v6, N.v6.
  rewrite ?node_10753.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55840 (s : N.State) (i : N.Inputs) :
  R.v55840 (state s) (inputs i) = Zmod.unsigned (N.v55840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55840 s i)) at 1.
  unfold R.v55840, N.v55840.
  rewrite ?node_55838.
  rewrite ?node_55839.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55841 (s : N.State) (i : N.Inputs) :
  R.v55841 (state s) (inputs i) = Zmod.unsigned (N.v55841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55841 s i)) at 1.
  unfold R.v55841, N.v55841.
  rewrite ?node_55837.
  rewrite ?node_55840.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55842 (s : N.State) (i : N.Inputs) :
  R.v55842 (state s) (inputs i) = Zmod.unsigned (N.v55842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55842 s i)) at 1.
  unfold R.v55842, N.v55842.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55843 (s : N.State) (i : N.Inputs) :
  R.v55843 (state s) (inputs i) = Zmod.unsigned (N.v55843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55843 s i)) at 1.
  unfold R.v55843, N.v55843.
  rewrite ?node_10745.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55844 (s : N.State) (i : N.Inputs) :
  R.v55844 (state s) (inputs i) = Zmod.unsigned (N.v55844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55844 s i)) at 1.
  unfold R.v55844, N.v55844.
  rewrite ?node_10741.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55845 (s : N.State) (i : N.Inputs) :
  R.v55845 (state s) (inputs i) = Zmod.unsigned (N.v55845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55845 s i)) at 1.
  unfold R.v55845, N.v55845.
  rewrite ?node_10737.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55846 (s : N.State) (i : N.Inputs) :
  R.v55846 (state s) (inputs i) = Zmod.unsigned (N.v55846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55846 s i)) at 1.
  unfold R.v55846, N.v55846.
  unfold R.v6, N.v6.
  rewrite ?node_10731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55847 (s : N.State) (i : N.Inputs) :
  R.v55847 (state s) (inputs i) = Zmod.unsigned (N.v55847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55847 s i)) at 1.
  unfold R.v55847, N.v55847.
  unfold R.v6, N.v6.
  rewrite ?node_10710.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55848 (s : N.State) (i : N.Inputs) :
  R.v55848 (state s) (inputs i) = Zmod.unsigned (N.v55848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55848 s i)) at 1.
  unfold R.v55848, N.v55848.
  rewrite ?node_55846.
  rewrite ?node_55847.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55849 (s : N.State) (i : N.Inputs) :
  R.v55849 (state s) (inputs i) = Zmod.unsigned (N.v55849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55849 s i)) at 1.
  unfold R.v55849, N.v55849.
  unfold R.v16484, N.v16484.
  rewrite ?node_55848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55850 (s : N.State) (i : N.Inputs) :
  R.v55850 (state s) (inputs i) = Zmod.unsigned (N.v55850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55850 s i)) at 1.
  unfold R.v55850, N.v55850.
  rewrite ?node_55843.
  rewrite ?node_55844.
  rewrite ?node_55845.
  rewrite ?node_55849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55851 (s : N.State) (i : N.Inputs) :
  R.v55851 (state s) (inputs i) = Zmod.unsigned (N.v55851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55851 s i)) at 1.
  unfold R.v55851, N.v55851.
  unfold R.v6, N.v6.
  rewrite ?node_55850.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55852 (s : N.State) (i : N.Inputs) :
  R.v55852 (state s) (inputs i) = Zmod.unsigned (N.v55852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55852 s i)) at 1.
  unfold R.v55852, N.v55852.
  rewrite ?node_10746.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55853 (s : N.State) (i : N.Inputs) :
  R.v55853 (state s) (inputs i) = Zmod.unsigned (N.v55853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55853 s i)) at 1.
  unfold R.v55853, N.v55853.
  unfold R.v6, N.v6.
  rewrite ?node_10904.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55854 (s : N.State) (i : N.Inputs) :
  R.v55854 (state s) (inputs i) = Zmod.unsigned (N.v55854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55854 s i)) at 1.
  unfold R.v55854, N.v55854.
  unfold R.v6, N.v6.
  rewrite ?node_10914.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55855 (s : N.State) (i : N.Inputs) :
  R.v55855 (state s) (inputs i) = Zmod.unsigned (N.v55855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55855 s i)) at 1.
  unfold R.v55855, N.v55855.
  rewrite ?node_55852.
  rewrite ?node_55853.
  rewrite ?node_55854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55856 (s : N.State) (i : N.Inputs) :
  R.v55856 (state s) (inputs i) = Zmod.unsigned (N.v55856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55856 s i)) at 1.
  unfold R.v55856, N.v55856.
  rewrite ?node_55851.
  rewrite ?node_55855.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55857 (s : N.State) (i : N.Inputs) :
  R.v55857 (state s) (inputs i) = Zmod.unsigned (N.v55857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55857 s i)) at 1.
  unfold R.v55857, N.v55857.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55858 (s : N.State) (i : N.Inputs) :
  R.v55858 (state s) (inputs i) = Zmod.unsigned (N.v55858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55858 s i)) at 1.
  unfold R.v55858, N.v55858.
  rewrite ?node_10737.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55859 (s : N.State) (i : N.Inputs) :
  R.v55859 (state s) (inputs i) = Zmod.unsigned (N.v55859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55859 s i)) at 1.
  unfold R.v55859, N.v55859.
  unfold R.v6, N.v6.
  rewrite ?node_10731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55860 (s : N.State) (i : N.Inputs) :
  R.v55860 (state s) (inputs i) = Zmod.unsigned (N.v55860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55860 s i)) at 1.
  unfold R.v55860, N.v55860.
  unfold R.v6, N.v6.
  rewrite ?node_10710.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55861 (s : N.State) (i : N.Inputs) :
  R.v55861 (state s) (inputs i) = Zmod.unsigned (N.v55861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55861 s i)) at 1.
  unfold R.v55861, N.v55861.
  rewrite ?node_55859.
  rewrite ?node_55860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55862 (s : N.State) (i : N.Inputs) :
  R.v55862 (state s) (inputs i) = Zmod.unsigned (N.v55862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55862 s i)) at 1.
  unfold R.v55862, N.v55862.
  unfold R.v16484, N.v16484.
  rewrite ?node_55861.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55863 (s : N.State) (i : N.Inputs) :
  R.v55863 (state s) (inputs i) = Zmod.unsigned (N.v55863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55863 s i)) at 1.
  unfold R.v55863, N.v55863.
  rewrite ?node_55858.
  rewrite ?node_55862.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55864 (s : N.State) (i : N.Inputs) :
  R.v55864 (state s) (inputs i) = Zmod.unsigned (N.v55864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55864 s i)) at 1.
  unfold R.v55864, N.v55864.
  unfold R.v6, N.v6.
  rewrite ?node_55863.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55865 (s : N.State) (i : N.Inputs) :
  R.v55865 (state s) (inputs i) = Zmod.unsigned (N.v55865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55865 s i)) at 1.
  unfold R.v55865, N.v55865.
  rewrite ?node_10738.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55866 (s : N.State) (i : N.Inputs) :
  R.v55866 (state s) (inputs i) = Zmod.unsigned (N.v55866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55866 s i)) at 1.
  unfold R.v55866, N.v55866.
  unfold R.v6, N.v6.
  rewrite ?node_10904.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55867 (s : N.State) (i : N.Inputs) :
  R.v55867 (state s) (inputs i) = Zmod.unsigned (N.v55867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55867 s i)) at 1.
  unfold R.v55867, N.v55867.
  rewrite ?node_55865.
  rewrite ?node_55866.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55868 (s : N.State) (i : N.Inputs) :
  R.v55868 (state s) (inputs i) = Zmod.unsigned (N.v55868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55868 s i)) at 1.
  unfold R.v55868, N.v55868.
  rewrite ?node_55864.
  rewrite ?node_55867.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55869 (s : N.State) (i : N.Inputs) :
  R.v55869 (state s) (inputs i) = Zmod.unsigned (N.v55869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55869 s i)) at 1.
  unfold R.v55869, N.v55869.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55870 (s : N.State) (i : N.Inputs) :
  R.v55870 (state s) (inputs i) = Zmod.unsigned (N.v55870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55870 s i)) at 1.
  unfold R.v55870, N.v55870.
  rewrite ?node_10745.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55871 (s : N.State) (i : N.Inputs) :
  R.v55871 (state s) (inputs i) = Zmod.unsigned (N.v55871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55871 s i)) at 1.
  unfold R.v55871, N.v55871.
  unfold R.v6, N.v6.
  rewrite ?node_10741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55872 (s : N.State) (i : N.Inputs) :
  R.v55872 (state s) (inputs i) = Zmod.unsigned (N.v55872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55872 s i)) at 1.
  unfold R.v55872, N.v55872.
  unfold R.v6, N.v6.
  rewrite ?node_10738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55873 (s : N.State) (i : N.Inputs) :
  R.v55873 (state s) (inputs i) = Zmod.unsigned (N.v55873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55873 s i)) at 1.
  unfold R.v55873, N.v55873.
  rewrite ?node_55871.
  rewrite ?node_55872.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55874 (s : N.State) (i : N.Inputs) :
  R.v55874 (state s) (inputs i) = Zmod.unsigned (N.v55874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55874 s i)) at 1.
  unfold R.v55874, N.v55874.
  unfold R.v16484, N.v16484.
  rewrite ?node_55873.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55875 (s : N.State) (i : N.Inputs) :
  R.v55875 (state s) (inputs i) = Zmod.unsigned (N.v55875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55875 s i)) at 1.
  unfold R.v55875, N.v55875.
  rewrite ?node_55870.
  rewrite ?node_55874.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55876 (s : N.State) (i : N.Inputs) :
  R.v55876 (state s) (inputs i) = Zmod.unsigned (N.v55876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55876 s i)) at 1.
  unfold R.v55876, N.v55876.
  unfold R.v6, N.v6.
  rewrite ?node_55875.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55877 (s : N.State) (i : N.Inputs) :
  R.v55877 (state s) (inputs i) = Zmod.unsigned (N.v55877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55877 s i)) at 1.
  unfold R.v55877, N.v55877.
  rewrite ?node_10746.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55878 (s : N.State) (i : N.Inputs) :
  R.v55878 (state s) (inputs i) = Zmod.unsigned (N.v55878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55878 s i)) at 1.
  unfold R.v55878, N.v55878.
  unfold R.v6, N.v6.
  rewrite ?node_10914.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55879 (s : N.State) (i : N.Inputs) :
  R.v55879 (state s) (inputs i) = Zmod.unsigned (N.v55879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55879 s i)) at 1.
  unfold R.v55879, N.v55879.
  rewrite ?node_55877.
  rewrite ?node_55878.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55880 (s : N.State) (i : N.Inputs) :
  R.v55880 (state s) (inputs i) = Zmod.unsigned (N.v55880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55880 s i)) at 1.
  unfold R.v55880, N.v55880.
  rewrite ?node_55876.
  rewrite ?node_55879.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55881 (s : N.State) (i : N.Inputs) :
  R.v55881 (state s) (inputs i) = Zmod.unsigned (N.v55881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55881 s i)) at 1.
  unfold R.v55881, N.v55881.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55882 (s : N.State) (i : N.Inputs) :
  R.v55882 (state s) (inputs i) = Zmod.unsigned (N.v55882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55882 s i)) at 1.
  unfold R.v55882, N.v55882.
  rewrite ?node_10904.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55883 (s : N.State) (i : N.Inputs) :
  R.v55883 (state s) (inputs i) = Zmod.unsigned (N.v55883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55883 s i)) at 1.
  unfold R.v55883, N.v55883.
  rewrite ?node_10900.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55884 (s : N.State) (i : N.Inputs) :
  R.v55884 (state s) (inputs i) = Zmod.unsigned (N.v55884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55884 s i)) at 1.
  unfold R.v55884, N.v55884.
  rewrite ?node_10896.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55885 (s : N.State) (i : N.Inputs) :
  R.v55885 (state s) (inputs i) = Zmod.unsigned (N.v55885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55885 s i)) at 1.
  unfold R.v55885, N.v55885.
  unfold R.v6, N.v6.
  rewrite ?node_10890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55886 (s : N.State) (i : N.Inputs) :
  R.v55886 (state s) (inputs i) = Zmod.unsigned (N.v55886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55886 s i)) at 1.
  unfold R.v55886, N.v55886.
  unfold R.v6, N.v6.
  rewrite ?node_10871.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55887 (s : N.State) (i : N.Inputs) :
  R.v55887 (state s) (inputs i) = Zmod.unsigned (N.v55887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55887 s i)) at 1.
  unfold R.v55887, N.v55887.
  rewrite ?node_55885.
  rewrite ?node_55886.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55888 (s : N.State) (i : N.Inputs) :
  R.v55888 (state s) (inputs i) = Zmod.unsigned (N.v55888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55888 s i)) at 1.
  unfold R.v55888, N.v55888.
  unfold R.v16484, N.v16484.
  rewrite ?node_55887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55889 (s : N.State) (i : N.Inputs) :
  R.v55889 (state s) (inputs i) = Zmod.unsigned (N.v55889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55889 s i)) at 1.
  unfold R.v55889, N.v55889.
  rewrite ?node_55882.
  rewrite ?node_55883.
  rewrite ?node_55884.
  rewrite ?node_55888.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55890 (s : N.State) (i : N.Inputs) :
  R.v55890 (state s) (inputs i) = Zmod.unsigned (N.v55890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55890 s i)) at 1.
  unfold R.v55890, N.v55890.
  unfold R.v6, N.v6.
  rewrite ?node_55889.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55891 (s : N.State) (i : N.Inputs) :
  R.v55891 (state s) (inputs i) = Zmod.unsigned (N.v55891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55891 s i)) at 1.
  unfold R.v55891, N.v55891.
  rewrite ?node_10905.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55892 (s : N.State) (i : N.Inputs) :
  R.v55892 (state s) (inputs i) = Zmod.unsigned (N.v55892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55892 s i)) at 1.
  unfold R.v55892, N.v55892.
  unfold R.v6, N.v6.
  rewrite ?node_11063.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55893 (s : N.State) (i : N.Inputs) :
  R.v55893 (state s) (inputs i) = Zmod.unsigned (N.v55893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55893 s i)) at 1.
  unfold R.v55893, N.v55893.
  unfold R.v6, N.v6.
  rewrite ?node_11073.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55894 (s : N.State) (i : N.Inputs) :
  R.v55894 (state s) (inputs i) = Zmod.unsigned (N.v55894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55894 s i)) at 1.
  unfold R.v55894, N.v55894.
  rewrite ?node_55891.
  rewrite ?node_55892.
  rewrite ?node_55893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55895 (s : N.State) (i : N.Inputs) :
  R.v55895 (state s) (inputs i) = Zmod.unsigned (N.v55895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55895 s i)) at 1.
  unfold R.v55895, N.v55895.
  rewrite ?node_55890.
  rewrite ?node_55894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55896 (s : N.State) (i : N.Inputs) :
  R.v55896 (state s) (inputs i) = Zmod.unsigned (N.v55896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55896 s i)) at 1.
  unfold R.v55896, N.v55896.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55897 (s : N.State) (i : N.Inputs) :
  R.v55897 (state s) (inputs i) = Zmod.unsigned (N.v55897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55897 s i)) at 1.
  unfold R.v55897, N.v55897.
  rewrite ?node_10896.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55898 (s : N.State) (i : N.Inputs) :
  R.v55898 (state s) (inputs i) = Zmod.unsigned (N.v55898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55898 s i)) at 1.
  unfold R.v55898, N.v55898.
  unfold R.v6, N.v6.
  rewrite ?node_10890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55899 (s : N.State) (i : N.Inputs) :
  R.v55899 (state s) (inputs i) = Zmod.unsigned (N.v55899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55899 s i)) at 1.
  unfold R.v55899, N.v55899.
  unfold R.v6, N.v6.
  rewrite ?node_10871.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55900 (s : N.State) (i : N.Inputs) :
  R.v55900 (state s) (inputs i) = Zmod.unsigned (N.v55900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55900 s i)) at 1.
  unfold R.v55900, N.v55900.
  rewrite ?node_55898.
  rewrite ?node_55899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55901 (s : N.State) (i : N.Inputs) :
  R.v55901 (state s) (inputs i) = Zmod.unsigned (N.v55901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55901 s i)) at 1.
  unfold R.v55901, N.v55901.
  unfold R.v16484, N.v16484.
  rewrite ?node_55900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55902 (s : N.State) (i : N.Inputs) :
  R.v55902 (state s) (inputs i) = Zmod.unsigned (N.v55902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55902 s i)) at 1.
  unfold R.v55902, N.v55902.
  rewrite ?node_55897.
  rewrite ?node_55901.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55903 (s : N.State) (i : N.Inputs) :
  R.v55903 (state s) (inputs i) = Zmod.unsigned (N.v55903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55903 s i)) at 1.
  unfold R.v55903, N.v55903.
  unfold R.v6, N.v6.
  rewrite ?node_55902.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55904 (s : N.State) (i : N.Inputs) :
  R.v55904 (state s) (inputs i) = Zmod.unsigned (N.v55904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55904 s i)) at 1.
  unfold R.v55904, N.v55904.
  rewrite ?node_10897.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55905 (s : N.State) (i : N.Inputs) :
  R.v55905 (state s) (inputs i) = Zmod.unsigned (N.v55905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55905 s i)) at 1.
  unfold R.v55905, N.v55905.
  unfold R.v6, N.v6.
  rewrite ?node_11063.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55906 (s : N.State) (i : N.Inputs) :
  R.v55906 (state s) (inputs i) = Zmod.unsigned (N.v55906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55906 s i)) at 1.
  unfold R.v55906, N.v55906.
  rewrite ?node_55904.
  rewrite ?node_55905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55907 (s : N.State) (i : N.Inputs) :
  R.v55907 (state s) (inputs i) = Zmod.unsigned (N.v55907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55907 s i)) at 1.
  unfold R.v55907, N.v55907.
  rewrite ?node_55903.
  rewrite ?node_55906.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55908 (s : N.State) (i : N.Inputs) :
  R.v55908 (state s) (inputs i) = Zmod.unsigned (N.v55908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55908 s i)) at 1.
  unfold R.v55908, N.v55908.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55909 (s : N.State) (i : N.Inputs) :
  R.v55909 (state s) (inputs i) = Zmod.unsigned (N.v55909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55909 s i)) at 1.
  unfold R.v55909, N.v55909.
  rewrite ?node_10904.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55910 (s : N.State) (i : N.Inputs) :
  R.v55910 (state s) (inputs i) = Zmod.unsigned (N.v55910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55910 s i)) at 1.
  unfold R.v55910, N.v55910.
  unfold R.v6, N.v6.
  rewrite ?node_10900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55911 (s : N.State) (i : N.Inputs) :
  R.v55911 (state s) (inputs i) = Zmod.unsigned (N.v55911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55911 s i)) at 1.
  unfold R.v55911, N.v55911.
  unfold R.v6, N.v6.
  rewrite ?node_10897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55912 (s : N.State) (i : N.Inputs) :
  R.v55912 (state s) (inputs i) = Zmod.unsigned (N.v55912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55912 s i)) at 1.
  unfold R.v55912, N.v55912.
  rewrite ?node_55910.
  rewrite ?node_55911.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55913 (s : N.State) (i : N.Inputs) :
  R.v55913 (state s) (inputs i) = Zmod.unsigned (N.v55913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55913 s i)) at 1.
  unfold R.v55913, N.v55913.
  unfold R.v16484, N.v16484.
  rewrite ?node_55912.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55914 (s : N.State) (i : N.Inputs) :
  R.v55914 (state s) (inputs i) = Zmod.unsigned (N.v55914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55914 s i)) at 1.
  unfold R.v55914, N.v55914.
  rewrite ?node_55909.
  rewrite ?node_55913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55915 (s : N.State) (i : N.Inputs) :
  R.v55915 (state s) (inputs i) = Zmod.unsigned (N.v55915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55915 s i)) at 1.
  unfold R.v55915, N.v55915.
  unfold R.v6, N.v6.
  rewrite ?node_55914.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55916 (s : N.State) (i : N.Inputs) :
  R.v55916 (state s) (inputs i) = Zmod.unsigned (N.v55916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55916 s i)) at 1.
  unfold R.v55916, N.v55916.
  rewrite ?node_10905.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55917 (s : N.State) (i : N.Inputs) :
  R.v55917 (state s) (inputs i) = Zmod.unsigned (N.v55917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55917 s i)) at 1.
  unfold R.v55917, N.v55917.
  unfold R.v6, N.v6.
  rewrite ?node_11073.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55918 (s : N.State) (i : N.Inputs) :
  R.v55918 (state s) (inputs i) = Zmod.unsigned (N.v55918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55918 s i)) at 1.
  unfold R.v55918, N.v55918.
  rewrite ?node_55916.
  rewrite ?node_55917.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55919 (s : N.State) (i : N.Inputs) :
  R.v55919 (state s) (inputs i) = Zmod.unsigned (N.v55919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55919 s i)) at 1.
  unfold R.v55919, N.v55919.
  rewrite ?node_55915.
  rewrite ?node_55918.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55920 (s : N.State) (i : N.Inputs) :
  R.v55920 (state s) (inputs i) = Zmod.unsigned (N.v55920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55920 s i)) at 1.
  unfold R.v55920, N.v55920.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55921 (s : N.State) (i : N.Inputs) :
  R.v55921 (state s) (inputs i) = Zmod.unsigned (N.v55921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55921 s i)) at 1.
  unfold R.v55921, N.v55921.
  unfold R.v6, N.v6.
  rewrite ?node_10909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55922 (s : N.State) (i : N.Inputs) :
  R.v55922 (state s) (inputs i) = Zmod.unsigned (N.v55922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55922 s i)) at 1.
  unfold R.v55922, N.v55922.
  unfold R.v6, N.v6.
  rewrite ?node_10908.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55923 (s : N.State) (i : N.Inputs) :
  R.v55923 (state s) (inputs i) = Zmod.unsigned (N.v55923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55923 s i)) at 1.
  unfold R.v55923, N.v55923.
  rewrite ?node_55921.
  rewrite ?node_55922.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55924 (s : N.State) (i : N.Inputs) :
  R.v55924 (state s) (inputs i) = Zmod.unsigned (N.v55924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55924 s i)) at 1.
  unfold R.v55924, N.v55924.
  unfold R.v16463, N.v16463.
  rewrite ?node_55923.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55925 (s : N.State) (i : N.Inputs) :
  R.v55925 (state s) (inputs i) = Zmod.unsigned (N.v55925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55925 s i)) at 1.
  unfold R.v55925, N.v55925.
  rewrite ?node_10910.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55926 (s : N.State) (i : N.Inputs) :
  R.v55926 (state s) (inputs i) = Zmod.unsigned (N.v55926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55926 s i)) at 1.
  unfold R.v55926, N.v55926.
  unfold R.v6, N.v6.
  rewrite ?node_11075.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55927 (s : N.State) (i : N.Inputs) :
  R.v55927 (state s) (inputs i) = Zmod.unsigned (N.v55927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55927 s i)) at 1.
  unfold R.v55927, N.v55927.
  rewrite ?node_55925.
  rewrite ?node_55926.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55928 (s : N.State) (i : N.Inputs) :
  R.v55928 (state s) (inputs i) = Zmod.unsigned (N.v55928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55928 s i)) at 1.
  unfold R.v55928, N.v55928.
  rewrite ?node_55924.
  rewrite ?node_55927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55929 (s : N.State) (i : N.Inputs) :
  R.v55929 (state s) (inputs i) = Zmod.unsigned (N.v55929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55929 s i)) at 1.
  unfold R.v55929, N.v55929.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55930 (s : N.State) (i : N.Inputs) :
  R.v55930 (state s) (inputs i) = Zmod.unsigned (N.v55930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55930 s i)) at 1.
  unfold R.v55930, N.v55930.
  rewrite ?node_11063.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55931 (s : N.State) (i : N.Inputs) :
  R.v55931 (state s) (inputs i) = Zmod.unsigned (N.v55931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55931 s i)) at 1.
  unfold R.v55931, N.v55931.
  rewrite ?node_11059.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55932 (s : N.State) (i : N.Inputs) :
  R.v55932 (state s) (inputs i) = Zmod.unsigned (N.v55932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55932 s i)) at 1.
  unfold R.v55932, N.v55932.
  rewrite ?node_11055.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55933 (s : N.State) (i : N.Inputs) :
  R.v55933 (state s) (inputs i) = Zmod.unsigned (N.v55933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55933 s i)) at 1.
  unfold R.v55933, N.v55933.
  unfold R.v6, N.v6.
  rewrite ?node_11051.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55934 (s : N.State) (i : N.Inputs) :
  R.v55934 (state s) (inputs i) = Zmod.unsigned (N.v55934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55934 s i)) at 1.
  unfold R.v55934, N.v55934.
  unfold R.v6, N.v6.
  rewrite ?node_11032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55935 (s : N.State) (i : N.Inputs) :
  R.v55935 (state s) (inputs i) = Zmod.unsigned (N.v55935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55935 s i)) at 1.
  unfold R.v55935, N.v55935.
  rewrite ?node_55933.
  rewrite ?node_55934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55936 (s : N.State) (i : N.Inputs) :
  R.v55936 (state s) (inputs i) = Zmod.unsigned (N.v55936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55936 s i)) at 1.
  unfold R.v55936, N.v55936.
  unfold R.v16484, N.v16484.
  rewrite ?node_55935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55937 (s : N.State) (i : N.Inputs) :
  R.v55937 (state s) (inputs i) = Zmod.unsigned (N.v55937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55937 s i)) at 1.
  unfold R.v55937, N.v55937.
  rewrite ?node_55930.
  rewrite ?node_55931.
  rewrite ?node_55932.
  rewrite ?node_55936.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55938 (s : N.State) (i : N.Inputs) :
  R.v55938 (state s) (inputs i) = Zmod.unsigned (N.v55938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55938 s i)) at 1.
  unfold R.v55938, N.v55938.
  unfold R.v6, N.v6.
  rewrite ?node_55937.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55939 (s : N.State) (i : N.Inputs) :
  R.v55939 (state s) (inputs i) = Zmod.unsigned (N.v55939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55939 s i)) at 1.
  unfold R.v55939, N.v55939.
  rewrite ?node_11064.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55940 (s : N.State) (i : N.Inputs) :
  R.v55940 (state s) (inputs i) = Zmod.unsigned (N.v55940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55940 s i)) at 1.
  unfold R.v55940, N.v55940.
  unfold R.v6, N.v6.
  rewrite ?node_11227.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55941 (s : N.State) (i : N.Inputs) :
  R.v55941 (state s) (inputs i) = Zmod.unsigned (N.v55941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55941 s i)) at 1.
  unfold R.v55941, N.v55941.
  unfold R.v6, N.v6.
  rewrite ?node_11231.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55942 (s : N.State) (i : N.Inputs) :
  R.v55942 (state s) (inputs i) = Zmod.unsigned (N.v55942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55942 s i)) at 1.
  unfold R.v55942, N.v55942.
  rewrite ?node_55939.
  rewrite ?node_55940.
  rewrite ?node_55941.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55943 (s : N.State) (i : N.Inputs) :
  R.v55943 (state s) (inputs i) = Zmod.unsigned (N.v55943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55943 s i)) at 1.
  unfold R.v55943, N.v55943.
  rewrite ?node_55938.
  rewrite ?node_55942.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55944 (s : N.State) (i : N.Inputs) :
  R.v55944 (state s) (inputs i) = Zmod.unsigned (N.v55944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55944 s i)) at 1.
  unfold R.v55944, N.v55944.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55945 (s : N.State) (i : N.Inputs) :
  R.v55945 (state s) (inputs i) = Zmod.unsigned (N.v55945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55945 s i)) at 1.
  unfold R.v55945, N.v55945.
  rewrite ?node_11055.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55946 (s : N.State) (i : N.Inputs) :
  R.v55946 (state s) (inputs i) = Zmod.unsigned (N.v55946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55946 s i)) at 1.
  unfold R.v55946, N.v55946.
  unfold R.v6, N.v6.
  rewrite ?node_11051.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55947 (s : N.State) (i : N.Inputs) :
  R.v55947 (state s) (inputs i) = Zmod.unsigned (N.v55947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55947 s i)) at 1.
  unfold R.v55947, N.v55947.
  unfold R.v6, N.v6.
  rewrite ?node_11032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55948 (s : N.State) (i : N.Inputs) :
  R.v55948 (state s) (inputs i) = Zmod.unsigned (N.v55948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55948 s i)) at 1.
  unfold R.v55948, N.v55948.
  rewrite ?node_55946.
  rewrite ?node_55947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55949 (s : N.State) (i : N.Inputs) :
  R.v55949 (state s) (inputs i) = Zmod.unsigned (N.v55949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55949 s i)) at 1.
  unfold R.v55949, N.v55949.
  unfold R.v16484, N.v16484.
  rewrite ?node_55948.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55950 (s : N.State) (i : N.Inputs) :
  R.v55950 (state s) (inputs i) = Zmod.unsigned (N.v55950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55950 s i)) at 1.
  unfold R.v55950, N.v55950.
  rewrite ?node_55945.
  rewrite ?node_55949.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55951 (s : N.State) (i : N.Inputs) :
  R.v55951 (state s) (inputs i) = Zmod.unsigned (N.v55951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55951 s i)) at 1.
  unfold R.v55951, N.v55951.
  unfold R.v6, N.v6.
  rewrite ?node_55950.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55952 (s : N.State) (i : N.Inputs) :
  R.v55952 (state s) (inputs i) = Zmod.unsigned (N.v55952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55952 s i)) at 1.
  unfold R.v55952, N.v55952.
  rewrite ?node_11056.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55953 (s : N.State) (i : N.Inputs) :
  R.v55953 (state s) (inputs i) = Zmod.unsigned (N.v55953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55953 s i)) at 1.
  unfold R.v55953, N.v55953.
  unfold R.v6, N.v6.
  rewrite ?node_11227.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55954 (s : N.State) (i : N.Inputs) :
  R.v55954 (state s) (inputs i) = Zmod.unsigned (N.v55954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55954 s i)) at 1.
  unfold R.v55954, N.v55954.
  rewrite ?node_55952.
  rewrite ?node_55953.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55955 (s : N.State) (i : N.Inputs) :
  R.v55955 (state s) (inputs i) = Zmod.unsigned (N.v55955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55955 s i)) at 1.
  unfold R.v55955, N.v55955.
  rewrite ?node_55951.
  rewrite ?node_55954.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55956 (s : N.State) (i : N.Inputs) :
  R.v55956 (state s) (inputs i) = Zmod.unsigned (N.v55956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55956 s i)) at 1.
  unfold R.v55956, N.v55956.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55957 (s : N.State) (i : N.Inputs) :
  R.v55957 (state s) (inputs i) = Zmod.unsigned (N.v55957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55957 s i)) at 1.
  unfold R.v55957, N.v55957.
  rewrite ?node_11063.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55958 (s : N.State) (i : N.Inputs) :
  R.v55958 (state s) (inputs i) = Zmod.unsigned (N.v55958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55958 s i)) at 1.
  unfold R.v55958, N.v55958.
  unfold R.v6, N.v6.
  rewrite ?node_11059.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55959 (s : N.State) (i : N.Inputs) :
  R.v55959 (state s) (inputs i) = Zmod.unsigned (N.v55959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55959 s i)) at 1.
  unfold R.v55959, N.v55959.
  unfold R.v6, N.v6.
  rewrite ?node_11056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55960 (s : N.State) (i : N.Inputs) :
  R.v55960 (state s) (inputs i) = Zmod.unsigned (N.v55960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55960 s i)) at 1.
  unfold R.v55960, N.v55960.
  rewrite ?node_55958.
  rewrite ?node_55959.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55961 (s : N.State) (i : N.Inputs) :
  R.v55961 (state s) (inputs i) = Zmod.unsigned (N.v55961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55961 s i)) at 1.
  unfold R.v55961, N.v55961.
  unfold R.v16484, N.v16484.
  rewrite ?node_55960.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55962 (s : N.State) (i : N.Inputs) :
  R.v55962 (state s) (inputs i) = Zmod.unsigned (N.v55962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55962 s i)) at 1.
  unfold R.v55962, N.v55962.
  rewrite ?node_55957.
  rewrite ?node_55961.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55963 (s : N.State) (i : N.Inputs) :
  R.v55963 (state s) (inputs i) = Zmod.unsigned (N.v55963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55963 s i)) at 1.
  unfold R.v55963, N.v55963.
  unfold R.v6, N.v6.
  rewrite ?node_55962.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55964 (s : N.State) (i : N.Inputs) :
  R.v55964 (state s) (inputs i) = Zmod.unsigned (N.v55964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55964 s i)) at 1.
  unfold R.v55964, N.v55964.
  rewrite ?node_11064.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55965 (s : N.State) (i : N.Inputs) :
  R.v55965 (state s) (inputs i) = Zmod.unsigned (N.v55965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55965 s i)) at 1.
  unfold R.v55965, N.v55965.
  unfold R.v6, N.v6.
  rewrite ?node_11231.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55966 (s : N.State) (i : N.Inputs) :
  R.v55966 (state s) (inputs i) = Zmod.unsigned (N.v55966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55966 s i)) at 1.
  unfold R.v55966, N.v55966.
  rewrite ?node_55964.
  rewrite ?node_55965.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55967 (s : N.State) (i : N.Inputs) :
  R.v55967 (state s) (inputs i) = Zmod.unsigned (N.v55967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55967 s i)) at 1.
  unfold R.v55967, N.v55967.
  rewrite ?node_55963.
  rewrite ?node_55966.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55968 (s : N.State) (i : N.Inputs) :
  R.v55968 (state s) (inputs i) = Zmod.unsigned (N.v55968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55968 s i)) at 1.
  unfold R.v55968, N.v55968.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55969 (s : N.State) (i : N.Inputs) :
  R.v55969 (state s) (inputs i) = Zmod.unsigned (N.v55969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55969 s i)) at 1.
  unfold R.v55969, N.v55969.
  unfold R.v6, N.v6.
  rewrite ?node_11068.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55970 (s : N.State) (i : N.Inputs) :
  R.v55970 (state s) (inputs i) = Zmod.unsigned (N.v55970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55970 s i)) at 1.
  unfold R.v55970, N.v55970.
  unfold R.v6, N.v6.
  rewrite ?node_11067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55971 (s : N.State) (i : N.Inputs) :
  R.v55971 (state s) (inputs i) = Zmod.unsigned (N.v55971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55971 s i)) at 1.
  unfold R.v55971, N.v55971.
  rewrite ?node_55969.
  rewrite ?node_55970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55972 (s : N.State) (i : N.Inputs) :
  R.v55972 (state s) (inputs i) = Zmod.unsigned (N.v55972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55972 s i)) at 1.
  unfold R.v55972, N.v55972.
  unfold R.v16463, N.v16463.
  rewrite ?node_55971.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55973 (s : N.State) (i : N.Inputs) :
  R.v55973 (state s) (inputs i) = Zmod.unsigned (N.v55973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55973 s i)) at 1.
  unfold R.v55973, N.v55973.
  rewrite ?node_11069.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55974 (s : N.State) (i : N.Inputs) :
  R.v55974 (state s) (inputs i) = Zmod.unsigned (N.v55974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55974 s i)) at 1.
  unfold R.v55974, N.v55974.
  unfold R.v6, N.v6.
  rewrite ?node_11233.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55975 (s : N.State) (i : N.Inputs) :
  R.v55975 (state s) (inputs i) = Zmod.unsigned (N.v55975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55975 s i)) at 1.
  unfold R.v55975, N.v55975.
  rewrite ?node_55973.
  rewrite ?node_55974.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55976 (s : N.State) (i : N.Inputs) :
  R.v55976 (state s) (inputs i) = Zmod.unsigned (N.v55976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55976 s i)) at 1.
  unfold R.v55976, N.v55976.
  rewrite ?node_55972.
  rewrite ?node_55975.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55977 (s : N.State) (i : N.Inputs) :
  R.v55977 (state s) (inputs i) = Zmod.unsigned (N.v55977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55977 s i)) at 1.
  unfold R.v55977, N.v55977.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55978 (s : N.State) (i : N.Inputs) :
  R.v55978 (state s) (inputs i) = Zmod.unsigned (N.v55978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55978 s i)) at 1.
  unfold R.v55978, N.v55978.
  rewrite ?node_11227.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55979 (s : N.State) (i : N.Inputs) :
  R.v55979 (state s) (inputs i) = Zmod.unsigned (N.v55979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55979 s i)) at 1.
  unfold R.v55979, N.v55979.
  rewrite ?node_11223.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55980 (s : N.State) (i : N.Inputs) :
  R.v55980 (state s) (inputs i) = Zmod.unsigned (N.v55980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55980 s i)) at 1.
  unfold R.v55980, N.v55980.
  rewrite ?node_11219.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55981 (s : N.State) (i : N.Inputs) :
  R.v55981 (state s) (inputs i) = Zmod.unsigned (N.v55981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55981 s i)) at 1.
  unfold R.v55981, N.v55981.
  unfold R.v6, N.v6.
  rewrite ?node_11215.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55982 (s : N.State) (i : N.Inputs) :
  R.v55982 (state s) (inputs i) = Zmod.unsigned (N.v55982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55982 s i)) at 1.
  unfold R.v55982, N.v55982.
  unfold R.v6, N.v6.
  rewrite ?node_11196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55983 (s : N.State) (i : N.Inputs) :
  R.v55983 (state s) (inputs i) = Zmod.unsigned (N.v55983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55983 s i)) at 1.
  unfold R.v55983, N.v55983.
  rewrite ?node_55981.
  rewrite ?node_55982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55984 (s : N.State) (i : N.Inputs) :
  R.v55984 (state s) (inputs i) = Zmod.unsigned (N.v55984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55984 s i)) at 1.
  unfold R.v55984, N.v55984.
  unfold R.v16484, N.v16484.
  rewrite ?node_55983.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55985 (s : N.State) (i : N.Inputs) :
  R.v55985 (state s) (inputs i) = Zmod.unsigned (N.v55985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55985 s i)) at 1.
  unfold R.v55985, N.v55985.
  rewrite ?node_55978.
  rewrite ?node_55979.
  rewrite ?node_55980.
  rewrite ?node_55984.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55986 (s : N.State) (i : N.Inputs) :
  R.v55986 (state s) (inputs i) = Zmod.unsigned (N.v55986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55986 s i)) at 1.
  unfold R.v55986, N.v55986.
  unfold R.v6, N.v6.
  rewrite ?node_55985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55987 (s : N.State) (i : N.Inputs) :
  R.v55987 (state s) (inputs i) = Zmod.unsigned (N.v55987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55987 s i)) at 1.
  unfold R.v55987, N.v55987.
  rewrite ?node_11228.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55988 (s : N.State) (i : N.Inputs) :
  R.v55988 (state s) (inputs i) = Zmod.unsigned (N.v55988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55988 s i)) at 1.
  unfold R.v55988, N.v55988.
  unfold R.v6, N.v6.
  rewrite ?node_11381.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55989 (s : N.State) (i : N.Inputs) :
  R.v55989 (state s) (inputs i) = Zmod.unsigned (N.v55989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55989 s i)) at 1.
  unfold R.v55989, N.v55989.
  unfold R.v6, N.v6.
  rewrite ?node_11389.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55990 (s : N.State) (i : N.Inputs) :
  R.v55990 (state s) (inputs i) = Zmod.unsigned (N.v55990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55990 s i)) at 1.
  unfold R.v55990, N.v55990.
  rewrite ?node_55987.
  rewrite ?node_55988.
  rewrite ?node_55989.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55991 (s : N.State) (i : N.Inputs) :
  R.v55991 (state s) (inputs i) = Zmod.unsigned (N.v55991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55991 s i)) at 1.
  unfold R.v55991, N.v55991.
  rewrite ?node_55986.
  rewrite ?node_55990.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55992 (s : N.State) (i : N.Inputs) :
  R.v55992 (state s) (inputs i) = Zmod.unsigned (N.v55992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55992 s i)) at 1.
  unfold R.v55992, N.v55992.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55993 (s : N.State) (i : N.Inputs) :
  R.v55993 (state s) (inputs i) = Zmod.unsigned (N.v55993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55993 s i)) at 1.
  unfold R.v55993, N.v55993.
  rewrite ?node_11219.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55994 (s : N.State) (i : N.Inputs) :
  R.v55994 (state s) (inputs i) = Zmod.unsigned (N.v55994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55994 s i)) at 1.
  unfold R.v55994, N.v55994.
  unfold R.v6, N.v6.
  rewrite ?node_11215.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55995 (s : N.State) (i : N.Inputs) :
  R.v55995 (state s) (inputs i) = Zmod.unsigned (N.v55995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55995 s i)) at 1.
  unfold R.v55995, N.v55995.
  unfold R.v6, N.v6.
  rewrite ?node_11196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55996 (s : N.State) (i : N.Inputs) :
  R.v55996 (state s) (inputs i) = Zmod.unsigned (N.v55996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55996 s i)) at 1.
  unfold R.v55996, N.v55996.
  rewrite ?node_55994.
  rewrite ?node_55995.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55997 (s : N.State) (i : N.Inputs) :
  R.v55997 (state s) (inputs i) = Zmod.unsigned (N.v55997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55997 s i)) at 1.
  unfold R.v55997, N.v55997.
  unfold R.v16484, N.v16484.
  rewrite ?node_55996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55998 (s : N.State) (i : N.Inputs) :
  R.v55998 (state s) (inputs i) = Zmod.unsigned (N.v55998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55998 s i)) at 1.
  unfold R.v55998, N.v55998.
  rewrite ?node_55993.
  rewrite ?node_55997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55999 (s : N.State) (i : N.Inputs) :
  R.v55999 (state s) (inputs i) = Zmod.unsigned (N.v55999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55999 s i)) at 1.
  unfold R.v55999, N.v55999.
  unfold R.v6, N.v6.
  rewrite ?node_55998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
