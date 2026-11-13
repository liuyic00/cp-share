(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes049.
Lemma node_50000 (s : N.State) (i : N.Inputs) :
  R.v50000 (state s) (inputs i) = Zmod.unsigned (N.v50000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50000 s i)) at 1.
  unfold R.v50000, N.v50000.
  rewrite ?node_8012.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50001 (s : N.State) (i : N.Inputs) :
  R.v50001 (state s) (inputs i) = Zmod.unsigned (N.v50001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50001 s i)) at 1.
  unfold R.v50001, N.v50001.
  unfold R.v6, N.v6.
  rewrite ?node_7992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50002 (s : N.State) (i : N.Inputs) :
  R.v50002 (state s) (inputs i) = Zmod.unsigned (N.v50002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50002 s i)) at 1.
  unfold R.v50002, N.v50002.
  unfold R.v6, N.v6.
  rewrite ?node_7968.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50003 (s : N.State) (i : N.Inputs) :
  R.v50003 (state s) (inputs i) = Zmod.unsigned (N.v50003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50003 s i)) at 1.
  unfold R.v50003, N.v50003.
  rewrite ?node_50001.
  rewrite ?node_50002.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50004 (s : N.State) (i : N.Inputs) :
  R.v50004 (state s) (inputs i) = Zmod.unsigned (N.v50004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50004 s i)) at 1.
  unfold R.v50004, N.v50004.
  unfold R.v16484, N.v16484.
  rewrite ?node_50003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50005 (s : N.State) (i : N.Inputs) :
  R.v50005 (state s) (inputs i) = Zmod.unsigned (N.v50005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50005 s i)) at 1.
  unfold R.v50005, N.v50005.
  rewrite ?node_50000.
  rewrite ?node_50004.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50006 (s : N.State) (i : N.Inputs) :
  R.v50006 (state s) (inputs i) = Zmod.unsigned (N.v50006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50006 s i)) at 1.
  unfold R.v50006, N.v50006.
  unfold R.v6, N.v6.
  rewrite ?node_50005.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50007 (s : N.State) (i : N.Inputs) :
  R.v50007 (state s) (inputs i) = Zmod.unsigned (N.v50007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50007 s i)) at 1.
  unfold R.v50007, N.v50007.
  rewrite ?node_8013.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50008 (s : N.State) (i : N.Inputs) :
  R.v50008 (state s) (inputs i) = Zmod.unsigned (N.v50008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50008 s i)) at 1.
  unfold R.v50008, N.v50008.
  unfold R.v6, N.v6.
  rewrite ?node_8140.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50009 (s : N.State) (i : N.Inputs) :
  R.v50009 (state s) (inputs i) = Zmod.unsigned (N.v50009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50009 s i)) at 1.
  unfold R.v50009, N.v50009.
  rewrite ?node_50007.
  rewrite ?node_50008.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50010 (s : N.State) (i : N.Inputs) :
  R.v50010 (state s) (inputs i) = Zmod.unsigned (N.v50010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50010 s i)) at 1.
  unfold R.v50010, N.v50010.
  rewrite ?node_50006.
  rewrite ?node_50009.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50011 (s : N.State) (i : N.Inputs) :
  R.v50011 (state s) (inputs i) = Zmod.unsigned (N.v50011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50011 s i)) at 1.
  unfold R.v50011, N.v50011.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50012 (s : N.State) (i : N.Inputs) :
  R.v50012 (state s) (inputs i) = Zmod.unsigned (N.v50012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50012 s i)) at 1.
  unfold R.v50012, N.v50012.
  rewrite ?node_8020.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50013 (s : N.State) (i : N.Inputs) :
  R.v50013 (state s) (inputs i) = Zmod.unsigned (N.v50013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50013 s i)) at 1.
  unfold R.v50013, N.v50013.
  unfold R.v6, N.v6.
  rewrite ?node_8016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50014 (s : N.State) (i : N.Inputs) :
  R.v50014 (state s) (inputs i) = Zmod.unsigned (N.v50014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50014 s i)) at 1.
  unfold R.v50014, N.v50014.
  unfold R.v6, N.v6.
  rewrite ?node_8013.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50015 (s : N.State) (i : N.Inputs) :
  R.v50015 (state s) (inputs i) = Zmod.unsigned (N.v50015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50015 s i)) at 1.
  unfold R.v50015, N.v50015.
  rewrite ?node_50013.
  rewrite ?node_50014.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50016 (s : N.State) (i : N.Inputs) :
  R.v50016 (state s) (inputs i) = Zmod.unsigned (N.v50016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50016 s i)) at 1.
  unfold R.v50016, N.v50016.
  unfold R.v16484, N.v16484.
  rewrite ?node_50015.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50017 (s : N.State) (i : N.Inputs) :
  R.v50017 (state s) (inputs i) = Zmod.unsigned (N.v50017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50017 s i)) at 1.
  unfold R.v50017, N.v50017.
  rewrite ?node_50012.
  rewrite ?node_50016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50018 (s : N.State) (i : N.Inputs) :
  R.v50018 (state s) (inputs i) = Zmod.unsigned (N.v50018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50018 s i)) at 1.
  unfold R.v50018, N.v50018.
  unfold R.v6, N.v6.
  rewrite ?node_50017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50019 (s : N.State) (i : N.Inputs) :
  R.v50019 (state s) (inputs i) = Zmod.unsigned (N.v50019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50019 s i)) at 1.
  unfold R.v50019, N.v50019.
  rewrite ?node_8021.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50020 (s : N.State) (i : N.Inputs) :
  R.v50020 (state s) (inputs i) = Zmod.unsigned (N.v50020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50020 s i)) at 1.
  unfold R.v50020, N.v50020.
  unfold R.v6, N.v6.
  rewrite ?node_8156.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50021 (s : N.State) (i : N.Inputs) :
  R.v50021 (state s) (inputs i) = Zmod.unsigned (N.v50021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50021 s i)) at 1.
  unfold R.v50021, N.v50021.
  rewrite ?node_50019.
  rewrite ?node_50020.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50022 (s : N.State) (i : N.Inputs) :
  R.v50022 (state s) (inputs i) = Zmod.unsigned (N.v50022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50022 s i)) at 1.
  unfold R.v50022, N.v50022.
  rewrite ?node_50018.
  rewrite ?node_50021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50023 (s : N.State) (i : N.Inputs) :
  R.v50023 (state s) (inputs i) = Zmod.unsigned (N.v50023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50023 s i)) at 1.
  unfold R.v50023, N.v50023.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50024 (s : N.State) (i : N.Inputs) :
  R.v50024 (state s) (inputs i) = Zmod.unsigned (N.v50024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50024 s i)) at 1.
  unfold R.v50024, N.v50024.
  rewrite ?node_8031.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50025 (s : N.State) (i : N.Inputs) :
  R.v50025 (state s) (inputs i) = Zmod.unsigned (N.v50025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50025 s i)) at 1.
  unfold R.v50025, N.v50025.
  unfold R.v6, N.v6.
  rewrite ?node_8027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50026 (s : N.State) (i : N.Inputs) :
  R.v50026 (state s) (inputs i) = Zmod.unsigned (N.v50026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50026 s i)) at 1.
  unfold R.v50026, N.v50026.
  unfold R.v6, N.v6.
  rewrite ?node_8024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50027 (s : N.State) (i : N.Inputs) :
  R.v50027 (state s) (inputs i) = Zmod.unsigned (N.v50027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50027 s i)) at 1.
  unfold R.v50027, N.v50027.
  rewrite ?node_50025.
  rewrite ?node_50026.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50028 (s : N.State) (i : N.Inputs) :
  R.v50028 (state s) (inputs i) = Zmod.unsigned (N.v50028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50028 s i)) at 1.
  unfold R.v50028, N.v50028.
  unfold R.v16484, N.v16484.
  rewrite ?node_50027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50029 (s : N.State) (i : N.Inputs) :
  R.v50029 (state s) (inputs i) = Zmod.unsigned (N.v50029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50029 s i)) at 1.
  unfold R.v50029, N.v50029.
  rewrite ?node_50024.
  rewrite ?node_50028.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50030 (s : N.State) (i : N.Inputs) :
  R.v50030 (state s) (inputs i) = Zmod.unsigned (N.v50030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50030 s i)) at 1.
  unfold R.v50030, N.v50030.
  unfold R.v6, N.v6.
  rewrite ?node_50029.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50031 (s : N.State) (i : N.Inputs) :
  R.v50031 (state s) (inputs i) = Zmod.unsigned (N.v50031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50031 s i)) at 1.
  unfold R.v50031, N.v50031.
  rewrite ?node_8032.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50032 (s : N.State) (i : N.Inputs) :
  R.v50032 (state s) (inputs i) = Zmod.unsigned (N.v50032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50032 s i)) at 1.
  unfold R.v50032, N.v50032.
  unfold R.v6, N.v6.
  rewrite ?node_8160.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50033 (s : N.State) (i : N.Inputs) :
  R.v50033 (state s) (inputs i) = Zmod.unsigned (N.v50033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50033 s i)) at 1.
  unfold R.v50033, N.v50033.
  rewrite ?node_50031.
  rewrite ?node_50032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50034 (s : N.State) (i : N.Inputs) :
  R.v50034 (state s) (inputs i) = Zmod.unsigned (N.v50034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50034 s i)) at 1.
  unfold R.v50034, N.v50034.
  rewrite ?node_50030.
  rewrite ?node_50033.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50035 (s : N.State) (i : N.Inputs) :
  R.v50035 (state s) (inputs i) = Zmod.unsigned (N.v50035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50035 s i)) at 1.
  unfold R.v50035, N.v50035.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50036 (s : N.State) (i : N.Inputs) :
  R.v50036 (state s) (inputs i) = Zmod.unsigned (N.v50036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50036 s i)) at 1.
  unfold R.v50036, N.v50036.
  rewrite ?node_8140.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50037 (s : N.State) (i : N.Inputs) :
  R.v50037 (state s) (inputs i) = Zmod.unsigned (N.v50037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50037 s i)) at 1.
  unfold R.v50037, N.v50037.
  rewrite ?node_8136.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50038 (s : N.State) (i : N.Inputs) :
  R.v50038 (state s) (inputs i) = Zmod.unsigned (N.v50038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50038 s i)) at 1.
  unfold R.v50038, N.v50038.
  rewrite ?node_8132.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50039 (s : N.State) (i : N.Inputs) :
  R.v50039 (state s) (inputs i) = Zmod.unsigned (N.v50039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50039 s i)) at 1.
  unfold R.v50039, N.v50039.
  unfold R.v6, N.v6.
  rewrite ?node_8112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50040 (s : N.State) (i : N.Inputs) :
  R.v50040 (state s) (inputs i) = Zmod.unsigned (N.v50040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50040 s i)) at 1.
  unfold R.v50040, N.v50040.
  unfold R.v6, N.v6.
  rewrite ?node_8087.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50041 (s : N.State) (i : N.Inputs) :
  R.v50041 (state s) (inputs i) = Zmod.unsigned (N.v50041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50041 s i)) at 1.
  unfold R.v50041, N.v50041.
  rewrite ?node_50039.
  rewrite ?node_50040.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50042 (s : N.State) (i : N.Inputs) :
  R.v50042 (state s) (inputs i) = Zmod.unsigned (N.v50042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50042 s i)) at 1.
  unfold R.v50042, N.v50042.
  unfold R.v16484, N.v16484.
  rewrite ?node_50041.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50043 (s : N.State) (i : N.Inputs) :
  R.v50043 (state s) (inputs i) = Zmod.unsigned (N.v50043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50043 s i)) at 1.
  unfold R.v50043, N.v50043.
  rewrite ?node_50036.
  rewrite ?node_50037.
  rewrite ?node_50038.
  rewrite ?node_50042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50044 (s : N.State) (i : N.Inputs) :
  R.v50044 (state s) (inputs i) = Zmod.unsigned (N.v50044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50044 s i)) at 1.
  unfold R.v50044, N.v50044.
  unfold R.v6, N.v6.
  rewrite ?node_50043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50045 (s : N.State) (i : N.Inputs) :
  R.v50045 (state s) (inputs i) = Zmod.unsigned (N.v50045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50045 s i)) at 1.
  unfold R.v50045, N.v50045.
  rewrite ?node_8141.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50046 (s : N.State) (i : N.Inputs) :
  R.v50046 (state s) (inputs i) = Zmod.unsigned (N.v50046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50046 s i)) at 1.
  unfold R.v50046, N.v50046.
  unfold R.v6, N.v6.
  rewrite ?node_8262.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50047 (s : N.State) (i : N.Inputs) :
  R.v50047 (state s) (inputs i) = Zmod.unsigned (N.v50047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50047 s i)) at 1.
  unfold R.v50047, N.v50047.
  unfold R.v6, N.v6.
  rewrite ?node_8278.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50048 (s : N.State) (i : N.Inputs) :
  R.v50048 (state s) (inputs i) = Zmod.unsigned (N.v50048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50048 s i)) at 1.
  unfold R.v50048, N.v50048.
  rewrite ?node_50045.
  rewrite ?node_50046.
  rewrite ?node_50047.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50049 (s : N.State) (i : N.Inputs) :
  R.v50049 (state s) (inputs i) = Zmod.unsigned (N.v50049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50049 s i)) at 1.
  unfold R.v50049, N.v50049.
  rewrite ?node_50044.
  rewrite ?node_50048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50050 (s : N.State) (i : N.Inputs) :
  R.v50050 (state s) (inputs i) = Zmod.unsigned (N.v50050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50050 s i)) at 1.
  unfold R.v50050, N.v50050.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50051 (s : N.State) (i : N.Inputs) :
  R.v50051 (state s) (inputs i) = Zmod.unsigned (N.v50051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50051 s i)) at 1.
  unfold R.v50051, N.v50051.
  rewrite ?node_8132.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50052 (s : N.State) (i : N.Inputs) :
  R.v50052 (state s) (inputs i) = Zmod.unsigned (N.v50052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50052 s i)) at 1.
  unfold R.v50052, N.v50052.
  unfold R.v6, N.v6.
  rewrite ?node_8112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50053 (s : N.State) (i : N.Inputs) :
  R.v50053 (state s) (inputs i) = Zmod.unsigned (N.v50053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50053 s i)) at 1.
  unfold R.v50053, N.v50053.
  unfold R.v6, N.v6.
  rewrite ?node_8087.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50054 (s : N.State) (i : N.Inputs) :
  R.v50054 (state s) (inputs i) = Zmod.unsigned (N.v50054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50054 s i)) at 1.
  unfold R.v50054, N.v50054.
  rewrite ?node_50052.
  rewrite ?node_50053.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50055 (s : N.State) (i : N.Inputs) :
  R.v50055 (state s) (inputs i) = Zmod.unsigned (N.v50055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50055 s i)) at 1.
  unfold R.v50055, N.v50055.
  unfold R.v16484, N.v16484.
  rewrite ?node_50054.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50056 (s : N.State) (i : N.Inputs) :
  R.v50056 (state s) (inputs i) = Zmod.unsigned (N.v50056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50056 s i)) at 1.
  unfold R.v50056, N.v50056.
  rewrite ?node_50051.
  rewrite ?node_50055.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50057 (s : N.State) (i : N.Inputs) :
  R.v50057 (state s) (inputs i) = Zmod.unsigned (N.v50057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50057 s i)) at 1.
  unfold R.v50057, N.v50057.
  unfold R.v6, N.v6.
  rewrite ?node_50056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50058 (s : N.State) (i : N.Inputs) :
  R.v50058 (state s) (inputs i) = Zmod.unsigned (N.v50058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50058 s i)) at 1.
  unfold R.v50058, N.v50058.
  rewrite ?node_8133.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50059 (s : N.State) (i : N.Inputs) :
  R.v50059 (state s) (inputs i) = Zmod.unsigned (N.v50059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50059 s i)) at 1.
  unfold R.v50059, N.v50059.
  unfold R.v6, N.v6.
  rewrite ?node_8262.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50060 (s : N.State) (i : N.Inputs) :
  R.v50060 (state s) (inputs i) = Zmod.unsigned (N.v50060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50060 s i)) at 1.
  unfold R.v50060, N.v50060.
  rewrite ?node_50058.
  rewrite ?node_50059.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50061 (s : N.State) (i : N.Inputs) :
  R.v50061 (state s) (inputs i) = Zmod.unsigned (N.v50061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50061 s i)) at 1.
  unfold R.v50061, N.v50061.
  rewrite ?node_50057.
  rewrite ?node_50060.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50062 (s : N.State) (i : N.Inputs) :
  R.v50062 (state s) (inputs i) = Zmod.unsigned (N.v50062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50062 s i)) at 1.
  unfold R.v50062, N.v50062.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50063 (s : N.State) (i : N.Inputs) :
  R.v50063 (state s) (inputs i) = Zmod.unsigned (N.v50063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50063 s i)) at 1.
  unfold R.v50063, N.v50063.
  rewrite ?node_8140.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50064 (s : N.State) (i : N.Inputs) :
  R.v50064 (state s) (inputs i) = Zmod.unsigned (N.v50064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50064 s i)) at 1.
  unfold R.v50064, N.v50064.
  unfold R.v6, N.v6.
  rewrite ?node_8136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50065 (s : N.State) (i : N.Inputs) :
  R.v50065 (state s) (inputs i) = Zmod.unsigned (N.v50065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50065 s i)) at 1.
  unfold R.v50065, N.v50065.
  unfold R.v6, N.v6.
  rewrite ?node_8133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50066 (s : N.State) (i : N.Inputs) :
  R.v50066 (state s) (inputs i) = Zmod.unsigned (N.v50066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50066 s i)) at 1.
  unfold R.v50066, N.v50066.
  rewrite ?node_50064.
  rewrite ?node_50065.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50067 (s : N.State) (i : N.Inputs) :
  R.v50067 (state s) (inputs i) = Zmod.unsigned (N.v50067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50067 s i)) at 1.
  unfold R.v50067, N.v50067.
  unfold R.v16484, N.v16484.
  rewrite ?node_50066.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50068 (s : N.State) (i : N.Inputs) :
  R.v50068 (state s) (inputs i) = Zmod.unsigned (N.v50068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50068 s i)) at 1.
  unfold R.v50068, N.v50068.
  rewrite ?node_50063.
  rewrite ?node_50067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50069 (s : N.State) (i : N.Inputs) :
  R.v50069 (state s) (inputs i) = Zmod.unsigned (N.v50069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50069 s i)) at 1.
  unfold R.v50069, N.v50069.
  unfold R.v6, N.v6.
  rewrite ?node_50068.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50070 (s : N.State) (i : N.Inputs) :
  R.v50070 (state s) (inputs i) = Zmod.unsigned (N.v50070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50070 s i)) at 1.
  unfold R.v50070, N.v50070.
  rewrite ?node_8141.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50071 (s : N.State) (i : N.Inputs) :
  R.v50071 (state s) (inputs i) = Zmod.unsigned (N.v50071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50071 s i)) at 1.
  unfold R.v50071, N.v50071.
  unfold R.v6, N.v6.
  rewrite ?node_8278.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50072 (s : N.State) (i : N.Inputs) :
  R.v50072 (state s) (inputs i) = Zmod.unsigned (N.v50072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50072 s i)) at 1.
  unfold R.v50072, N.v50072.
  rewrite ?node_50070.
  rewrite ?node_50071.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50073 (s : N.State) (i : N.Inputs) :
  R.v50073 (state s) (inputs i) = Zmod.unsigned (N.v50073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50073 s i)) at 1.
  unfold R.v50073, N.v50073.
  rewrite ?node_50069.
  rewrite ?node_50072.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50074 (s : N.State) (i : N.Inputs) :
  R.v50074 (state s) (inputs i) = Zmod.unsigned (N.v50074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50074 s i)) at 1.
  unfold R.v50074, N.v50074.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50075 (s : N.State) (i : N.Inputs) :
  R.v50075 (state s) (inputs i) = Zmod.unsigned (N.v50075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50075 s i)) at 1.
  unfold R.v50075, N.v50075.
  rewrite ?node_8151.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50076 (s : N.State) (i : N.Inputs) :
  R.v50076 (state s) (inputs i) = Zmod.unsigned (N.v50076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50076 s i)) at 1.
  unfold R.v50076, N.v50076.
  unfold R.v6, N.v6.
  rewrite ?node_8147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50077 (s : N.State) (i : N.Inputs) :
  R.v50077 (state s) (inputs i) = Zmod.unsigned (N.v50077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50077 s i)) at 1.
  unfold R.v50077, N.v50077.
  unfold R.v6, N.v6.
  rewrite ?node_8144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50078 (s : N.State) (i : N.Inputs) :
  R.v50078 (state s) (inputs i) = Zmod.unsigned (N.v50078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50078 s i)) at 1.
  unfold R.v50078, N.v50078.
  rewrite ?node_50076.
  rewrite ?node_50077.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50079 (s : N.State) (i : N.Inputs) :
  R.v50079 (state s) (inputs i) = Zmod.unsigned (N.v50079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50079 s i)) at 1.
  unfold R.v50079, N.v50079.
  unfold R.v16484, N.v16484.
  rewrite ?node_50078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50080 (s : N.State) (i : N.Inputs) :
  R.v50080 (state s) (inputs i) = Zmod.unsigned (N.v50080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50080 s i)) at 1.
  unfold R.v50080, N.v50080.
  rewrite ?node_50075.
  rewrite ?node_50079.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50081 (s : N.State) (i : N.Inputs) :
  R.v50081 (state s) (inputs i) = Zmod.unsigned (N.v50081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50081 s i)) at 1.
  unfold R.v50081, N.v50081.
  unfold R.v6, N.v6.
  rewrite ?node_50080.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50082 (s : N.State) (i : N.Inputs) :
  R.v50082 (state s) (inputs i) = Zmod.unsigned (N.v50082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50082 s i)) at 1.
  unfold R.v50082, N.v50082.
  rewrite ?node_8152.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50083 (s : N.State) (i : N.Inputs) :
  R.v50083 (state s) (inputs i) = Zmod.unsigned (N.v50083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50083 s i)) at 1.
  unfold R.v50083, N.v50083.
  unfold R.v6, N.v6.
  rewrite ?node_8282.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50084 (s : N.State) (i : N.Inputs) :
  R.v50084 (state s) (inputs i) = Zmod.unsigned (N.v50084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50084 s i)) at 1.
  unfold R.v50084, N.v50084.
  rewrite ?node_50082.
  rewrite ?node_50083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50085 (s : N.State) (i : N.Inputs) :
  R.v50085 (state s) (inputs i) = Zmod.unsigned (N.v50085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50085 s i)) at 1.
  unfold R.v50085, N.v50085.
  rewrite ?node_50081.
  rewrite ?node_50084.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50086 (s : N.State) (i : N.Inputs) :
  R.v50086 (state s) (inputs i) = Zmod.unsigned (N.v50086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50086 s i)) at 1.
  unfold R.v50086, N.v50086.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50087 (s : N.State) (i : N.Inputs) :
  R.v50087 (state s) (inputs i) = Zmod.unsigned (N.v50087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50087 s i)) at 1.
  unfold R.v50087, N.v50087.
  rewrite ?node_8262.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50088 (s : N.State) (i : N.Inputs) :
  R.v50088 (state s) (inputs i) = Zmod.unsigned (N.v50088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50088 s i)) at 1.
  unfold R.v50088, N.v50088.
  rewrite ?node_8258.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50089 (s : N.State) (i : N.Inputs) :
  R.v50089 (state s) (inputs i) = Zmod.unsigned (N.v50089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50089 s i)) at 1.
  unfold R.v50089, N.v50089.
  rewrite ?node_8252.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50090 (s : N.State) (i : N.Inputs) :
  R.v50090 (state s) (inputs i) = Zmod.unsigned (N.v50090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50090 s i)) at 1.
  unfold R.v50090, N.v50090.
  unfold R.v6, N.v6.
  rewrite ?node_8232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50091 (s : N.State) (i : N.Inputs) :
  R.v50091 (state s) (inputs i) = Zmod.unsigned (N.v50091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50091 s i)) at 1.
  unfold R.v50091, N.v50091.
  unfold R.v6, N.v6.
  rewrite ?node_8207.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50092 (s : N.State) (i : N.Inputs) :
  R.v50092 (state s) (inputs i) = Zmod.unsigned (N.v50092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50092 s i)) at 1.
  unfold R.v50092, N.v50092.
  rewrite ?node_50090.
  rewrite ?node_50091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50093 (s : N.State) (i : N.Inputs) :
  R.v50093 (state s) (inputs i) = Zmod.unsigned (N.v50093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50093 s i)) at 1.
  unfold R.v50093, N.v50093.
  unfold R.v16484, N.v16484.
  rewrite ?node_50092.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50094 (s : N.State) (i : N.Inputs) :
  R.v50094 (state s) (inputs i) = Zmod.unsigned (N.v50094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50094 s i)) at 1.
  unfold R.v50094, N.v50094.
  rewrite ?node_50087.
  rewrite ?node_50088.
  rewrite ?node_50089.
  rewrite ?node_50093.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50095 (s : N.State) (i : N.Inputs) :
  R.v50095 (state s) (inputs i) = Zmod.unsigned (N.v50095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50095 s i)) at 1.
  unfold R.v50095, N.v50095.
  unfold R.v6, N.v6.
  rewrite ?node_50094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50096 (s : N.State) (i : N.Inputs) :
  R.v50096 (state s) (inputs i) = Zmod.unsigned (N.v50096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50096 s i)) at 1.
  unfold R.v50096, N.v50096.
  rewrite ?node_8263.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50097 (s : N.State) (i : N.Inputs) :
  R.v50097 (state s) (inputs i) = Zmod.unsigned (N.v50097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50097 s i)) at 1.
  unfold R.v50097, N.v50097.
  unfold R.v6, N.v6.
  rewrite ?node_8385.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50098 (s : N.State) (i : N.Inputs) :
  R.v50098 (state s) (inputs i) = Zmod.unsigned (N.v50098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50098 s i)) at 1.
  unfold R.v50098, N.v50098.
  unfold R.v6, N.v6.
  rewrite ?node_8403.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50099 (s : N.State) (i : N.Inputs) :
  R.v50099 (state s) (inputs i) = Zmod.unsigned (N.v50099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50099 s i)) at 1.
  unfold R.v50099, N.v50099.
  rewrite ?node_50096.
  rewrite ?node_50097.
  rewrite ?node_50098.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50100 (s : N.State) (i : N.Inputs) :
  R.v50100 (state s) (inputs i) = Zmod.unsigned (N.v50100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50100 s i)) at 1.
  unfold R.v50100, N.v50100.
  rewrite ?node_50095.
  rewrite ?node_50099.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50101 (s : N.State) (i : N.Inputs) :
  R.v50101 (state s) (inputs i) = Zmod.unsigned (N.v50101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50101 s i)) at 1.
  unfold R.v50101, N.v50101.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50102 (s : N.State) (i : N.Inputs) :
  R.v50102 (state s) (inputs i) = Zmod.unsigned (N.v50102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50102 s i)) at 1.
  unfold R.v50102, N.v50102.
  rewrite ?node_8252.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50103 (s : N.State) (i : N.Inputs) :
  R.v50103 (state s) (inputs i) = Zmod.unsigned (N.v50103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50103 s i)) at 1.
  unfold R.v50103, N.v50103.
  unfold R.v6, N.v6.
  rewrite ?node_8232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50104 (s : N.State) (i : N.Inputs) :
  R.v50104 (state s) (inputs i) = Zmod.unsigned (N.v50104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50104 s i)) at 1.
  unfold R.v50104, N.v50104.
  unfold R.v6, N.v6.
  rewrite ?node_8207.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50105 (s : N.State) (i : N.Inputs) :
  R.v50105 (state s) (inputs i) = Zmod.unsigned (N.v50105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50105 s i)) at 1.
  unfold R.v50105, N.v50105.
  rewrite ?node_50103.
  rewrite ?node_50104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50106 (s : N.State) (i : N.Inputs) :
  R.v50106 (state s) (inputs i) = Zmod.unsigned (N.v50106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50106 s i)) at 1.
  unfold R.v50106, N.v50106.
  unfold R.v16484, N.v16484.
  rewrite ?node_50105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50107 (s : N.State) (i : N.Inputs) :
  R.v50107 (state s) (inputs i) = Zmod.unsigned (N.v50107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50107 s i)) at 1.
  unfold R.v50107, N.v50107.
  rewrite ?node_50102.
  rewrite ?node_50106.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50108 (s : N.State) (i : N.Inputs) :
  R.v50108 (state s) (inputs i) = Zmod.unsigned (N.v50108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50108 s i)) at 1.
  unfold R.v50108, N.v50108.
  unfold R.v6, N.v6.
  rewrite ?node_50107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50109 (s : N.State) (i : N.Inputs) :
  R.v50109 (state s) (inputs i) = Zmod.unsigned (N.v50109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50109 s i)) at 1.
  unfold R.v50109, N.v50109.
  rewrite ?node_8253.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50110 (s : N.State) (i : N.Inputs) :
  R.v50110 (state s) (inputs i) = Zmod.unsigned (N.v50110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50110 s i)) at 1.
  unfold R.v50110, N.v50110.
  unfold R.v6, N.v6.
  rewrite ?node_8385.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50111 (s : N.State) (i : N.Inputs) :
  R.v50111 (state s) (inputs i) = Zmod.unsigned (N.v50111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50111 s i)) at 1.
  unfold R.v50111, N.v50111.
  rewrite ?node_50109.
  rewrite ?node_50110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50112 (s : N.State) (i : N.Inputs) :
  R.v50112 (state s) (inputs i) = Zmod.unsigned (N.v50112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50112 s i)) at 1.
  unfold R.v50112, N.v50112.
  rewrite ?node_50108.
  rewrite ?node_50111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50113 (s : N.State) (i : N.Inputs) :
  R.v50113 (state s) (inputs i) = Zmod.unsigned (N.v50113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50113 s i)) at 1.
  unfold R.v50113, N.v50113.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50114 (s : N.State) (i : N.Inputs) :
  R.v50114 (state s) (inputs i) = Zmod.unsigned (N.v50114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50114 s i)) at 1.
  unfold R.v50114, N.v50114.
  rewrite ?node_8262.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50115 (s : N.State) (i : N.Inputs) :
  R.v50115 (state s) (inputs i) = Zmod.unsigned (N.v50115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50115 s i)) at 1.
  unfold R.v50115, N.v50115.
  unfold R.v6, N.v6.
  rewrite ?node_8258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50116 (s : N.State) (i : N.Inputs) :
  R.v50116 (state s) (inputs i) = Zmod.unsigned (N.v50116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50116 s i)) at 1.
  unfold R.v50116, N.v50116.
  unfold R.v6, N.v6.
  rewrite ?node_8253.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50117 (s : N.State) (i : N.Inputs) :
  R.v50117 (state s) (inputs i) = Zmod.unsigned (N.v50117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50117 s i)) at 1.
  unfold R.v50117, N.v50117.
  rewrite ?node_50115.
  rewrite ?node_50116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50118 (s : N.State) (i : N.Inputs) :
  R.v50118 (state s) (inputs i) = Zmod.unsigned (N.v50118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50118 s i)) at 1.
  unfold R.v50118, N.v50118.
  unfold R.v16484, N.v16484.
  rewrite ?node_50117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50119 (s : N.State) (i : N.Inputs) :
  R.v50119 (state s) (inputs i) = Zmod.unsigned (N.v50119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50119 s i)) at 1.
  unfold R.v50119, N.v50119.
  rewrite ?node_50114.
  rewrite ?node_50118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50120 (s : N.State) (i : N.Inputs) :
  R.v50120 (state s) (inputs i) = Zmod.unsigned (N.v50120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50120 s i)) at 1.
  unfold R.v50120, N.v50120.
  unfold R.v6, N.v6.
  rewrite ?node_50119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50121 (s : N.State) (i : N.Inputs) :
  R.v50121 (state s) (inputs i) = Zmod.unsigned (N.v50121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50121 s i)) at 1.
  unfold R.v50121, N.v50121.
  rewrite ?node_8263.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50122 (s : N.State) (i : N.Inputs) :
  R.v50122 (state s) (inputs i) = Zmod.unsigned (N.v50122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50122 s i)) at 1.
  unfold R.v50122, N.v50122.
  unfold R.v6, N.v6.
  rewrite ?node_8403.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50123 (s : N.State) (i : N.Inputs) :
  R.v50123 (state s) (inputs i) = Zmod.unsigned (N.v50123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50123 s i)) at 1.
  unfold R.v50123, N.v50123.
  rewrite ?node_50121.
  rewrite ?node_50122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50124 (s : N.State) (i : N.Inputs) :
  R.v50124 (state s) (inputs i) = Zmod.unsigned (N.v50124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50124 s i)) at 1.
  unfold R.v50124, N.v50124.
  rewrite ?node_50120.
  rewrite ?node_50123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50125 (s : N.State) (i : N.Inputs) :
  R.v50125 (state s) (inputs i) = Zmod.unsigned (N.v50125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50125 s i)) at 1.
  unfold R.v50125, N.v50125.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50126 (s : N.State) (i : N.Inputs) :
  R.v50126 (state s) (inputs i) = Zmod.unsigned (N.v50126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50126 s i)) at 1.
  unfold R.v50126, N.v50126.
  rewrite ?node_8273.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50127 (s : N.State) (i : N.Inputs) :
  R.v50127 (state s) (inputs i) = Zmod.unsigned (N.v50127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50127 s i)) at 1.
  unfold R.v50127, N.v50127.
  unfold R.v6, N.v6.
  rewrite ?node_8269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50128 (s : N.State) (i : N.Inputs) :
  R.v50128 (state s) (inputs i) = Zmod.unsigned (N.v50128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50128 s i)) at 1.
  unfold R.v50128, N.v50128.
  unfold R.v6, N.v6.
  rewrite ?node_8266.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50129 (s : N.State) (i : N.Inputs) :
  R.v50129 (state s) (inputs i) = Zmod.unsigned (N.v50129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50129 s i)) at 1.
  unfold R.v50129, N.v50129.
  rewrite ?node_50127.
  rewrite ?node_50128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50130 (s : N.State) (i : N.Inputs) :
  R.v50130 (state s) (inputs i) = Zmod.unsigned (N.v50130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50130 s i)) at 1.
  unfold R.v50130, N.v50130.
  unfold R.v16484, N.v16484.
  rewrite ?node_50129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50131 (s : N.State) (i : N.Inputs) :
  R.v50131 (state s) (inputs i) = Zmod.unsigned (N.v50131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50131 s i)) at 1.
  unfold R.v50131, N.v50131.
  rewrite ?node_50126.
  rewrite ?node_50130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50132 (s : N.State) (i : N.Inputs) :
  R.v50132 (state s) (inputs i) = Zmod.unsigned (N.v50132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50132 s i)) at 1.
  unfold R.v50132, N.v50132.
  unfold R.v6, N.v6.
  rewrite ?node_50131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50133 (s : N.State) (i : N.Inputs) :
  R.v50133 (state s) (inputs i) = Zmod.unsigned (N.v50133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50133 s i)) at 1.
  unfold R.v50133, N.v50133.
  rewrite ?node_8274.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50134 (s : N.State) (i : N.Inputs) :
  R.v50134 (state s) (inputs i) = Zmod.unsigned (N.v50134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50134 s i)) at 1.
  unfold R.v50134, N.v50134.
  unfold R.v6, N.v6.
  rewrite ?node_8407.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50135 (s : N.State) (i : N.Inputs) :
  R.v50135 (state s) (inputs i) = Zmod.unsigned (N.v50135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50135 s i)) at 1.
  unfold R.v50135, N.v50135.
  rewrite ?node_50133.
  rewrite ?node_50134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50136 (s : N.State) (i : N.Inputs) :
  R.v50136 (state s) (inputs i) = Zmod.unsigned (N.v50136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50136 s i)) at 1.
  unfold R.v50136, N.v50136.
  rewrite ?node_50132.
  rewrite ?node_50135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50137 (s : N.State) (i : N.Inputs) :
  R.v50137 (state s) (inputs i) = Zmod.unsigned (N.v50137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50137 s i)) at 1.
  unfold R.v50137, N.v50137.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50138 (s : N.State) (i : N.Inputs) :
  R.v50138 (state s) (inputs i) = Zmod.unsigned (N.v50138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50138 s i)) at 1.
  unfold R.v50138, N.v50138.
  rewrite ?node_8385.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50139 (s : N.State) (i : N.Inputs) :
  R.v50139 (state s) (inputs i) = Zmod.unsigned (N.v50139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50139 s i)) at 1.
  unfold R.v50139, N.v50139.
  rewrite ?node_8381.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50140 (s : N.State) (i : N.Inputs) :
  R.v50140 (state s) (inputs i) = Zmod.unsigned (N.v50140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50140 s i)) at 1.
  unfold R.v50140, N.v50140.
  rewrite ?node_8375.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50141 (s : N.State) (i : N.Inputs) :
  R.v50141 (state s) (inputs i) = Zmod.unsigned (N.v50141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50141 s i)) at 1.
  unfold R.v50141, N.v50141.
  unfold R.v6, N.v6.
  rewrite ?node_8355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50142 (s : N.State) (i : N.Inputs) :
  R.v50142 (state s) (inputs i) = Zmod.unsigned (N.v50142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50142 s i)) at 1.
  unfold R.v50142, N.v50142.
  unfold R.v6, N.v6.
  rewrite ?node_8329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50143 (s : N.State) (i : N.Inputs) :
  R.v50143 (state s) (inputs i) = Zmod.unsigned (N.v50143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50143 s i)) at 1.
  unfold R.v50143, N.v50143.
  rewrite ?node_50141.
  rewrite ?node_50142.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50144 (s : N.State) (i : N.Inputs) :
  R.v50144 (state s) (inputs i) = Zmod.unsigned (N.v50144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50144 s i)) at 1.
  unfold R.v50144, N.v50144.
  unfold R.v16484, N.v16484.
  rewrite ?node_50143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50145 (s : N.State) (i : N.Inputs) :
  R.v50145 (state s) (inputs i) = Zmod.unsigned (N.v50145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50145 s i)) at 1.
  unfold R.v50145, N.v50145.
  rewrite ?node_50138.
  rewrite ?node_50139.
  rewrite ?node_50140.
  rewrite ?node_50144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50146 (s : N.State) (i : N.Inputs) :
  R.v50146 (state s) (inputs i) = Zmod.unsigned (N.v50146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50146 s i)) at 1.
  unfold R.v50146, N.v50146.
  unfold R.v6, N.v6.
  rewrite ?node_50145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50147 (s : N.State) (i : N.Inputs) :
  R.v50147 (state s) (inputs i) = Zmod.unsigned (N.v50147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50147 s i)) at 1.
  unfold R.v50147, N.v50147.
  rewrite ?node_8386.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50148 (s : N.State) (i : N.Inputs) :
  R.v50148 (state s) (inputs i) = Zmod.unsigned (N.v50148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50148 s i)) at 1.
  unfold R.v50148, N.v50148.
  unfold R.v6, N.v6.
  rewrite ?node_8512.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50149 (s : N.State) (i : N.Inputs) :
  R.v50149 (state s) (inputs i) = Zmod.unsigned (N.v50149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50149 s i)) at 1.
  unfold R.v50149, N.v50149.
  unfold R.v6, N.v6.
  rewrite ?node_8534.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50150 (s : N.State) (i : N.Inputs) :
  R.v50150 (state s) (inputs i) = Zmod.unsigned (N.v50150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50150 s i)) at 1.
  unfold R.v50150, N.v50150.
  rewrite ?node_50147.
  rewrite ?node_50148.
  rewrite ?node_50149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50151 (s : N.State) (i : N.Inputs) :
  R.v50151 (state s) (inputs i) = Zmod.unsigned (N.v50151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50151 s i)) at 1.
  unfold R.v50151, N.v50151.
  rewrite ?node_50146.
  rewrite ?node_50150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50152 (s : N.State) (i : N.Inputs) :
  R.v50152 (state s) (inputs i) = Zmod.unsigned (N.v50152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50152 s i)) at 1.
  unfold R.v50152, N.v50152.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50153 (s : N.State) (i : N.Inputs) :
  R.v50153 (state s) (inputs i) = Zmod.unsigned (N.v50153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50153 s i)) at 1.
  unfold R.v50153, N.v50153.
  rewrite ?node_8375.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50154 (s : N.State) (i : N.Inputs) :
  R.v50154 (state s) (inputs i) = Zmod.unsigned (N.v50154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50154 s i)) at 1.
  unfold R.v50154, N.v50154.
  unfold R.v6, N.v6.
  rewrite ?node_8355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50155 (s : N.State) (i : N.Inputs) :
  R.v50155 (state s) (inputs i) = Zmod.unsigned (N.v50155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50155 s i)) at 1.
  unfold R.v50155, N.v50155.
  unfold R.v6, N.v6.
  rewrite ?node_8329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50156 (s : N.State) (i : N.Inputs) :
  R.v50156 (state s) (inputs i) = Zmod.unsigned (N.v50156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50156 s i)) at 1.
  unfold R.v50156, N.v50156.
  rewrite ?node_50154.
  rewrite ?node_50155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50157 (s : N.State) (i : N.Inputs) :
  R.v50157 (state s) (inputs i) = Zmod.unsigned (N.v50157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50157 s i)) at 1.
  unfold R.v50157, N.v50157.
  unfold R.v16484, N.v16484.
  rewrite ?node_50156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50158 (s : N.State) (i : N.Inputs) :
  R.v50158 (state s) (inputs i) = Zmod.unsigned (N.v50158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50158 s i)) at 1.
  unfold R.v50158, N.v50158.
  rewrite ?node_50153.
  rewrite ?node_50157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50159 (s : N.State) (i : N.Inputs) :
  R.v50159 (state s) (inputs i) = Zmod.unsigned (N.v50159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50159 s i)) at 1.
  unfold R.v50159, N.v50159.
  unfold R.v6, N.v6.
  rewrite ?node_50158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50160 (s : N.State) (i : N.Inputs) :
  R.v50160 (state s) (inputs i) = Zmod.unsigned (N.v50160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50160 s i)) at 1.
  unfold R.v50160, N.v50160.
  rewrite ?node_8376.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50161 (s : N.State) (i : N.Inputs) :
  R.v50161 (state s) (inputs i) = Zmod.unsigned (N.v50161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50161 s i)) at 1.
  unfold R.v50161, N.v50161.
  unfold R.v6, N.v6.
  rewrite ?node_8512.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50162 (s : N.State) (i : N.Inputs) :
  R.v50162 (state s) (inputs i) = Zmod.unsigned (N.v50162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50162 s i)) at 1.
  unfold R.v50162, N.v50162.
  rewrite ?node_50160.
  rewrite ?node_50161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50163 (s : N.State) (i : N.Inputs) :
  R.v50163 (state s) (inputs i) = Zmod.unsigned (N.v50163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50163 s i)) at 1.
  unfold R.v50163, N.v50163.
  rewrite ?node_50159.
  rewrite ?node_50162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50164 (s : N.State) (i : N.Inputs) :
  R.v50164 (state s) (inputs i) = Zmod.unsigned (N.v50164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50164 s i)) at 1.
  unfold R.v50164, N.v50164.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50165 (s : N.State) (i : N.Inputs) :
  R.v50165 (state s) (inputs i) = Zmod.unsigned (N.v50165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50165 s i)) at 1.
  unfold R.v50165, N.v50165.
  rewrite ?node_8385.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50166 (s : N.State) (i : N.Inputs) :
  R.v50166 (state s) (inputs i) = Zmod.unsigned (N.v50166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50166 s i)) at 1.
  unfold R.v50166, N.v50166.
  unfold R.v6, N.v6.
  rewrite ?node_8381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50167 (s : N.State) (i : N.Inputs) :
  R.v50167 (state s) (inputs i) = Zmod.unsigned (N.v50167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50167 s i)) at 1.
  unfold R.v50167, N.v50167.
  unfold R.v6, N.v6.
  rewrite ?node_8376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50168 (s : N.State) (i : N.Inputs) :
  R.v50168 (state s) (inputs i) = Zmod.unsigned (N.v50168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50168 s i)) at 1.
  unfold R.v50168, N.v50168.
  rewrite ?node_50166.
  rewrite ?node_50167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50169 (s : N.State) (i : N.Inputs) :
  R.v50169 (state s) (inputs i) = Zmod.unsigned (N.v50169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50169 s i)) at 1.
  unfold R.v50169, N.v50169.
  unfold R.v16484, N.v16484.
  rewrite ?node_50168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50170 (s : N.State) (i : N.Inputs) :
  R.v50170 (state s) (inputs i) = Zmod.unsigned (N.v50170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50170 s i)) at 1.
  unfold R.v50170, N.v50170.
  rewrite ?node_50165.
  rewrite ?node_50169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50171 (s : N.State) (i : N.Inputs) :
  R.v50171 (state s) (inputs i) = Zmod.unsigned (N.v50171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50171 s i)) at 1.
  unfold R.v50171, N.v50171.
  unfold R.v6, N.v6.
  rewrite ?node_50170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50172 (s : N.State) (i : N.Inputs) :
  R.v50172 (state s) (inputs i) = Zmod.unsigned (N.v50172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50172 s i)) at 1.
  unfold R.v50172, N.v50172.
  rewrite ?node_8386.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50173 (s : N.State) (i : N.Inputs) :
  R.v50173 (state s) (inputs i) = Zmod.unsigned (N.v50173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50173 s i)) at 1.
  unfold R.v50173, N.v50173.
  unfold R.v6, N.v6.
  rewrite ?node_8534.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50174 (s : N.State) (i : N.Inputs) :
  R.v50174 (state s) (inputs i) = Zmod.unsigned (N.v50174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50174 s i)) at 1.
  unfold R.v50174, N.v50174.
  rewrite ?node_50172.
  rewrite ?node_50173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50175 (s : N.State) (i : N.Inputs) :
  R.v50175 (state s) (inputs i) = Zmod.unsigned (N.v50175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50175 s i)) at 1.
  unfold R.v50175, N.v50175.
  rewrite ?node_50171.
  rewrite ?node_50174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50176 (s : N.State) (i : N.Inputs) :
  R.v50176 (state s) (inputs i) = Zmod.unsigned (N.v50176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50176 s i)) at 1.
  unfold R.v50176, N.v50176.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50177 (s : N.State) (i : N.Inputs) :
  R.v50177 (state s) (inputs i) = Zmod.unsigned (N.v50177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50177 s i)) at 1.
  unfold R.v50177, N.v50177.
  rewrite ?node_8398.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50178 (s : N.State) (i : N.Inputs) :
  R.v50178 (state s) (inputs i) = Zmod.unsigned (N.v50178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50178 s i)) at 1.
  unfold R.v50178, N.v50178.
  rewrite ?node_8396.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50179 (s : N.State) (i : N.Inputs) :
  R.v50179 (state s) (inputs i) = Zmod.unsigned (N.v50179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50179 s i)) at 1.
  unfold R.v50179, N.v50179.
  unfold R.v6, N.v6.
  rewrite ?node_8392.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50180 (s : N.State) (i : N.Inputs) :
  R.v50180 (state s) (inputs i) = Zmod.unsigned (N.v50180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50180 s i)) at 1.
  unfold R.v50180, N.v50180.
  unfold R.v6, N.v6.
  rewrite ?node_8389.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50181 (s : N.State) (i : N.Inputs) :
  R.v50181 (state s) (inputs i) = Zmod.unsigned (N.v50181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50181 s i)) at 1.
  unfold R.v50181, N.v50181.
  rewrite ?node_50179.
  rewrite ?node_50180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50182 (s : N.State) (i : N.Inputs) :
  R.v50182 (state s) (inputs i) = Zmod.unsigned (N.v50182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50182 s i)) at 1.
  unfold R.v50182, N.v50182.
  unfold R.v16484, N.v16484.
  rewrite ?node_50181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50183 (s : N.State) (i : N.Inputs) :
  R.v50183 (state s) (inputs i) = Zmod.unsigned (N.v50183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50183 s i)) at 1.
  unfold R.v50183, N.v50183.
  rewrite ?node_50177.
  rewrite ?node_50178.
  rewrite ?node_50182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50184 (s : N.State) (i : N.Inputs) :
  R.v50184 (state s) (inputs i) = Zmod.unsigned (N.v50184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50184 s i)) at 1.
  unfold R.v50184, N.v50184.
  unfold R.v6, N.v6.
  rewrite ?node_50183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50185 (s : N.State) (i : N.Inputs) :
  R.v50185 (state s) (inputs i) = Zmod.unsigned (N.v50185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50185 s i)) at 1.
  unfold R.v50185, N.v50185.
  rewrite ?node_8399.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50186 (s : N.State) (i : N.Inputs) :
  R.v50186 (state s) (inputs i) = Zmod.unsigned (N.v50186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50186 s i)) at 1.
  unfold R.v50186, N.v50186.
  unfold R.v6, N.v6.
  rewrite ?node_8529.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50187 (s : N.State) (i : N.Inputs) :
  R.v50187 (state s) (inputs i) = Zmod.unsigned (N.v50187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50187 s i)) at 1.
  unfold R.v50187, N.v50187.
  unfold R.v6, N.v6.
  rewrite ?node_8536.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50188 (s : N.State) (i : N.Inputs) :
  R.v50188 (state s) (inputs i) = Zmod.unsigned (N.v50188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50188 s i)) at 1.
  unfold R.v50188, N.v50188.
  rewrite ?node_50185.
  rewrite ?node_50186.
  rewrite ?node_50187.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50189 (s : N.State) (i : N.Inputs) :
  R.v50189 (state s) (inputs i) = Zmod.unsigned (N.v50189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50189 s i)) at 1.
  unfold R.v50189, N.v50189.
  rewrite ?node_50184.
  rewrite ?node_50188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50190 (s : N.State) (i : N.Inputs) :
  R.v50190 (state s) (inputs i) = Zmod.unsigned (N.v50190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50190 s i)) at 1.
  unfold R.v50190, N.v50190.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50191 (s : N.State) (i : N.Inputs) :
  R.v50191 (state s) (inputs i) = Zmod.unsigned (N.v50191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50191 s i)) at 1.
  unfold R.v50191, N.v50191.
  rewrite ?node_8396.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50192 (s : N.State) (i : N.Inputs) :
  R.v50192 (state s) (inputs i) = Zmod.unsigned (N.v50192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50192 s i)) at 1.
  unfold R.v50192, N.v50192.
  unfold R.v6, N.v6.
  rewrite ?node_8392.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50193 (s : N.State) (i : N.Inputs) :
  R.v50193 (state s) (inputs i) = Zmod.unsigned (N.v50193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50193 s i)) at 1.
  unfold R.v50193, N.v50193.
  unfold R.v6, N.v6.
  rewrite ?node_8389.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50194 (s : N.State) (i : N.Inputs) :
  R.v50194 (state s) (inputs i) = Zmod.unsigned (N.v50194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50194 s i)) at 1.
  unfold R.v50194, N.v50194.
  rewrite ?node_50192.
  rewrite ?node_50193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50195 (s : N.State) (i : N.Inputs) :
  R.v50195 (state s) (inputs i) = Zmod.unsigned (N.v50195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50195 s i)) at 1.
  unfold R.v50195, N.v50195.
  unfold R.v16484, N.v16484.
  rewrite ?node_50194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50196 (s : N.State) (i : N.Inputs) :
  R.v50196 (state s) (inputs i) = Zmod.unsigned (N.v50196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50196 s i)) at 1.
  unfold R.v50196, N.v50196.
  rewrite ?node_50191.
  rewrite ?node_50195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50197 (s : N.State) (i : N.Inputs) :
  R.v50197 (state s) (inputs i) = Zmod.unsigned (N.v50197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50197 s i)) at 1.
  unfold R.v50197, N.v50197.
  unfold R.v6, N.v6.
  rewrite ?node_50196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50198 (s : N.State) (i : N.Inputs) :
  R.v50198 (state s) (inputs i) = Zmod.unsigned (N.v50198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50198 s i)) at 1.
  unfold R.v50198, N.v50198.
  rewrite ?node_8397.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50199 (s : N.State) (i : N.Inputs) :
  R.v50199 (state s) (inputs i) = Zmod.unsigned (N.v50199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50199 s i)) at 1.
  unfold R.v50199, N.v50199.
  unfold R.v6, N.v6.
  rewrite ?node_8529.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50200 (s : N.State) (i : N.Inputs) :
  R.v50200 (state s) (inputs i) = Zmod.unsigned (N.v50200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50200 s i)) at 1.
  unfold R.v50200, N.v50200.
  rewrite ?node_50198.
  rewrite ?node_50199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50201 (s : N.State) (i : N.Inputs) :
  R.v50201 (state s) (inputs i) = Zmod.unsigned (N.v50201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50201 s i)) at 1.
  unfold R.v50201, N.v50201.
  rewrite ?node_50197.
  rewrite ?node_50200.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50202 (s : N.State) (i : N.Inputs) :
  R.v50202 (state s) (inputs i) = Zmod.unsigned (N.v50202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50202 s i)) at 1.
  unfold R.v50202, N.v50202.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50203 (s : N.State) (i : N.Inputs) :
  R.v50203 (state s) (inputs i) = Zmod.unsigned (N.v50203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50203 s i)) at 1.
  unfold R.v50203, N.v50203.
  unfold R.v6, N.v6.
  rewrite ?node_8398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50204 (s : N.State) (i : N.Inputs) :
  R.v50204 (state s) (inputs i) = Zmod.unsigned (N.v50204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50204 s i)) at 1.
  unfold R.v50204, N.v50204.
  unfold R.v6, N.v6.
  rewrite ?node_8397.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50205 (s : N.State) (i : N.Inputs) :
  R.v50205 (state s) (inputs i) = Zmod.unsigned (N.v50205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50205 s i)) at 1.
  unfold R.v50205, N.v50205.
  rewrite ?node_50203.
  rewrite ?node_50204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50206 (s : N.State) (i : N.Inputs) :
  R.v50206 (state s) (inputs i) = Zmod.unsigned (N.v50206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50206 s i)) at 1.
  unfold R.v50206, N.v50206.
  unfold R.v16463, N.v16463.
  rewrite ?node_50205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50207 (s : N.State) (i : N.Inputs) :
  R.v50207 (state s) (inputs i) = Zmod.unsigned (N.v50207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50207 s i)) at 1.
  unfold R.v50207, N.v50207.
  rewrite ?node_8399.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50208 (s : N.State) (i : N.Inputs) :
  R.v50208 (state s) (inputs i) = Zmod.unsigned (N.v50208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50208 s i)) at 1.
  unfold R.v50208, N.v50208.
  unfold R.v6, N.v6.
  rewrite ?node_8536.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50209 (s : N.State) (i : N.Inputs) :
  R.v50209 (state s) (inputs i) = Zmod.unsigned (N.v50209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50209 s i)) at 1.
  unfold R.v50209, N.v50209.
  rewrite ?node_50207.
  rewrite ?node_50208.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50210 (s : N.State) (i : N.Inputs) :
  R.v50210 (state s) (inputs i) = Zmod.unsigned (N.v50210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50210 s i)) at 1.
  unfold R.v50210, N.v50210.
  rewrite ?node_50206.
  rewrite ?node_50209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50211 (s : N.State) (i : N.Inputs) :
  R.v50211 (state s) (inputs i) = Zmod.unsigned (N.v50211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50211 s i)) at 1.
  unfold R.v50211, N.v50211.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50212 (s : N.State) (i : N.Inputs) :
  R.v50212 (state s) (inputs i) = Zmod.unsigned (N.v50212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50212 s i)) at 1.
  unfold R.v50212, N.v50212.
  rewrite ?node_8512.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50213 (s : N.State) (i : N.Inputs) :
  R.v50213 (state s) (inputs i) = Zmod.unsigned (N.v50213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50213 s i)) at 1.
  unfold R.v50213, N.v50213.
  rewrite ?node_8508.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50214 (s : N.State) (i : N.Inputs) :
  R.v50214 (state s) (inputs i) = Zmod.unsigned (N.v50214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50214 s i)) at 1.
  unfold R.v50214, N.v50214.
  rewrite ?node_8500.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50215 (s : N.State) (i : N.Inputs) :
  R.v50215 (state s) (inputs i) = Zmod.unsigned (N.v50215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50215 s i)) at 1.
  unfold R.v50215, N.v50215.
  unfold R.v6, N.v6.
  rewrite ?node_8480.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50216 (s : N.State) (i : N.Inputs) :
  R.v50216 (state s) (inputs i) = Zmod.unsigned (N.v50216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50216 s i)) at 1.
  unfold R.v50216, N.v50216.
  unfold R.v6, N.v6.
  rewrite ?node_8454.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50217 (s : N.State) (i : N.Inputs) :
  R.v50217 (state s) (inputs i) = Zmod.unsigned (N.v50217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50217 s i)) at 1.
  unfold R.v50217, N.v50217.
  rewrite ?node_50215.
  rewrite ?node_50216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50218 (s : N.State) (i : N.Inputs) :
  R.v50218 (state s) (inputs i) = Zmod.unsigned (N.v50218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50218 s i)) at 1.
  unfold R.v50218, N.v50218.
  unfold R.v16484, N.v16484.
  rewrite ?node_50217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50219 (s : N.State) (i : N.Inputs) :
  R.v50219 (state s) (inputs i) = Zmod.unsigned (N.v50219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50219 s i)) at 1.
  unfold R.v50219, N.v50219.
  rewrite ?node_50212.
  rewrite ?node_50213.
  rewrite ?node_50214.
  rewrite ?node_50218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50220 (s : N.State) (i : N.Inputs) :
  R.v50220 (state s) (inputs i) = Zmod.unsigned (N.v50220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50220 s i)) at 1.
  unfold R.v50220, N.v50220.
  unfold R.v6, N.v6.
  rewrite ?node_50219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50221 (s : N.State) (i : N.Inputs) :
  R.v50221 (state s) (inputs i) = Zmod.unsigned (N.v50221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50221 s i)) at 1.
  unfold R.v50221, N.v50221.
  rewrite ?node_8513.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50222 (s : N.State) (i : N.Inputs) :
  R.v50222 (state s) (inputs i) = Zmod.unsigned (N.v50222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50222 s i)) at 1.
  unfold R.v50222, N.v50222.
  unfold R.v6, N.v6.
  rewrite ?node_8642.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50223 (s : N.State) (i : N.Inputs) :
  R.v50223 (state s) (inputs i) = Zmod.unsigned (N.v50223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50223 s i)) at 1.
  unfold R.v50223, N.v50223.
  unfold R.v6, N.v6.
  rewrite ?node_8664.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50224 (s : N.State) (i : N.Inputs) :
  R.v50224 (state s) (inputs i) = Zmod.unsigned (N.v50224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50224 s i)) at 1.
  unfold R.v50224, N.v50224.
  rewrite ?node_50221.
  rewrite ?node_50222.
  rewrite ?node_50223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50225 (s : N.State) (i : N.Inputs) :
  R.v50225 (state s) (inputs i) = Zmod.unsigned (N.v50225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50225 s i)) at 1.
  unfold R.v50225, N.v50225.
  rewrite ?node_50220.
  rewrite ?node_50224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50226 (s : N.State) (i : N.Inputs) :
  R.v50226 (state s) (inputs i) = Zmod.unsigned (N.v50226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50226 s i)) at 1.
  unfold R.v50226, N.v50226.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50227 (s : N.State) (i : N.Inputs) :
  R.v50227 (state s) (inputs i) = Zmod.unsigned (N.v50227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50227 s i)) at 1.
  unfold R.v50227, N.v50227.
  rewrite ?node_8500.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50228 (s : N.State) (i : N.Inputs) :
  R.v50228 (state s) (inputs i) = Zmod.unsigned (N.v50228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50228 s i)) at 1.
  unfold R.v50228, N.v50228.
  unfold R.v6, N.v6.
  rewrite ?node_8480.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50229 (s : N.State) (i : N.Inputs) :
  R.v50229 (state s) (inputs i) = Zmod.unsigned (N.v50229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50229 s i)) at 1.
  unfold R.v50229, N.v50229.
  unfold R.v6, N.v6.
  rewrite ?node_8454.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50230 (s : N.State) (i : N.Inputs) :
  R.v50230 (state s) (inputs i) = Zmod.unsigned (N.v50230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50230 s i)) at 1.
  unfold R.v50230, N.v50230.
  rewrite ?node_50228.
  rewrite ?node_50229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50231 (s : N.State) (i : N.Inputs) :
  R.v50231 (state s) (inputs i) = Zmod.unsigned (N.v50231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50231 s i)) at 1.
  unfold R.v50231, N.v50231.
  unfold R.v16484, N.v16484.
  rewrite ?node_50230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50232 (s : N.State) (i : N.Inputs) :
  R.v50232 (state s) (inputs i) = Zmod.unsigned (N.v50232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50232 s i)) at 1.
  unfold R.v50232, N.v50232.
  rewrite ?node_50227.
  rewrite ?node_50231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50233 (s : N.State) (i : N.Inputs) :
  R.v50233 (state s) (inputs i) = Zmod.unsigned (N.v50233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50233 s i)) at 1.
  unfold R.v50233, N.v50233.
  unfold R.v6, N.v6.
  rewrite ?node_50232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50234 (s : N.State) (i : N.Inputs) :
  R.v50234 (state s) (inputs i) = Zmod.unsigned (N.v50234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50234 s i)) at 1.
  unfold R.v50234, N.v50234.
  rewrite ?node_8501.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50235 (s : N.State) (i : N.Inputs) :
  R.v50235 (state s) (inputs i) = Zmod.unsigned (N.v50235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50235 s i)) at 1.
  unfold R.v50235, N.v50235.
  unfold R.v6, N.v6.
  rewrite ?node_8642.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50236 (s : N.State) (i : N.Inputs) :
  R.v50236 (state s) (inputs i) = Zmod.unsigned (N.v50236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50236 s i)) at 1.
  unfold R.v50236, N.v50236.
  rewrite ?node_50234.
  rewrite ?node_50235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50237 (s : N.State) (i : N.Inputs) :
  R.v50237 (state s) (inputs i) = Zmod.unsigned (N.v50237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50237 s i)) at 1.
  unfold R.v50237, N.v50237.
  rewrite ?node_50233.
  rewrite ?node_50236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50238 (s : N.State) (i : N.Inputs) :
  R.v50238 (state s) (inputs i) = Zmod.unsigned (N.v50238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50238 s i)) at 1.
  unfold R.v50238, N.v50238.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50239 (s : N.State) (i : N.Inputs) :
  R.v50239 (state s) (inputs i) = Zmod.unsigned (N.v50239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50239 s i)) at 1.
  unfold R.v50239, N.v50239.
  rewrite ?node_8512.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50240 (s : N.State) (i : N.Inputs) :
  R.v50240 (state s) (inputs i) = Zmod.unsigned (N.v50240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50240 s i)) at 1.
  unfold R.v50240, N.v50240.
  unfold R.v6, N.v6.
  rewrite ?node_8508.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50241 (s : N.State) (i : N.Inputs) :
  R.v50241 (state s) (inputs i) = Zmod.unsigned (N.v50241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50241 s i)) at 1.
  unfold R.v50241, N.v50241.
  unfold R.v6, N.v6.
  rewrite ?node_8501.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50242 (s : N.State) (i : N.Inputs) :
  R.v50242 (state s) (inputs i) = Zmod.unsigned (N.v50242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50242 s i)) at 1.
  unfold R.v50242, N.v50242.
  rewrite ?node_50240.
  rewrite ?node_50241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50243 (s : N.State) (i : N.Inputs) :
  R.v50243 (state s) (inputs i) = Zmod.unsigned (N.v50243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50243 s i)) at 1.
  unfold R.v50243, N.v50243.
  unfold R.v16484, N.v16484.
  rewrite ?node_50242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50244 (s : N.State) (i : N.Inputs) :
  R.v50244 (state s) (inputs i) = Zmod.unsigned (N.v50244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50244 s i)) at 1.
  unfold R.v50244, N.v50244.
  rewrite ?node_50239.
  rewrite ?node_50243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50245 (s : N.State) (i : N.Inputs) :
  R.v50245 (state s) (inputs i) = Zmod.unsigned (N.v50245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50245 s i)) at 1.
  unfold R.v50245, N.v50245.
  unfold R.v6, N.v6.
  rewrite ?node_50244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50246 (s : N.State) (i : N.Inputs) :
  R.v50246 (state s) (inputs i) = Zmod.unsigned (N.v50246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50246 s i)) at 1.
  unfold R.v50246, N.v50246.
  rewrite ?node_8513.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50247 (s : N.State) (i : N.Inputs) :
  R.v50247 (state s) (inputs i) = Zmod.unsigned (N.v50247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50247 s i)) at 1.
  unfold R.v50247, N.v50247.
  unfold R.v6, N.v6.
  rewrite ?node_8664.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50248 (s : N.State) (i : N.Inputs) :
  R.v50248 (state s) (inputs i) = Zmod.unsigned (N.v50248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50248 s i)) at 1.
  unfold R.v50248, N.v50248.
  rewrite ?node_50246.
  rewrite ?node_50247.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50249 (s : N.State) (i : N.Inputs) :
  R.v50249 (state s) (inputs i) = Zmod.unsigned (N.v50249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50249 s i)) at 1.
  unfold R.v50249, N.v50249.
  rewrite ?node_50245.
  rewrite ?node_50248.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50250 (s : N.State) (i : N.Inputs) :
  R.v50250 (state s) (inputs i) = Zmod.unsigned (N.v50250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50250 s i)) at 1.
  unfold R.v50250, N.v50250.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50251 (s : N.State) (i : N.Inputs) :
  R.v50251 (state s) (inputs i) = Zmod.unsigned (N.v50251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50251 s i)) at 1.
  unfold R.v50251, N.v50251.
  rewrite ?node_8529.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50252 (s : N.State) (i : N.Inputs) :
  R.v50252 (state s) (inputs i) = Zmod.unsigned (N.v50252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50252 s i)) at 1.
  unfold R.v50252, N.v50252.
  rewrite ?node_8525.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50253 (s : N.State) (i : N.Inputs) :
  R.v50253 (state s) (inputs i) = Zmod.unsigned (N.v50253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50253 s i)) at 1.
  unfold R.v50253, N.v50253.
  rewrite ?node_8523.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50254 (s : N.State) (i : N.Inputs) :
  R.v50254 (state s) (inputs i) = Zmod.unsigned (N.v50254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50254 s i)) at 1.
  unfold R.v50254, N.v50254.
  unfold R.v6, N.v6.
  rewrite ?node_8519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50255 (s : N.State) (i : N.Inputs) :
  R.v50255 (state s) (inputs i) = Zmod.unsigned (N.v50255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50255 s i)) at 1.
  unfold R.v50255, N.v50255.
  unfold R.v6, N.v6.
  rewrite ?node_8516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50256 (s : N.State) (i : N.Inputs) :
  R.v50256 (state s) (inputs i) = Zmod.unsigned (N.v50256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50256 s i)) at 1.
  unfold R.v50256, N.v50256.
  rewrite ?node_50254.
  rewrite ?node_50255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50257 (s : N.State) (i : N.Inputs) :
  R.v50257 (state s) (inputs i) = Zmod.unsigned (N.v50257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50257 s i)) at 1.
  unfold R.v50257, N.v50257.
  unfold R.v16484, N.v16484.
  rewrite ?node_50256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50258 (s : N.State) (i : N.Inputs) :
  R.v50258 (state s) (inputs i) = Zmod.unsigned (N.v50258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50258 s i)) at 1.
  unfold R.v50258, N.v50258.
  rewrite ?node_50251.
  rewrite ?node_50252.
  rewrite ?node_50253.
  rewrite ?node_50257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50259 (s : N.State) (i : N.Inputs) :
  R.v50259 (state s) (inputs i) = Zmod.unsigned (N.v50259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50259 s i)) at 1.
  unfold R.v50259, N.v50259.
  unfold R.v6, N.v6.
  rewrite ?node_50258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50260 (s : N.State) (i : N.Inputs) :
  R.v50260 (state s) (inputs i) = Zmod.unsigned (N.v50260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50260 s i)) at 1.
  unfold R.v50260, N.v50260.
  rewrite ?node_8530.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50261 (s : N.State) (i : N.Inputs) :
  R.v50261 (state s) (inputs i) = Zmod.unsigned (N.v50261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50261 s i)) at 1.
  unfold R.v50261, N.v50261.
  unfold R.v6, N.v6.
  rewrite ?node_8659.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50262 (s : N.State) (i : N.Inputs) :
  R.v50262 (state s) (inputs i) = Zmod.unsigned (N.v50262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50262 s i)) at 1.
  unfold R.v50262, N.v50262.
  unfold R.v6, N.v6.
  rewrite ?node_8668.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50263 (s : N.State) (i : N.Inputs) :
  R.v50263 (state s) (inputs i) = Zmod.unsigned (N.v50263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50263 s i)) at 1.
  unfold R.v50263, N.v50263.
  rewrite ?node_50260.
  rewrite ?node_50261.
  rewrite ?node_50262.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50264 (s : N.State) (i : N.Inputs) :
  R.v50264 (state s) (inputs i) = Zmod.unsigned (N.v50264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50264 s i)) at 1.
  unfold R.v50264, N.v50264.
  rewrite ?node_50259.
  rewrite ?node_50263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50265 (s : N.State) (i : N.Inputs) :
  R.v50265 (state s) (inputs i) = Zmod.unsigned (N.v50265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50265 s i)) at 1.
  unfold R.v50265, N.v50265.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50266 (s : N.State) (i : N.Inputs) :
  R.v50266 (state s) (inputs i) = Zmod.unsigned (N.v50266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50266 s i)) at 1.
  unfold R.v50266, N.v50266.
  rewrite ?node_8523.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50267 (s : N.State) (i : N.Inputs) :
  R.v50267 (state s) (inputs i) = Zmod.unsigned (N.v50267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50267 s i)) at 1.
  unfold R.v50267, N.v50267.
  unfold R.v6, N.v6.
  rewrite ?node_8519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50268 (s : N.State) (i : N.Inputs) :
  R.v50268 (state s) (inputs i) = Zmod.unsigned (N.v50268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50268 s i)) at 1.
  unfold R.v50268, N.v50268.
  unfold R.v6, N.v6.
  rewrite ?node_8516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50269 (s : N.State) (i : N.Inputs) :
  R.v50269 (state s) (inputs i) = Zmod.unsigned (N.v50269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50269 s i)) at 1.
  unfold R.v50269, N.v50269.
  rewrite ?node_50267.
  rewrite ?node_50268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50270 (s : N.State) (i : N.Inputs) :
  R.v50270 (state s) (inputs i) = Zmod.unsigned (N.v50270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50270 s i)) at 1.
  unfold R.v50270, N.v50270.
  unfold R.v16484, N.v16484.
  rewrite ?node_50269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50271 (s : N.State) (i : N.Inputs) :
  R.v50271 (state s) (inputs i) = Zmod.unsigned (N.v50271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50271 s i)) at 1.
  unfold R.v50271, N.v50271.
  rewrite ?node_50266.
  rewrite ?node_50270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50272 (s : N.State) (i : N.Inputs) :
  R.v50272 (state s) (inputs i) = Zmod.unsigned (N.v50272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50272 s i)) at 1.
  unfold R.v50272, N.v50272.
  unfold R.v6, N.v6.
  rewrite ?node_50271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50273 (s : N.State) (i : N.Inputs) :
  R.v50273 (state s) (inputs i) = Zmod.unsigned (N.v50273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50273 s i)) at 1.
  unfold R.v50273, N.v50273.
  rewrite ?node_8524.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50274 (s : N.State) (i : N.Inputs) :
  R.v50274 (state s) (inputs i) = Zmod.unsigned (N.v50274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50274 s i)) at 1.
  unfold R.v50274, N.v50274.
  unfold R.v6, N.v6.
  rewrite ?node_8659.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50275 (s : N.State) (i : N.Inputs) :
  R.v50275 (state s) (inputs i) = Zmod.unsigned (N.v50275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50275 s i)) at 1.
  unfold R.v50275, N.v50275.
  rewrite ?node_50273.
  rewrite ?node_50274.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50276 (s : N.State) (i : N.Inputs) :
  R.v50276 (state s) (inputs i) = Zmod.unsigned (N.v50276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50276 s i)) at 1.
  unfold R.v50276, N.v50276.
  rewrite ?node_50272.
  rewrite ?node_50275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50277 (s : N.State) (i : N.Inputs) :
  R.v50277 (state s) (inputs i) = Zmod.unsigned (N.v50277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50277 s i)) at 1.
  unfold R.v50277, N.v50277.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50278 (s : N.State) (i : N.Inputs) :
  R.v50278 (state s) (inputs i) = Zmod.unsigned (N.v50278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50278 s i)) at 1.
  unfold R.v50278, N.v50278.
  rewrite ?node_8529.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50279 (s : N.State) (i : N.Inputs) :
  R.v50279 (state s) (inputs i) = Zmod.unsigned (N.v50279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50279 s i)) at 1.
  unfold R.v50279, N.v50279.
  unfold R.v6, N.v6.
  rewrite ?node_8525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50280 (s : N.State) (i : N.Inputs) :
  R.v50280 (state s) (inputs i) = Zmod.unsigned (N.v50280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50280 s i)) at 1.
  unfold R.v50280, N.v50280.
  unfold R.v6, N.v6.
  rewrite ?node_8524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50281 (s : N.State) (i : N.Inputs) :
  R.v50281 (state s) (inputs i) = Zmod.unsigned (N.v50281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50281 s i)) at 1.
  unfold R.v50281, N.v50281.
  rewrite ?node_50279.
  rewrite ?node_50280.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50282 (s : N.State) (i : N.Inputs) :
  R.v50282 (state s) (inputs i) = Zmod.unsigned (N.v50282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50282 s i)) at 1.
  unfold R.v50282, N.v50282.
  unfold R.v16484, N.v16484.
  rewrite ?node_50281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50283 (s : N.State) (i : N.Inputs) :
  R.v50283 (state s) (inputs i) = Zmod.unsigned (N.v50283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50283 s i)) at 1.
  unfold R.v50283, N.v50283.
  rewrite ?node_50278.
  rewrite ?node_50282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50284 (s : N.State) (i : N.Inputs) :
  R.v50284 (state s) (inputs i) = Zmod.unsigned (N.v50284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50284 s i)) at 1.
  unfold R.v50284, N.v50284.
  unfold R.v6, N.v6.
  rewrite ?node_50283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50285 (s : N.State) (i : N.Inputs) :
  R.v50285 (state s) (inputs i) = Zmod.unsigned (N.v50285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50285 s i)) at 1.
  unfold R.v50285, N.v50285.
  rewrite ?node_8530.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50286 (s : N.State) (i : N.Inputs) :
  R.v50286 (state s) (inputs i) = Zmod.unsigned (N.v50286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50286 s i)) at 1.
  unfold R.v50286, N.v50286.
  unfold R.v6, N.v6.
  rewrite ?node_8668.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50287 (s : N.State) (i : N.Inputs) :
  R.v50287 (state s) (inputs i) = Zmod.unsigned (N.v50287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50287 s i)) at 1.
  unfold R.v50287, N.v50287.
  rewrite ?node_50285.
  rewrite ?node_50286.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50288 (s : N.State) (i : N.Inputs) :
  R.v50288 (state s) (inputs i) = Zmod.unsigned (N.v50288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50288 s i)) at 1.
  unfold R.v50288, N.v50288.
  rewrite ?node_50284.
  rewrite ?node_50287.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50289 (s : N.State) (i : N.Inputs) :
  R.v50289 (state s) (inputs i) = Zmod.unsigned (N.v50289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50289 s i)) at 1.
  unfold R.v50289, N.v50289.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50290 (s : N.State) (i : N.Inputs) :
  R.v50290 (state s) (inputs i) = Zmod.unsigned (N.v50290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50290 s i)) at 1.
  unfold R.v50290, N.v50290.
  rewrite ?node_8642.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50291 (s : N.State) (i : N.Inputs) :
  R.v50291 (state s) (inputs i) = Zmod.unsigned (N.v50291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50291 s i)) at 1.
  unfold R.v50291, N.v50291.
  rewrite ?node_8638.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50292 (s : N.State) (i : N.Inputs) :
  R.v50292 (state s) (inputs i) = Zmod.unsigned (N.v50292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50292 s i)) at 1.
  unfold R.v50292, N.v50292.
  rewrite ?node_8630.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50293 (s : N.State) (i : N.Inputs) :
  R.v50293 (state s) (inputs i) = Zmod.unsigned (N.v50293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50293 s i)) at 1.
  unfold R.v50293, N.v50293.
  unfold R.v6, N.v6.
  rewrite ?node_8610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50294 (s : N.State) (i : N.Inputs) :
  R.v50294 (state s) (inputs i) = Zmod.unsigned (N.v50294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50294 s i)) at 1.
  unfold R.v50294, N.v50294.
  unfold R.v6, N.v6.
  rewrite ?node_8583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50295 (s : N.State) (i : N.Inputs) :
  R.v50295 (state s) (inputs i) = Zmod.unsigned (N.v50295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50295 s i)) at 1.
  unfold R.v50295, N.v50295.
  rewrite ?node_50293.
  rewrite ?node_50294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50296 (s : N.State) (i : N.Inputs) :
  R.v50296 (state s) (inputs i) = Zmod.unsigned (N.v50296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50296 s i)) at 1.
  unfold R.v50296, N.v50296.
  unfold R.v16484, N.v16484.
  rewrite ?node_50295.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50297 (s : N.State) (i : N.Inputs) :
  R.v50297 (state s) (inputs i) = Zmod.unsigned (N.v50297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50297 s i)) at 1.
  unfold R.v50297, N.v50297.
  rewrite ?node_50290.
  rewrite ?node_50291.
  rewrite ?node_50292.
  rewrite ?node_50296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50298 (s : N.State) (i : N.Inputs) :
  R.v50298 (state s) (inputs i) = Zmod.unsigned (N.v50298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50298 s i)) at 1.
  unfold R.v50298, N.v50298.
  unfold R.v6, N.v6.
  rewrite ?node_50297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50299 (s : N.State) (i : N.Inputs) :
  R.v50299 (state s) (inputs i) = Zmod.unsigned (N.v50299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50299 s i)) at 1.
  unfold R.v50299, N.v50299.
  rewrite ?node_8643.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50300 (s : N.State) (i : N.Inputs) :
  R.v50300 (state s) (inputs i) = Zmod.unsigned (N.v50300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50300 s i)) at 1.
  unfold R.v50300, N.v50300.
  unfold R.v6, N.v6.
  rewrite ?node_8776.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50301 (s : N.State) (i : N.Inputs) :
  R.v50301 (state s) (inputs i) = Zmod.unsigned (N.v50301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50301 s i)) at 1.
  unfold R.v50301, N.v50301.
  unfold R.v6, N.v6.
  rewrite ?node_8798.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50302 (s : N.State) (i : N.Inputs) :
  R.v50302 (state s) (inputs i) = Zmod.unsigned (N.v50302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50302 s i)) at 1.
  unfold R.v50302, N.v50302.
  rewrite ?node_50299.
  rewrite ?node_50300.
  rewrite ?node_50301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50303 (s : N.State) (i : N.Inputs) :
  R.v50303 (state s) (inputs i) = Zmod.unsigned (N.v50303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50303 s i)) at 1.
  unfold R.v50303, N.v50303.
  rewrite ?node_50298.
  rewrite ?node_50302.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50304 (s : N.State) (i : N.Inputs) :
  R.v50304 (state s) (inputs i) = Zmod.unsigned (N.v50304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50304 s i)) at 1.
  unfold R.v50304, N.v50304.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50305 (s : N.State) (i : N.Inputs) :
  R.v50305 (state s) (inputs i) = Zmod.unsigned (N.v50305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50305 s i)) at 1.
  unfold R.v50305, N.v50305.
  rewrite ?node_8630.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50306 (s : N.State) (i : N.Inputs) :
  R.v50306 (state s) (inputs i) = Zmod.unsigned (N.v50306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50306 s i)) at 1.
  unfold R.v50306, N.v50306.
  unfold R.v6, N.v6.
  rewrite ?node_8610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50307 (s : N.State) (i : N.Inputs) :
  R.v50307 (state s) (inputs i) = Zmod.unsigned (N.v50307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50307 s i)) at 1.
  unfold R.v50307, N.v50307.
  unfold R.v6, N.v6.
  rewrite ?node_8583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50308 (s : N.State) (i : N.Inputs) :
  R.v50308 (state s) (inputs i) = Zmod.unsigned (N.v50308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50308 s i)) at 1.
  unfold R.v50308, N.v50308.
  rewrite ?node_50306.
  rewrite ?node_50307.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50309 (s : N.State) (i : N.Inputs) :
  R.v50309 (state s) (inputs i) = Zmod.unsigned (N.v50309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50309 s i)) at 1.
  unfold R.v50309, N.v50309.
  unfold R.v16484, N.v16484.
  rewrite ?node_50308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50310 (s : N.State) (i : N.Inputs) :
  R.v50310 (state s) (inputs i) = Zmod.unsigned (N.v50310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50310 s i)) at 1.
  unfold R.v50310, N.v50310.
  rewrite ?node_50305.
  rewrite ?node_50309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50311 (s : N.State) (i : N.Inputs) :
  R.v50311 (state s) (inputs i) = Zmod.unsigned (N.v50311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50311 s i)) at 1.
  unfold R.v50311, N.v50311.
  unfold R.v6, N.v6.
  rewrite ?node_50310.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50312 (s : N.State) (i : N.Inputs) :
  R.v50312 (state s) (inputs i) = Zmod.unsigned (N.v50312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50312 s i)) at 1.
  unfold R.v50312, N.v50312.
  rewrite ?node_8631.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50313 (s : N.State) (i : N.Inputs) :
  R.v50313 (state s) (inputs i) = Zmod.unsigned (N.v50313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50313 s i)) at 1.
  unfold R.v50313, N.v50313.
  unfold R.v6, N.v6.
  rewrite ?node_8776.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50314 (s : N.State) (i : N.Inputs) :
  R.v50314 (state s) (inputs i) = Zmod.unsigned (N.v50314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50314 s i)) at 1.
  unfold R.v50314, N.v50314.
  rewrite ?node_50312.
  rewrite ?node_50313.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50315 (s : N.State) (i : N.Inputs) :
  R.v50315 (state s) (inputs i) = Zmod.unsigned (N.v50315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50315 s i)) at 1.
  unfold R.v50315, N.v50315.
  rewrite ?node_50311.
  rewrite ?node_50314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50316 (s : N.State) (i : N.Inputs) :
  R.v50316 (state s) (inputs i) = Zmod.unsigned (N.v50316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50316 s i)) at 1.
  unfold R.v50316, N.v50316.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50317 (s : N.State) (i : N.Inputs) :
  R.v50317 (state s) (inputs i) = Zmod.unsigned (N.v50317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50317 s i)) at 1.
  unfold R.v50317, N.v50317.
  rewrite ?node_8642.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50318 (s : N.State) (i : N.Inputs) :
  R.v50318 (state s) (inputs i) = Zmod.unsigned (N.v50318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50318 s i)) at 1.
  unfold R.v50318, N.v50318.
  unfold R.v6, N.v6.
  rewrite ?node_8638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50319 (s : N.State) (i : N.Inputs) :
  R.v50319 (state s) (inputs i) = Zmod.unsigned (N.v50319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50319 s i)) at 1.
  unfold R.v50319, N.v50319.
  unfold R.v6, N.v6.
  rewrite ?node_8631.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50320 (s : N.State) (i : N.Inputs) :
  R.v50320 (state s) (inputs i) = Zmod.unsigned (N.v50320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50320 s i)) at 1.
  unfold R.v50320, N.v50320.
  rewrite ?node_50318.
  rewrite ?node_50319.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50321 (s : N.State) (i : N.Inputs) :
  R.v50321 (state s) (inputs i) = Zmod.unsigned (N.v50321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50321 s i)) at 1.
  unfold R.v50321, N.v50321.
  unfold R.v16484, N.v16484.
  rewrite ?node_50320.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50322 (s : N.State) (i : N.Inputs) :
  R.v50322 (state s) (inputs i) = Zmod.unsigned (N.v50322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50322 s i)) at 1.
  unfold R.v50322, N.v50322.
  rewrite ?node_50317.
  rewrite ?node_50321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50323 (s : N.State) (i : N.Inputs) :
  R.v50323 (state s) (inputs i) = Zmod.unsigned (N.v50323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50323 s i)) at 1.
  unfold R.v50323, N.v50323.
  unfold R.v6, N.v6.
  rewrite ?node_50322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50324 (s : N.State) (i : N.Inputs) :
  R.v50324 (state s) (inputs i) = Zmod.unsigned (N.v50324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50324 s i)) at 1.
  unfold R.v50324, N.v50324.
  rewrite ?node_8643.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50325 (s : N.State) (i : N.Inputs) :
  R.v50325 (state s) (inputs i) = Zmod.unsigned (N.v50325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50325 s i)) at 1.
  unfold R.v50325, N.v50325.
  unfold R.v6, N.v6.
  rewrite ?node_8798.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50326 (s : N.State) (i : N.Inputs) :
  R.v50326 (state s) (inputs i) = Zmod.unsigned (N.v50326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50326 s i)) at 1.
  unfold R.v50326, N.v50326.
  rewrite ?node_50324.
  rewrite ?node_50325.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50327 (s : N.State) (i : N.Inputs) :
  R.v50327 (state s) (inputs i) = Zmod.unsigned (N.v50327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50327 s i)) at 1.
  unfold R.v50327, N.v50327.
  rewrite ?node_50323.
  rewrite ?node_50326.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50328 (s : N.State) (i : N.Inputs) :
  R.v50328 (state s) (inputs i) = Zmod.unsigned (N.v50328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50328 s i)) at 1.
  unfold R.v50328, N.v50328.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50329 (s : N.State) (i : N.Inputs) :
  R.v50329 (state s) (inputs i) = Zmod.unsigned (N.v50329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50329 s i)) at 1.
  unfold R.v50329, N.v50329.
  rewrite ?node_8659.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50330 (s : N.State) (i : N.Inputs) :
  R.v50330 (state s) (inputs i) = Zmod.unsigned (N.v50330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50330 s i)) at 1.
  unfold R.v50330, N.v50330.
  rewrite ?node_8655.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50331 (s : N.State) (i : N.Inputs) :
  R.v50331 (state s) (inputs i) = Zmod.unsigned (N.v50331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50331 s i)) at 1.
  unfold R.v50331, N.v50331.
  rewrite ?node_8653.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50332 (s : N.State) (i : N.Inputs) :
  R.v50332 (state s) (inputs i) = Zmod.unsigned (N.v50332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50332 s i)) at 1.
  unfold R.v50332, N.v50332.
  unfold R.v6, N.v6.
  rewrite ?node_8649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50333 (s : N.State) (i : N.Inputs) :
  R.v50333 (state s) (inputs i) = Zmod.unsigned (N.v50333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50333 s i)) at 1.
  unfold R.v50333, N.v50333.
  unfold R.v6, N.v6.
  rewrite ?node_8646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50334 (s : N.State) (i : N.Inputs) :
  R.v50334 (state s) (inputs i) = Zmod.unsigned (N.v50334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50334 s i)) at 1.
  unfold R.v50334, N.v50334.
  rewrite ?node_50332.
  rewrite ?node_50333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50335 (s : N.State) (i : N.Inputs) :
  R.v50335 (state s) (inputs i) = Zmod.unsigned (N.v50335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50335 s i)) at 1.
  unfold R.v50335, N.v50335.
  unfold R.v16484, N.v16484.
  rewrite ?node_50334.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50336 (s : N.State) (i : N.Inputs) :
  R.v50336 (state s) (inputs i) = Zmod.unsigned (N.v50336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50336 s i)) at 1.
  unfold R.v50336, N.v50336.
  rewrite ?node_50329.
  rewrite ?node_50330.
  rewrite ?node_50331.
  rewrite ?node_50335.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50337 (s : N.State) (i : N.Inputs) :
  R.v50337 (state s) (inputs i) = Zmod.unsigned (N.v50337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50337 s i)) at 1.
  unfold R.v50337, N.v50337.
  unfold R.v6, N.v6.
  rewrite ?node_50336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50338 (s : N.State) (i : N.Inputs) :
  R.v50338 (state s) (inputs i) = Zmod.unsigned (N.v50338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50338 s i)) at 1.
  unfold R.v50338, N.v50338.
  rewrite ?node_8660.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50339 (s : N.State) (i : N.Inputs) :
  R.v50339 (state s) (inputs i) = Zmod.unsigned (N.v50339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50339 s i)) at 1.
  unfold R.v50339, N.v50339.
  unfold R.v6, N.v6.
  rewrite ?node_8793.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50340 (s : N.State) (i : N.Inputs) :
  R.v50340 (state s) (inputs i) = Zmod.unsigned (N.v50340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50340 s i)) at 1.
  unfold R.v50340, N.v50340.
  unfold R.v6, N.v6.
  rewrite ?node_8802.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50341 (s : N.State) (i : N.Inputs) :
  R.v50341 (state s) (inputs i) = Zmod.unsigned (N.v50341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50341 s i)) at 1.
  unfold R.v50341, N.v50341.
  rewrite ?node_50338.
  rewrite ?node_50339.
  rewrite ?node_50340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50342 (s : N.State) (i : N.Inputs) :
  R.v50342 (state s) (inputs i) = Zmod.unsigned (N.v50342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50342 s i)) at 1.
  unfold R.v50342, N.v50342.
  rewrite ?node_50337.
  rewrite ?node_50341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50343 (s : N.State) (i : N.Inputs) :
  R.v50343 (state s) (inputs i) = Zmod.unsigned (N.v50343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50343 s i)) at 1.
  unfold R.v50343, N.v50343.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50344 (s : N.State) (i : N.Inputs) :
  R.v50344 (state s) (inputs i) = Zmod.unsigned (N.v50344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50344 s i)) at 1.
  unfold R.v50344, N.v50344.
  rewrite ?node_8653.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50345 (s : N.State) (i : N.Inputs) :
  R.v50345 (state s) (inputs i) = Zmod.unsigned (N.v50345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50345 s i)) at 1.
  unfold R.v50345, N.v50345.
  unfold R.v6, N.v6.
  rewrite ?node_8649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50346 (s : N.State) (i : N.Inputs) :
  R.v50346 (state s) (inputs i) = Zmod.unsigned (N.v50346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50346 s i)) at 1.
  unfold R.v50346, N.v50346.
  unfold R.v6, N.v6.
  rewrite ?node_8646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50347 (s : N.State) (i : N.Inputs) :
  R.v50347 (state s) (inputs i) = Zmod.unsigned (N.v50347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50347 s i)) at 1.
  unfold R.v50347, N.v50347.
  rewrite ?node_50345.
  rewrite ?node_50346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50348 (s : N.State) (i : N.Inputs) :
  R.v50348 (state s) (inputs i) = Zmod.unsigned (N.v50348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50348 s i)) at 1.
  unfold R.v50348, N.v50348.
  unfold R.v16484, N.v16484.
  rewrite ?node_50347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50349 (s : N.State) (i : N.Inputs) :
  R.v50349 (state s) (inputs i) = Zmod.unsigned (N.v50349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50349 s i)) at 1.
  unfold R.v50349, N.v50349.
  rewrite ?node_50344.
  rewrite ?node_50348.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50350 (s : N.State) (i : N.Inputs) :
  R.v50350 (state s) (inputs i) = Zmod.unsigned (N.v50350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50350 s i)) at 1.
  unfold R.v50350, N.v50350.
  unfold R.v6, N.v6.
  rewrite ?node_50349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50351 (s : N.State) (i : N.Inputs) :
  R.v50351 (state s) (inputs i) = Zmod.unsigned (N.v50351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50351 s i)) at 1.
  unfold R.v50351, N.v50351.
  rewrite ?node_8654.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50352 (s : N.State) (i : N.Inputs) :
  R.v50352 (state s) (inputs i) = Zmod.unsigned (N.v50352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50352 s i)) at 1.
  unfold R.v50352, N.v50352.
  unfold R.v6, N.v6.
  rewrite ?node_8793.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50353 (s : N.State) (i : N.Inputs) :
  R.v50353 (state s) (inputs i) = Zmod.unsigned (N.v50353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50353 s i)) at 1.
  unfold R.v50353, N.v50353.
  rewrite ?node_50351.
  rewrite ?node_50352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50354 (s : N.State) (i : N.Inputs) :
  R.v50354 (state s) (inputs i) = Zmod.unsigned (N.v50354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50354 s i)) at 1.
  unfold R.v50354, N.v50354.
  rewrite ?node_50350.
  rewrite ?node_50353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50355 (s : N.State) (i : N.Inputs) :
  R.v50355 (state s) (inputs i) = Zmod.unsigned (N.v50355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50355 s i)) at 1.
  unfold R.v50355, N.v50355.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50356 (s : N.State) (i : N.Inputs) :
  R.v50356 (state s) (inputs i) = Zmod.unsigned (N.v50356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50356 s i)) at 1.
  unfold R.v50356, N.v50356.
  rewrite ?node_8659.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50357 (s : N.State) (i : N.Inputs) :
  R.v50357 (state s) (inputs i) = Zmod.unsigned (N.v50357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50357 s i)) at 1.
  unfold R.v50357, N.v50357.
  unfold R.v6, N.v6.
  rewrite ?node_8655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50358 (s : N.State) (i : N.Inputs) :
  R.v50358 (state s) (inputs i) = Zmod.unsigned (N.v50358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50358 s i)) at 1.
  unfold R.v50358, N.v50358.
  unfold R.v6, N.v6.
  rewrite ?node_8654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50359 (s : N.State) (i : N.Inputs) :
  R.v50359 (state s) (inputs i) = Zmod.unsigned (N.v50359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50359 s i)) at 1.
  unfold R.v50359, N.v50359.
  rewrite ?node_50357.
  rewrite ?node_50358.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50360 (s : N.State) (i : N.Inputs) :
  R.v50360 (state s) (inputs i) = Zmod.unsigned (N.v50360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50360 s i)) at 1.
  unfold R.v50360, N.v50360.
  unfold R.v16484, N.v16484.
  rewrite ?node_50359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50361 (s : N.State) (i : N.Inputs) :
  R.v50361 (state s) (inputs i) = Zmod.unsigned (N.v50361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50361 s i)) at 1.
  unfold R.v50361, N.v50361.
  rewrite ?node_50356.
  rewrite ?node_50360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50362 (s : N.State) (i : N.Inputs) :
  R.v50362 (state s) (inputs i) = Zmod.unsigned (N.v50362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50362 s i)) at 1.
  unfold R.v50362, N.v50362.
  unfold R.v6, N.v6.
  rewrite ?node_50361.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50363 (s : N.State) (i : N.Inputs) :
  R.v50363 (state s) (inputs i) = Zmod.unsigned (N.v50363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50363 s i)) at 1.
  unfold R.v50363, N.v50363.
  rewrite ?node_8660.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50364 (s : N.State) (i : N.Inputs) :
  R.v50364 (state s) (inputs i) = Zmod.unsigned (N.v50364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50364 s i)) at 1.
  unfold R.v50364, N.v50364.
  unfold R.v6, N.v6.
  rewrite ?node_8802.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50365 (s : N.State) (i : N.Inputs) :
  R.v50365 (state s) (inputs i) = Zmod.unsigned (N.v50365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50365 s i)) at 1.
  unfold R.v50365, N.v50365.
  rewrite ?node_50363.
  rewrite ?node_50364.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50366 (s : N.State) (i : N.Inputs) :
  R.v50366 (state s) (inputs i) = Zmod.unsigned (N.v50366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50366 s i)) at 1.
  unfold R.v50366, N.v50366.
  rewrite ?node_50362.
  rewrite ?node_50365.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50367 (s : N.State) (i : N.Inputs) :
  R.v50367 (state s) (inputs i) = Zmod.unsigned (N.v50367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50367 s i)) at 1.
  unfold R.v50367, N.v50367.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50368 (s : N.State) (i : N.Inputs) :
  R.v50368 (state s) (inputs i) = Zmod.unsigned (N.v50368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50368 s i)) at 1.
  unfold R.v50368, N.v50368.
  rewrite ?node_8776.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50369 (s : N.State) (i : N.Inputs) :
  R.v50369 (state s) (inputs i) = Zmod.unsigned (N.v50369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50369 s i)) at 1.
  unfold R.v50369, N.v50369.
  rewrite ?node_8772.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50370 (s : N.State) (i : N.Inputs) :
  R.v50370 (state s) (inputs i) = Zmod.unsigned (N.v50370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50370 s i)) at 1.
  unfold R.v50370, N.v50370.
  rewrite ?node_8766.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50371 (s : N.State) (i : N.Inputs) :
  R.v50371 (state s) (inputs i) = Zmod.unsigned (N.v50371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50371 s i)) at 1.
  unfold R.v50371, N.v50371.
  unfold R.v6, N.v6.
  rewrite ?node_8746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50372 (s : N.State) (i : N.Inputs) :
  R.v50372 (state s) (inputs i) = Zmod.unsigned (N.v50372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50372 s i)) at 1.
  unfold R.v50372, N.v50372.
  unfold R.v6, N.v6.
  rewrite ?node_8715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50373 (s : N.State) (i : N.Inputs) :
  R.v50373 (state s) (inputs i) = Zmod.unsigned (N.v50373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50373 s i)) at 1.
  unfold R.v50373, N.v50373.
  rewrite ?node_50371.
  rewrite ?node_50372.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50374 (s : N.State) (i : N.Inputs) :
  R.v50374 (state s) (inputs i) = Zmod.unsigned (N.v50374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50374 s i)) at 1.
  unfold R.v50374, N.v50374.
  unfold R.v16484, N.v16484.
  rewrite ?node_50373.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50375 (s : N.State) (i : N.Inputs) :
  R.v50375 (state s) (inputs i) = Zmod.unsigned (N.v50375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50375 s i)) at 1.
  unfold R.v50375, N.v50375.
  rewrite ?node_50368.
  rewrite ?node_50369.
  rewrite ?node_50370.
  rewrite ?node_50374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50376 (s : N.State) (i : N.Inputs) :
  R.v50376 (state s) (inputs i) = Zmod.unsigned (N.v50376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50376 s i)) at 1.
  unfold R.v50376, N.v50376.
  unfold R.v6, N.v6.
  rewrite ?node_50375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50377 (s : N.State) (i : N.Inputs) :
  R.v50377 (state s) (inputs i) = Zmod.unsigned (N.v50377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50377 s i)) at 1.
  unfold R.v50377, N.v50377.
  rewrite ?node_8777.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50378 (s : N.State) (i : N.Inputs) :
  R.v50378 (state s) (inputs i) = Zmod.unsigned (N.v50378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50378 s i)) at 1.
  unfold R.v50378, N.v50378.
  unfold R.v6, N.v6.
  rewrite ?node_8913.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50379 (s : N.State) (i : N.Inputs) :
  R.v50379 (state s) (inputs i) = Zmod.unsigned (N.v50379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50379 s i)) at 1.
  unfold R.v50379, N.v50379.
  unfold R.v6, N.v6.
  rewrite ?node_8935.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50380 (s : N.State) (i : N.Inputs) :
  R.v50380 (state s) (inputs i) = Zmod.unsigned (N.v50380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50380 s i)) at 1.
  unfold R.v50380, N.v50380.
  rewrite ?node_50377.
  rewrite ?node_50378.
  rewrite ?node_50379.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50381 (s : N.State) (i : N.Inputs) :
  R.v50381 (state s) (inputs i) = Zmod.unsigned (N.v50381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50381 s i)) at 1.
  unfold R.v50381, N.v50381.
  rewrite ?node_50376.
  rewrite ?node_50380.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50382 (s : N.State) (i : N.Inputs) :
  R.v50382 (state s) (inputs i) = Zmod.unsigned (N.v50382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50382 s i)) at 1.
  unfold R.v50382, N.v50382.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50383 (s : N.State) (i : N.Inputs) :
  R.v50383 (state s) (inputs i) = Zmod.unsigned (N.v50383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50383 s i)) at 1.
  unfold R.v50383, N.v50383.
  rewrite ?node_8766.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50384 (s : N.State) (i : N.Inputs) :
  R.v50384 (state s) (inputs i) = Zmod.unsigned (N.v50384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50384 s i)) at 1.
  unfold R.v50384, N.v50384.
  unfold R.v6, N.v6.
  rewrite ?node_8746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50385 (s : N.State) (i : N.Inputs) :
  R.v50385 (state s) (inputs i) = Zmod.unsigned (N.v50385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50385 s i)) at 1.
  unfold R.v50385, N.v50385.
  unfold R.v6, N.v6.
  rewrite ?node_8715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50386 (s : N.State) (i : N.Inputs) :
  R.v50386 (state s) (inputs i) = Zmod.unsigned (N.v50386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50386 s i)) at 1.
  unfold R.v50386, N.v50386.
  rewrite ?node_50384.
  rewrite ?node_50385.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50387 (s : N.State) (i : N.Inputs) :
  R.v50387 (state s) (inputs i) = Zmod.unsigned (N.v50387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50387 s i)) at 1.
  unfold R.v50387, N.v50387.
  unfold R.v16484, N.v16484.
  rewrite ?node_50386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50388 (s : N.State) (i : N.Inputs) :
  R.v50388 (state s) (inputs i) = Zmod.unsigned (N.v50388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50388 s i)) at 1.
  unfold R.v50388, N.v50388.
  rewrite ?node_50383.
  rewrite ?node_50387.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50389 (s : N.State) (i : N.Inputs) :
  R.v50389 (state s) (inputs i) = Zmod.unsigned (N.v50389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50389 s i)) at 1.
  unfold R.v50389, N.v50389.
  unfold R.v6, N.v6.
  rewrite ?node_50388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50390 (s : N.State) (i : N.Inputs) :
  R.v50390 (state s) (inputs i) = Zmod.unsigned (N.v50390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50390 s i)) at 1.
  unfold R.v50390, N.v50390.
  rewrite ?node_8767.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50391 (s : N.State) (i : N.Inputs) :
  R.v50391 (state s) (inputs i) = Zmod.unsigned (N.v50391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50391 s i)) at 1.
  unfold R.v50391, N.v50391.
  unfold R.v6, N.v6.
  rewrite ?node_8913.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50392 (s : N.State) (i : N.Inputs) :
  R.v50392 (state s) (inputs i) = Zmod.unsigned (N.v50392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50392 s i)) at 1.
  unfold R.v50392, N.v50392.
  rewrite ?node_50390.
  rewrite ?node_50391.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50393 (s : N.State) (i : N.Inputs) :
  R.v50393 (state s) (inputs i) = Zmod.unsigned (N.v50393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50393 s i)) at 1.
  unfold R.v50393, N.v50393.
  rewrite ?node_50389.
  rewrite ?node_50392.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50394 (s : N.State) (i : N.Inputs) :
  R.v50394 (state s) (inputs i) = Zmod.unsigned (N.v50394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50394 s i)) at 1.
  unfold R.v50394, N.v50394.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50395 (s : N.State) (i : N.Inputs) :
  R.v50395 (state s) (inputs i) = Zmod.unsigned (N.v50395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50395 s i)) at 1.
  unfold R.v50395, N.v50395.
  rewrite ?node_8776.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50396 (s : N.State) (i : N.Inputs) :
  R.v50396 (state s) (inputs i) = Zmod.unsigned (N.v50396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50396 s i)) at 1.
  unfold R.v50396, N.v50396.
  unfold R.v6, N.v6.
  rewrite ?node_8772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50397 (s : N.State) (i : N.Inputs) :
  R.v50397 (state s) (inputs i) = Zmod.unsigned (N.v50397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50397 s i)) at 1.
  unfold R.v50397, N.v50397.
  unfold R.v6, N.v6.
  rewrite ?node_8767.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50398 (s : N.State) (i : N.Inputs) :
  R.v50398 (state s) (inputs i) = Zmod.unsigned (N.v50398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50398 s i)) at 1.
  unfold R.v50398, N.v50398.
  rewrite ?node_50396.
  rewrite ?node_50397.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50399 (s : N.State) (i : N.Inputs) :
  R.v50399 (state s) (inputs i) = Zmod.unsigned (N.v50399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50399 s i)) at 1.
  unfold R.v50399, N.v50399.
  unfold R.v16484, N.v16484.
  rewrite ?node_50398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50400 (s : N.State) (i : N.Inputs) :
  R.v50400 (state s) (inputs i) = Zmod.unsigned (N.v50400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50400 s i)) at 1.
  unfold R.v50400, N.v50400.
  rewrite ?node_50395.
  rewrite ?node_50399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50401 (s : N.State) (i : N.Inputs) :
  R.v50401 (state s) (inputs i) = Zmod.unsigned (N.v50401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50401 s i)) at 1.
  unfold R.v50401, N.v50401.
  unfold R.v6, N.v6.
  rewrite ?node_50400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50402 (s : N.State) (i : N.Inputs) :
  R.v50402 (state s) (inputs i) = Zmod.unsigned (N.v50402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50402 s i)) at 1.
  unfold R.v50402, N.v50402.
  rewrite ?node_8777.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50403 (s : N.State) (i : N.Inputs) :
  R.v50403 (state s) (inputs i) = Zmod.unsigned (N.v50403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50403 s i)) at 1.
  unfold R.v50403, N.v50403.
  unfold R.v6, N.v6.
  rewrite ?node_8935.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50404 (s : N.State) (i : N.Inputs) :
  R.v50404 (state s) (inputs i) = Zmod.unsigned (N.v50404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50404 s i)) at 1.
  unfold R.v50404, N.v50404.
  rewrite ?node_50402.
  rewrite ?node_50403.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50405 (s : N.State) (i : N.Inputs) :
  R.v50405 (state s) (inputs i) = Zmod.unsigned (N.v50405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50405 s i)) at 1.
  unfold R.v50405, N.v50405.
  rewrite ?node_50401.
  rewrite ?node_50404.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50406 (s : N.State) (i : N.Inputs) :
  R.v50406 (state s) (inputs i) = Zmod.unsigned (N.v50406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50406 s i)) at 1.
  unfold R.v50406, N.v50406.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50407 (s : N.State) (i : N.Inputs) :
  R.v50407 (state s) (inputs i) = Zmod.unsigned (N.v50407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50407 s i)) at 1.
  unfold R.v50407, N.v50407.
  rewrite ?node_8793.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50408 (s : N.State) (i : N.Inputs) :
  R.v50408 (state s) (inputs i) = Zmod.unsigned (N.v50408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50408 s i)) at 1.
  unfold R.v50408, N.v50408.
  rewrite ?node_8789.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50409 (s : N.State) (i : N.Inputs) :
  R.v50409 (state s) (inputs i) = Zmod.unsigned (N.v50409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50409 s i)) at 1.
  unfold R.v50409, N.v50409.
  rewrite ?node_8787.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50410 (s : N.State) (i : N.Inputs) :
  R.v50410 (state s) (inputs i) = Zmod.unsigned (N.v50410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50410 s i)) at 1.
  unfold R.v50410, N.v50410.
  unfold R.v6, N.v6.
  rewrite ?node_8783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50411 (s : N.State) (i : N.Inputs) :
  R.v50411 (state s) (inputs i) = Zmod.unsigned (N.v50411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50411 s i)) at 1.
  unfold R.v50411, N.v50411.
  unfold R.v6, N.v6.
  rewrite ?node_8780.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50412 (s : N.State) (i : N.Inputs) :
  R.v50412 (state s) (inputs i) = Zmod.unsigned (N.v50412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50412 s i)) at 1.
  unfold R.v50412, N.v50412.
  rewrite ?node_50410.
  rewrite ?node_50411.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50413 (s : N.State) (i : N.Inputs) :
  R.v50413 (state s) (inputs i) = Zmod.unsigned (N.v50413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50413 s i)) at 1.
  unfold R.v50413, N.v50413.
  unfold R.v16484, N.v16484.
  rewrite ?node_50412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50414 (s : N.State) (i : N.Inputs) :
  R.v50414 (state s) (inputs i) = Zmod.unsigned (N.v50414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50414 s i)) at 1.
  unfold R.v50414, N.v50414.
  rewrite ?node_50407.
  rewrite ?node_50408.
  rewrite ?node_50409.
  rewrite ?node_50413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50415 (s : N.State) (i : N.Inputs) :
  R.v50415 (state s) (inputs i) = Zmod.unsigned (N.v50415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50415 s i)) at 1.
  unfold R.v50415, N.v50415.
  unfold R.v6, N.v6.
  rewrite ?node_50414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50416 (s : N.State) (i : N.Inputs) :
  R.v50416 (state s) (inputs i) = Zmod.unsigned (N.v50416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50416 s i)) at 1.
  unfold R.v50416, N.v50416.
  rewrite ?node_8794.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50417 (s : N.State) (i : N.Inputs) :
  R.v50417 (state s) (inputs i) = Zmod.unsigned (N.v50417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50417 s i)) at 1.
  unfold R.v50417, N.v50417.
  unfold R.v6, N.v6.
  rewrite ?node_8930.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50418 (s : N.State) (i : N.Inputs) :
  R.v50418 (state s) (inputs i) = Zmod.unsigned (N.v50418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50418 s i)) at 1.
  unfold R.v50418, N.v50418.
  unfold R.v6, N.v6.
  rewrite ?node_8939.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50419 (s : N.State) (i : N.Inputs) :
  R.v50419 (state s) (inputs i) = Zmod.unsigned (N.v50419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50419 s i)) at 1.
  unfold R.v50419, N.v50419.
  rewrite ?node_50416.
  rewrite ?node_50417.
  rewrite ?node_50418.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50420 (s : N.State) (i : N.Inputs) :
  R.v50420 (state s) (inputs i) = Zmod.unsigned (N.v50420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50420 s i)) at 1.
  unfold R.v50420, N.v50420.
  rewrite ?node_50415.
  rewrite ?node_50419.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50421 (s : N.State) (i : N.Inputs) :
  R.v50421 (state s) (inputs i) = Zmod.unsigned (N.v50421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50421 s i)) at 1.
  unfold R.v50421, N.v50421.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50422 (s : N.State) (i : N.Inputs) :
  R.v50422 (state s) (inputs i) = Zmod.unsigned (N.v50422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50422 s i)) at 1.
  unfold R.v50422, N.v50422.
  rewrite ?node_8787.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50423 (s : N.State) (i : N.Inputs) :
  R.v50423 (state s) (inputs i) = Zmod.unsigned (N.v50423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50423 s i)) at 1.
  unfold R.v50423, N.v50423.
  unfold R.v6, N.v6.
  rewrite ?node_8783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50424 (s : N.State) (i : N.Inputs) :
  R.v50424 (state s) (inputs i) = Zmod.unsigned (N.v50424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50424 s i)) at 1.
  unfold R.v50424, N.v50424.
  unfold R.v6, N.v6.
  rewrite ?node_8780.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50425 (s : N.State) (i : N.Inputs) :
  R.v50425 (state s) (inputs i) = Zmod.unsigned (N.v50425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50425 s i)) at 1.
  unfold R.v50425, N.v50425.
  rewrite ?node_50423.
  rewrite ?node_50424.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50426 (s : N.State) (i : N.Inputs) :
  R.v50426 (state s) (inputs i) = Zmod.unsigned (N.v50426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50426 s i)) at 1.
  unfold R.v50426, N.v50426.
  unfold R.v16484, N.v16484.
  rewrite ?node_50425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50427 (s : N.State) (i : N.Inputs) :
  R.v50427 (state s) (inputs i) = Zmod.unsigned (N.v50427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50427 s i)) at 1.
  unfold R.v50427, N.v50427.
  rewrite ?node_50422.
  rewrite ?node_50426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50428 (s : N.State) (i : N.Inputs) :
  R.v50428 (state s) (inputs i) = Zmod.unsigned (N.v50428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50428 s i)) at 1.
  unfold R.v50428, N.v50428.
  unfold R.v6, N.v6.
  rewrite ?node_50427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50429 (s : N.State) (i : N.Inputs) :
  R.v50429 (state s) (inputs i) = Zmod.unsigned (N.v50429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50429 s i)) at 1.
  unfold R.v50429, N.v50429.
  rewrite ?node_8788.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50430 (s : N.State) (i : N.Inputs) :
  R.v50430 (state s) (inputs i) = Zmod.unsigned (N.v50430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50430 s i)) at 1.
  unfold R.v50430, N.v50430.
  unfold R.v6, N.v6.
  rewrite ?node_8930.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50431 (s : N.State) (i : N.Inputs) :
  R.v50431 (state s) (inputs i) = Zmod.unsigned (N.v50431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50431 s i)) at 1.
  unfold R.v50431, N.v50431.
  rewrite ?node_50429.
  rewrite ?node_50430.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50432 (s : N.State) (i : N.Inputs) :
  R.v50432 (state s) (inputs i) = Zmod.unsigned (N.v50432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50432 s i)) at 1.
  unfold R.v50432, N.v50432.
  rewrite ?node_50428.
  rewrite ?node_50431.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50433 (s : N.State) (i : N.Inputs) :
  R.v50433 (state s) (inputs i) = Zmod.unsigned (N.v50433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50433 s i)) at 1.
  unfold R.v50433, N.v50433.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50434 (s : N.State) (i : N.Inputs) :
  R.v50434 (state s) (inputs i) = Zmod.unsigned (N.v50434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50434 s i)) at 1.
  unfold R.v50434, N.v50434.
  rewrite ?node_8793.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50435 (s : N.State) (i : N.Inputs) :
  R.v50435 (state s) (inputs i) = Zmod.unsigned (N.v50435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50435 s i)) at 1.
  unfold R.v50435, N.v50435.
  unfold R.v6, N.v6.
  rewrite ?node_8789.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50436 (s : N.State) (i : N.Inputs) :
  R.v50436 (state s) (inputs i) = Zmod.unsigned (N.v50436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50436 s i)) at 1.
  unfold R.v50436, N.v50436.
  unfold R.v6, N.v6.
  rewrite ?node_8788.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50437 (s : N.State) (i : N.Inputs) :
  R.v50437 (state s) (inputs i) = Zmod.unsigned (N.v50437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50437 s i)) at 1.
  unfold R.v50437, N.v50437.
  rewrite ?node_50435.
  rewrite ?node_50436.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50438 (s : N.State) (i : N.Inputs) :
  R.v50438 (state s) (inputs i) = Zmod.unsigned (N.v50438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50438 s i)) at 1.
  unfold R.v50438, N.v50438.
  unfold R.v16484, N.v16484.
  rewrite ?node_50437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50439 (s : N.State) (i : N.Inputs) :
  R.v50439 (state s) (inputs i) = Zmod.unsigned (N.v50439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50439 s i)) at 1.
  unfold R.v50439, N.v50439.
  rewrite ?node_50434.
  rewrite ?node_50438.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50440 (s : N.State) (i : N.Inputs) :
  R.v50440 (state s) (inputs i) = Zmod.unsigned (N.v50440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50440 s i)) at 1.
  unfold R.v50440, N.v50440.
  unfold R.v6, N.v6.
  rewrite ?node_50439.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50441 (s : N.State) (i : N.Inputs) :
  R.v50441 (state s) (inputs i) = Zmod.unsigned (N.v50441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50441 s i)) at 1.
  unfold R.v50441, N.v50441.
  rewrite ?node_8794.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50442 (s : N.State) (i : N.Inputs) :
  R.v50442 (state s) (inputs i) = Zmod.unsigned (N.v50442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50442 s i)) at 1.
  unfold R.v50442, N.v50442.
  unfold R.v6, N.v6.
  rewrite ?node_8939.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50443 (s : N.State) (i : N.Inputs) :
  R.v50443 (state s) (inputs i) = Zmod.unsigned (N.v50443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50443 s i)) at 1.
  unfold R.v50443, N.v50443.
  rewrite ?node_50441.
  rewrite ?node_50442.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50444 (s : N.State) (i : N.Inputs) :
  R.v50444 (state s) (inputs i) = Zmod.unsigned (N.v50444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50444 s i)) at 1.
  unfold R.v50444, N.v50444.
  rewrite ?node_50440.
  rewrite ?node_50443.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50445 (s : N.State) (i : N.Inputs) :
  R.v50445 (state s) (inputs i) = Zmod.unsigned (N.v50445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50445 s i)) at 1.
  unfold R.v50445, N.v50445.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50446 (s : N.State) (i : N.Inputs) :
  R.v50446 (state s) (inputs i) = Zmod.unsigned (N.v50446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50446 s i)) at 1.
  unfold R.v50446, N.v50446.
  rewrite ?node_8913.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50447 (s : N.State) (i : N.Inputs) :
  R.v50447 (state s) (inputs i) = Zmod.unsigned (N.v50447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50447 s i)) at 1.
  unfold R.v50447, N.v50447.
  rewrite ?node_8909.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50448 (s : N.State) (i : N.Inputs) :
  R.v50448 (state s) (inputs i) = Zmod.unsigned (N.v50448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50448 s i)) at 1.
  unfold R.v50448, N.v50448.
  rewrite ?node_8897.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50449 (s : N.State) (i : N.Inputs) :
  R.v50449 (state s) (inputs i) = Zmod.unsigned (N.v50449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50449 s i)) at 1.
  unfold R.v50449, N.v50449.
  unfold R.v6, N.v6.
  rewrite ?node_8877.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50450 (s : N.State) (i : N.Inputs) :
  R.v50450 (state s) (inputs i) = Zmod.unsigned (N.v50450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50450 s i)) at 1.
  unfold R.v50450, N.v50450.
  unfold R.v6, N.v6.
  rewrite ?node_8849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50451 (s : N.State) (i : N.Inputs) :
  R.v50451 (state s) (inputs i) = Zmod.unsigned (N.v50451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50451 s i)) at 1.
  unfold R.v50451, N.v50451.
  rewrite ?node_50449.
  rewrite ?node_50450.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50452 (s : N.State) (i : N.Inputs) :
  R.v50452 (state s) (inputs i) = Zmod.unsigned (N.v50452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50452 s i)) at 1.
  unfold R.v50452, N.v50452.
  unfold R.v16484, N.v16484.
  rewrite ?node_50451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50453 (s : N.State) (i : N.Inputs) :
  R.v50453 (state s) (inputs i) = Zmod.unsigned (N.v50453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50453 s i)) at 1.
  unfold R.v50453, N.v50453.
  rewrite ?node_50446.
  rewrite ?node_50447.
  rewrite ?node_50448.
  rewrite ?node_50452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50454 (s : N.State) (i : N.Inputs) :
  R.v50454 (state s) (inputs i) = Zmod.unsigned (N.v50454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50454 s i)) at 1.
  unfold R.v50454, N.v50454.
  unfold R.v6, N.v6.
  rewrite ?node_50453.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50455 (s : N.State) (i : N.Inputs) :
  R.v50455 (state s) (inputs i) = Zmod.unsigned (N.v50455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50455 s i)) at 1.
  unfold R.v50455, N.v50455.
  rewrite ?node_8914.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50456 (s : N.State) (i : N.Inputs) :
  R.v50456 (state s) (inputs i) = Zmod.unsigned (N.v50456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50456 s i)) at 1.
  unfold R.v50456, N.v50456.
  unfold R.v6, N.v6.
  rewrite ?node_9050.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50457 (s : N.State) (i : N.Inputs) :
  R.v50457 (state s) (inputs i) = Zmod.unsigned (N.v50457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50457 s i)) at 1.
  unfold R.v50457, N.v50457.
  unfold R.v6, N.v6.
  rewrite ?node_9074.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50458 (s : N.State) (i : N.Inputs) :
  R.v50458 (state s) (inputs i) = Zmod.unsigned (N.v50458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50458 s i)) at 1.
  unfold R.v50458, N.v50458.
  rewrite ?node_50455.
  rewrite ?node_50456.
  rewrite ?node_50457.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50459 (s : N.State) (i : N.Inputs) :
  R.v50459 (state s) (inputs i) = Zmod.unsigned (N.v50459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50459 s i)) at 1.
  unfold R.v50459, N.v50459.
  rewrite ?node_50454.
  rewrite ?node_50458.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50460 (s : N.State) (i : N.Inputs) :
  R.v50460 (state s) (inputs i) = Zmod.unsigned (N.v50460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50460 s i)) at 1.
  unfold R.v50460, N.v50460.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50461 (s : N.State) (i : N.Inputs) :
  R.v50461 (state s) (inputs i) = Zmod.unsigned (N.v50461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50461 s i)) at 1.
  unfold R.v50461, N.v50461.
  rewrite ?node_8897.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50462 (s : N.State) (i : N.Inputs) :
  R.v50462 (state s) (inputs i) = Zmod.unsigned (N.v50462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50462 s i)) at 1.
  unfold R.v50462, N.v50462.
  unfold R.v6, N.v6.
  rewrite ?node_8877.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50463 (s : N.State) (i : N.Inputs) :
  R.v50463 (state s) (inputs i) = Zmod.unsigned (N.v50463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50463 s i)) at 1.
  unfold R.v50463, N.v50463.
  unfold R.v6, N.v6.
  rewrite ?node_8849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50464 (s : N.State) (i : N.Inputs) :
  R.v50464 (state s) (inputs i) = Zmod.unsigned (N.v50464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50464 s i)) at 1.
  unfold R.v50464, N.v50464.
  rewrite ?node_50462.
  rewrite ?node_50463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50465 (s : N.State) (i : N.Inputs) :
  R.v50465 (state s) (inputs i) = Zmod.unsigned (N.v50465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50465 s i)) at 1.
  unfold R.v50465, N.v50465.
  unfold R.v16484, N.v16484.
  rewrite ?node_50464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50466 (s : N.State) (i : N.Inputs) :
  R.v50466 (state s) (inputs i) = Zmod.unsigned (N.v50466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50466 s i)) at 1.
  unfold R.v50466, N.v50466.
  rewrite ?node_50461.
  rewrite ?node_50465.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50467 (s : N.State) (i : N.Inputs) :
  R.v50467 (state s) (inputs i) = Zmod.unsigned (N.v50467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50467 s i)) at 1.
  unfold R.v50467, N.v50467.
  unfold R.v6, N.v6.
  rewrite ?node_50466.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50468 (s : N.State) (i : N.Inputs) :
  R.v50468 (state s) (inputs i) = Zmod.unsigned (N.v50468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50468 s i)) at 1.
  unfold R.v50468, N.v50468.
  rewrite ?node_8898.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50469 (s : N.State) (i : N.Inputs) :
  R.v50469 (state s) (inputs i) = Zmod.unsigned (N.v50469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50469 s i)) at 1.
  unfold R.v50469, N.v50469.
  unfold R.v6, N.v6.
  rewrite ?node_9050.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50470 (s : N.State) (i : N.Inputs) :
  R.v50470 (state s) (inputs i) = Zmod.unsigned (N.v50470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50470 s i)) at 1.
  unfold R.v50470, N.v50470.
  rewrite ?node_50468.
  rewrite ?node_50469.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50471 (s : N.State) (i : N.Inputs) :
  R.v50471 (state s) (inputs i) = Zmod.unsigned (N.v50471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50471 s i)) at 1.
  unfold R.v50471, N.v50471.
  rewrite ?node_50467.
  rewrite ?node_50470.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50472 (s : N.State) (i : N.Inputs) :
  R.v50472 (state s) (inputs i) = Zmod.unsigned (N.v50472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50472 s i)) at 1.
  unfold R.v50472, N.v50472.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50473 (s : N.State) (i : N.Inputs) :
  R.v50473 (state s) (inputs i) = Zmod.unsigned (N.v50473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50473 s i)) at 1.
  unfold R.v50473, N.v50473.
  rewrite ?node_8913.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50474 (s : N.State) (i : N.Inputs) :
  R.v50474 (state s) (inputs i) = Zmod.unsigned (N.v50474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50474 s i)) at 1.
  unfold R.v50474, N.v50474.
  unfold R.v6, N.v6.
  rewrite ?node_8909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50475 (s : N.State) (i : N.Inputs) :
  R.v50475 (state s) (inputs i) = Zmod.unsigned (N.v50475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50475 s i)) at 1.
  unfold R.v50475, N.v50475.
  unfold R.v6, N.v6.
  rewrite ?node_8898.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50476 (s : N.State) (i : N.Inputs) :
  R.v50476 (state s) (inputs i) = Zmod.unsigned (N.v50476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50476 s i)) at 1.
  unfold R.v50476, N.v50476.
  rewrite ?node_50474.
  rewrite ?node_50475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50477 (s : N.State) (i : N.Inputs) :
  R.v50477 (state s) (inputs i) = Zmod.unsigned (N.v50477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50477 s i)) at 1.
  unfold R.v50477, N.v50477.
  unfold R.v16484, N.v16484.
  rewrite ?node_50476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50478 (s : N.State) (i : N.Inputs) :
  R.v50478 (state s) (inputs i) = Zmod.unsigned (N.v50478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50478 s i)) at 1.
  unfold R.v50478, N.v50478.
  rewrite ?node_50473.
  rewrite ?node_50477.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50479 (s : N.State) (i : N.Inputs) :
  R.v50479 (state s) (inputs i) = Zmod.unsigned (N.v50479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50479 s i)) at 1.
  unfold R.v50479, N.v50479.
  unfold R.v6, N.v6.
  rewrite ?node_50478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50480 (s : N.State) (i : N.Inputs) :
  R.v50480 (state s) (inputs i) = Zmod.unsigned (N.v50480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50480 s i)) at 1.
  unfold R.v50480, N.v50480.
  rewrite ?node_8914.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50481 (s : N.State) (i : N.Inputs) :
  R.v50481 (state s) (inputs i) = Zmod.unsigned (N.v50481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50481 s i)) at 1.
  unfold R.v50481, N.v50481.
  unfold R.v6, N.v6.
  rewrite ?node_9074.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50482 (s : N.State) (i : N.Inputs) :
  R.v50482 (state s) (inputs i) = Zmod.unsigned (N.v50482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50482 s i)) at 1.
  unfold R.v50482, N.v50482.
  rewrite ?node_50480.
  rewrite ?node_50481.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50483 (s : N.State) (i : N.Inputs) :
  R.v50483 (state s) (inputs i) = Zmod.unsigned (N.v50483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50483 s i)) at 1.
  unfold R.v50483, N.v50483.
  rewrite ?node_50479.
  rewrite ?node_50482.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50484 (s : N.State) (i : N.Inputs) :
  R.v50484 (state s) (inputs i) = Zmod.unsigned (N.v50484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50484 s i)) at 1.
  unfold R.v50484, N.v50484.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50485 (s : N.State) (i : N.Inputs) :
  R.v50485 (state s) (inputs i) = Zmod.unsigned (N.v50485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50485 s i)) at 1.
  unfold R.v50485, N.v50485.
  rewrite ?node_8930.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50486 (s : N.State) (i : N.Inputs) :
  R.v50486 (state s) (inputs i) = Zmod.unsigned (N.v50486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50486 s i)) at 1.
  unfold R.v50486, N.v50486.
  rewrite ?node_8926.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50487 (s : N.State) (i : N.Inputs) :
  R.v50487 (state s) (inputs i) = Zmod.unsigned (N.v50487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50487 s i)) at 1.
  unfold R.v50487, N.v50487.
  rewrite ?node_8924.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50488 (s : N.State) (i : N.Inputs) :
  R.v50488 (state s) (inputs i) = Zmod.unsigned (N.v50488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50488 s i)) at 1.
  unfold R.v50488, N.v50488.
  unfold R.v6, N.v6.
  rewrite ?node_8920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50489 (s : N.State) (i : N.Inputs) :
  R.v50489 (state s) (inputs i) = Zmod.unsigned (N.v50489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50489 s i)) at 1.
  unfold R.v50489, N.v50489.
  unfold R.v6, N.v6.
  rewrite ?node_8917.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50490 (s : N.State) (i : N.Inputs) :
  R.v50490 (state s) (inputs i) = Zmod.unsigned (N.v50490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50490 s i)) at 1.
  unfold R.v50490, N.v50490.
  rewrite ?node_50488.
  rewrite ?node_50489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50491 (s : N.State) (i : N.Inputs) :
  R.v50491 (state s) (inputs i) = Zmod.unsigned (N.v50491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50491 s i)) at 1.
  unfold R.v50491, N.v50491.
  unfold R.v16484, N.v16484.
  rewrite ?node_50490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50492 (s : N.State) (i : N.Inputs) :
  R.v50492 (state s) (inputs i) = Zmod.unsigned (N.v50492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50492 s i)) at 1.
  unfold R.v50492, N.v50492.
  rewrite ?node_50485.
  rewrite ?node_50486.
  rewrite ?node_50487.
  rewrite ?node_50491.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50493 (s : N.State) (i : N.Inputs) :
  R.v50493 (state s) (inputs i) = Zmod.unsigned (N.v50493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50493 s i)) at 1.
  unfold R.v50493, N.v50493.
  unfold R.v6, N.v6.
  rewrite ?node_50492.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50494 (s : N.State) (i : N.Inputs) :
  R.v50494 (state s) (inputs i) = Zmod.unsigned (N.v50494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50494 s i)) at 1.
  unfold R.v50494, N.v50494.
  rewrite ?node_8931.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50495 (s : N.State) (i : N.Inputs) :
  R.v50495 (state s) (inputs i) = Zmod.unsigned (N.v50495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50495 s i)) at 1.
  unfold R.v50495, N.v50495.
  unfold R.v6, N.v6.
  rewrite ?node_9069.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50496 (s : N.State) (i : N.Inputs) :
  R.v50496 (state s) (inputs i) = Zmod.unsigned (N.v50496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50496 s i)) at 1.
  unfold R.v50496, N.v50496.
  unfold R.v6, N.v6.
  rewrite ?node_9078.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50497 (s : N.State) (i : N.Inputs) :
  R.v50497 (state s) (inputs i) = Zmod.unsigned (N.v50497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50497 s i)) at 1.
  unfold R.v50497, N.v50497.
  rewrite ?node_50494.
  rewrite ?node_50495.
  rewrite ?node_50496.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50498 (s : N.State) (i : N.Inputs) :
  R.v50498 (state s) (inputs i) = Zmod.unsigned (N.v50498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50498 s i)) at 1.
  unfold R.v50498, N.v50498.
  rewrite ?node_50493.
  rewrite ?node_50497.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50499 (s : N.State) (i : N.Inputs) :
  R.v50499 (state s) (inputs i) = Zmod.unsigned (N.v50499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50499 s i)) at 1.
  unfold R.v50499, N.v50499.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50500 (s : N.State) (i : N.Inputs) :
  R.v50500 (state s) (inputs i) = Zmod.unsigned (N.v50500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50500 s i)) at 1.
  unfold R.v50500, N.v50500.
  rewrite ?node_8924.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50501 (s : N.State) (i : N.Inputs) :
  R.v50501 (state s) (inputs i) = Zmod.unsigned (N.v50501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50501 s i)) at 1.
  unfold R.v50501, N.v50501.
  unfold R.v6, N.v6.
  rewrite ?node_8920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50502 (s : N.State) (i : N.Inputs) :
  R.v50502 (state s) (inputs i) = Zmod.unsigned (N.v50502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50502 s i)) at 1.
  unfold R.v50502, N.v50502.
  unfold R.v6, N.v6.
  rewrite ?node_8917.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50503 (s : N.State) (i : N.Inputs) :
  R.v50503 (state s) (inputs i) = Zmod.unsigned (N.v50503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50503 s i)) at 1.
  unfold R.v50503, N.v50503.
  rewrite ?node_50501.
  rewrite ?node_50502.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50504 (s : N.State) (i : N.Inputs) :
  R.v50504 (state s) (inputs i) = Zmod.unsigned (N.v50504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50504 s i)) at 1.
  unfold R.v50504, N.v50504.
  unfold R.v16484, N.v16484.
  rewrite ?node_50503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50505 (s : N.State) (i : N.Inputs) :
  R.v50505 (state s) (inputs i) = Zmod.unsigned (N.v50505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50505 s i)) at 1.
  unfold R.v50505, N.v50505.
  rewrite ?node_50500.
  rewrite ?node_50504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50506 (s : N.State) (i : N.Inputs) :
  R.v50506 (state s) (inputs i) = Zmod.unsigned (N.v50506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50506 s i)) at 1.
  unfold R.v50506, N.v50506.
  unfold R.v6, N.v6.
  rewrite ?node_50505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50507 (s : N.State) (i : N.Inputs) :
  R.v50507 (state s) (inputs i) = Zmod.unsigned (N.v50507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50507 s i)) at 1.
  unfold R.v50507, N.v50507.
  rewrite ?node_8925.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50508 (s : N.State) (i : N.Inputs) :
  R.v50508 (state s) (inputs i) = Zmod.unsigned (N.v50508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50508 s i)) at 1.
  unfold R.v50508, N.v50508.
  unfold R.v6, N.v6.
  rewrite ?node_9069.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50509 (s : N.State) (i : N.Inputs) :
  R.v50509 (state s) (inputs i) = Zmod.unsigned (N.v50509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50509 s i)) at 1.
  unfold R.v50509, N.v50509.
  rewrite ?node_50507.
  rewrite ?node_50508.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50510 (s : N.State) (i : N.Inputs) :
  R.v50510 (state s) (inputs i) = Zmod.unsigned (N.v50510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50510 s i)) at 1.
  unfold R.v50510, N.v50510.
  rewrite ?node_50506.
  rewrite ?node_50509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50511 (s : N.State) (i : N.Inputs) :
  R.v50511 (state s) (inputs i) = Zmod.unsigned (N.v50511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50511 s i)) at 1.
  unfold R.v50511, N.v50511.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50512 (s : N.State) (i : N.Inputs) :
  R.v50512 (state s) (inputs i) = Zmod.unsigned (N.v50512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50512 s i)) at 1.
  unfold R.v50512, N.v50512.
  rewrite ?node_8930.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50513 (s : N.State) (i : N.Inputs) :
  R.v50513 (state s) (inputs i) = Zmod.unsigned (N.v50513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50513 s i)) at 1.
  unfold R.v50513, N.v50513.
  unfold R.v6, N.v6.
  rewrite ?node_8926.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50514 (s : N.State) (i : N.Inputs) :
  R.v50514 (state s) (inputs i) = Zmod.unsigned (N.v50514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50514 s i)) at 1.
  unfold R.v50514, N.v50514.
  unfold R.v6, N.v6.
  rewrite ?node_8925.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50515 (s : N.State) (i : N.Inputs) :
  R.v50515 (state s) (inputs i) = Zmod.unsigned (N.v50515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50515 s i)) at 1.
  unfold R.v50515, N.v50515.
  rewrite ?node_50513.
  rewrite ?node_50514.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50516 (s : N.State) (i : N.Inputs) :
  R.v50516 (state s) (inputs i) = Zmod.unsigned (N.v50516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50516 s i)) at 1.
  unfold R.v50516, N.v50516.
  unfold R.v16484, N.v16484.
  rewrite ?node_50515.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50517 (s : N.State) (i : N.Inputs) :
  R.v50517 (state s) (inputs i) = Zmod.unsigned (N.v50517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50517 s i)) at 1.
  unfold R.v50517, N.v50517.
  rewrite ?node_50512.
  rewrite ?node_50516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50518 (s : N.State) (i : N.Inputs) :
  R.v50518 (state s) (inputs i) = Zmod.unsigned (N.v50518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50518 s i)) at 1.
  unfold R.v50518, N.v50518.
  unfold R.v6, N.v6.
  rewrite ?node_50517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50519 (s : N.State) (i : N.Inputs) :
  R.v50519 (state s) (inputs i) = Zmod.unsigned (N.v50519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50519 s i)) at 1.
  unfold R.v50519, N.v50519.
  rewrite ?node_8931.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50520 (s : N.State) (i : N.Inputs) :
  R.v50520 (state s) (inputs i) = Zmod.unsigned (N.v50520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50520 s i)) at 1.
  unfold R.v50520, N.v50520.
  unfold R.v6, N.v6.
  rewrite ?node_9078.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50521 (s : N.State) (i : N.Inputs) :
  R.v50521 (state s) (inputs i) = Zmod.unsigned (N.v50521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50521 s i)) at 1.
  unfold R.v50521, N.v50521.
  rewrite ?node_50519.
  rewrite ?node_50520.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50522 (s : N.State) (i : N.Inputs) :
  R.v50522 (state s) (inputs i) = Zmod.unsigned (N.v50522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50522 s i)) at 1.
  unfold R.v50522, N.v50522.
  rewrite ?node_50518.
  rewrite ?node_50521.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50523 (s : N.State) (i : N.Inputs) :
  R.v50523 (state s) (inputs i) = Zmod.unsigned (N.v50523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50523 s i)) at 1.
  unfold R.v50523, N.v50523.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50524 (s : N.State) (i : N.Inputs) :
  R.v50524 (state s) (inputs i) = Zmod.unsigned (N.v50524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50524 s i)) at 1.
  unfold R.v50524, N.v50524.
  rewrite ?node_9050.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50525 (s : N.State) (i : N.Inputs) :
  R.v50525 (state s) (inputs i) = Zmod.unsigned (N.v50525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50525 s i)) at 1.
  unfold R.v50525, N.v50525.
  rewrite ?node_9046.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50526 (s : N.State) (i : N.Inputs) :
  R.v50526 (state s) (inputs i) = Zmod.unsigned (N.v50526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50526 s i)) at 1.
  unfold R.v50526, N.v50526.
  rewrite ?node_9034.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50527 (s : N.State) (i : N.Inputs) :
  R.v50527 (state s) (inputs i) = Zmod.unsigned (N.v50527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50527 s i)) at 1.
  unfold R.v50527, N.v50527.
  unfold R.v6, N.v6.
  rewrite ?node_9014.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50528 (s : N.State) (i : N.Inputs) :
  R.v50528 (state s) (inputs i) = Zmod.unsigned (N.v50528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50528 s i)) at 1.
  unfold R.v50528, N.v50528.
  unfold R.v6, N.v6.
  rewrite ?node_8986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50529 (s : N.State) (i : N.Inputs) :
  R.v50529 (state s) (inputs i) = Zmod.unsigned (N.v50529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50529 s i)) at 1.
  unfold R.v50529, N.v50529.
  rewrite ?node_50527.
  rewrite ?node_50528.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50530 (s : N.State) (i : N.Inputs) :
  R.v50530 (state s) (inputs i) = Zmod.unsigned (N.v50530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50530 s i)) at 1.
  unfold R.v50530, N.v50530.
  unfold R.v16484, N.v16484.
  rewrite ?node_50529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50531 (s : N.State) (i : N.Inputs) :
  R.v50531 (state s) (inputs i) = Zmod.unsigned (N.v50531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50531 s i)) at 1.
  unfold R.v50531, N.v50531.
  rewrite ?node_50524.
  rewrite ?node_50525.
  rewrite ?node_50526.
  rewrite ?node_50530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50532 (s : N.State) (i : N.Inputs) :
  R.v50532 (state s) (inputs i) = Zmod.unsigned (N.v50532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50532 s i)) at 1.
  unfold R.v50532, N.v50532.
  unfold R.v6, N.v6.
  rewrite ?node_50531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50533 (s : N.State) (i : N.Inputs) :
  R.v50533 (state s) (inputs i) = Zmod.unsigned (N.v50533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50533 s i)) at 1.
  unfold R.v50533, N.v50533.
  rewrite ?node_9051.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50534 (s : N.State) (i : N.Inputs) :
  R.v50534 (state s) (inputs i) = Zmod.unsigned (N.v50534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50534 s i)) at 1.
  unfold R.v50534, N.v50534.
  unfold R.v6, N.v6.
  rewrite ?node_9190.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50535 (s : N.State) (i : N.Inputs) :
  R.v50535 (state s) (inputs i) = Zmod.unsigned (N.v50535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50535 s i)) at 1.
  unfold R.v50535, N.v50535.
  unfold R.v6, N.v6.
  rewrite ?node_9214.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50536 (s : N.State) (i : N.Inputs) :
  R.v50536 (state s) (inputs i) = Zmod.unsigned (N.v50536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50536 s i)) at 1.
  unfold R.v50536, N.v50536.
  rewrite ?node_50533.
  rewrite ?node_50534.
  rewrite ?node_50535.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50537 (s : N.State) (i : N.Inputs) :
  R.v50537 (state s) (inputs i) = Zmod.unsigned (N.v50537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50537 s i)) at 1.
  unfold R.v50537, N.v50537.
  rewrite ?node_50532.
  rewrite ?node_50536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50538 (s : N.State) (i : N.Inputs) :
  R.v50538 (state s) (inputs i) = Zmod.unsigned (N.v50538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50538 s i)) at 1.
  unfold R.v50538, N.v50538.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50539 (s : N.State) (i : N.Inputs) :
  R.v50539 (state s) (inputs i) = Zmod.unsigned (N.v50539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50539 s i)) at 1.
  unfold R.v50539, N.v50539.
  rewrite ?node_9034.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50540 (s : N.State) (i : N.Inputs) :
  R.v50540 (state s) (inputs i) = Zmod.unsigned (N.v50540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50540 s i)) at 1.
  unfold R.v50540, N.v50540.
  unfold R.v6, N.v6.
  rewrite ?node_9014.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50541 (s : N.State) (i : N.Inputs) :
  R.v50541 (state s) (inputs i) = Zmod.unsigned (N.v50541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50541 s i)) at 1.
  unfold R.v50541, N.v50541.
  unfold R.v6, N.v6.
  rewrite ?node_8986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50542 (s : N.State) (i : N.Inputs) :
  R.v50542 (state s) (inputs i) = Zmod.unsigned (N.v50542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50542 s i)) at 1.
  unfold R.v50542, N.v50542.
  rewrite ?node_50540.
  rewrite ?node_50541.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50543 (s : N.State) (i : N.Inputs) :
  R.v50543 (state s) (inputs i) = Zmod.unsigned (N.v50543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50543 s i)) at 1.
  unfold R.v50543, N.v50543.
  unfold R.v16484, N.v16484.
  rewrite ?node_50542.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50544 (s : N.State) (i : N.Inputs) :
  R.v50544 (state s) (inputs i) = Zmod.unsigned (N.v50544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50544 s i)) at 1.
  unfold R.v50544, N.v50544.
  rewrite ?node_50539.
  rewrite ?node_50543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50545 (s : N.State) (i : N.Inputs) :
  R.v50545 (state s) (inputs i) = Zmod.unsigned (N.v50545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50545 s i)) at 1.
  unfold R.v50545, N.v50545.
  unfold R.v6, N.v6.
  rewrite ?node_50544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50546 (s : N.State) (i : N.Inputs) :
  R.v50546 (state s) (inputs i) = Zmod.unsigned (N.v50546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50546 s i)) at 1.
  unfold R.v50546, N.v50546.
  rewrite ?node_9035.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50547 (s : N.State) (i : N.Inputs) :
  R.v50547 (state s) (inputs i) = Zmod.unsigned (N.v50547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50547 s i)) at 1.
  unfold R.v50547, N.v50547.
  unfold R.v6, N.v6.
  rewrite ?node_9190.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50548 (s : N.State) (i : N.Inputs) :
  R.v50548 (state s) (inputs i) = Zmod.unsigned (N.v50548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50548 s i)) at 1.
  unfold R.v50548, N.v50548.
  rewrite ?node_50546.
  rewrite ?node_50547.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50549 (s : N.State) (i : N.Inputs) :
  R.v50549 (state s) (inputs i) = Zmod.unsigned (N.v50549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50549 s i)) at 1.
  unfold R.v50549, N.v50549.
  rewrite ?node_50545.
  rewrite ?node_50548.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50550 (s : N.State) (i : N.Inputs) :
  R.v50550 (state s) (inputs i) = Zmod.unsigned (N.v50550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50550 s i)) at 1.
  unfold R.v50550, N.v50550.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50551 (s : N.State) (i : N.Inputs) :
  R.v50551 (state s) (inputs i) = Zmod.unsigned (N.v50551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50551 s i)) at 1.
  unfold R.v50551, N.v50551.
  rewrite ?node_9050.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50552 (s : N.State) (i : N.Inputs) :
  R.v50552 (state s) (inputs i) = Zmod.unsigned (N.v50552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50552 s i)) at 1.
  unfold R.v50552, N.v50552.
  unfold R.v6, N.v6.
  rewrite ?node_9046.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50553 (s : N.State) (i : N.Inputs) :
  R.v50553 (state s) (inputs i) = Zmod.unsigned (N.v50553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50553 s i)) at 1.
  unfold R.v50553, N.v50553.
  unfold R.v6, N.v6.
  rewrite ?node_9035.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50554 (s : N.State) (i : N.Inputs) :
  R.v50554 (state s) (inputs i) = Zmod.unsigned (N.v50554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50554 s i)) at 1.
  unfold R.v50554, N.v50554.
  rewrite ?node_50552.
  rewrite ?node_50553.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50555 (s : N.State) (i : N.Inputs) :
  R.v50555 (state s) (inputs i) = Zmod.unsigned (N.v50555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50555 s i)) at 1.
  unfold R.v50555, N.v50555.
  unfold R.v16484, N.v16484.
  rewrite ?node_50554.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50556 (s : N.State) (i : N.Inputs) :
  R.v50556 (state s) (inputs i) = Zmod.unsigned (N.v50556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50556 s i)) at 1.
  unfold R.v50556, N.v50556.
  rewrite ?node_50551.
  rewrite ?node_50555.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50557 (s : N.State) (i : N.Inputs) :
  R.v50557 (state s) (inputs i) = Zmod.unsigned (N.v50557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50557 s i)) at 1.
  unfold R.v50557, N.v50557.
  unfold R.v6, N.v6.
  rewrite ?node_50556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50558 (s : N.State) (i : N.Inputs) :
  R.v50558 (state s) (inputs i) = Zmod.unsigned (N.v50558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50558 s i)) at 1.
  unfold R.v50558, N.v50558.
  rewrite ?node_9051.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50559 (s : N.State) (i : N.Inputs) :
  R.v50559 (state s) (inputs i) = Zmod.unsigned (N.v50559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50559 s i)) at 1.
  unfold R.v50559, N.v50559.
  unfold R.v6, N.v6.
  rewrite ?node_9214.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50560 (s : N.State) (i : N.Inputs) :
  R.v50560 (state s) (inputs i) = Zmod.unsigned (N.v50560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50560 s i)) at 1.
  unfold R.v50560, N.v50560.
  rewrite ?node_50558.
  rewrite ?node_50559.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50561 (s : N.State) (i : N.Inputs) :
  R.v50561 (state s) (inputs i) = Zmod.unsigned (N.v50561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50561 s i)) at 1.
  unfold R.v50561, N.v50561.
  rewrite ?node_50557.
  rewrite ?node_50560.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50562 (s : N.State) (i : N.Inputs) :
  R.v50562 (state s) (inputs i) = Zmod.unsigned (N.v50562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50562 s i)) at 1.
  unfold R.v50562, N.v50562.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50563 (s : N.State) (i : N.Inputs) :
  R.v50563 (state s) (inputs i) = Zmod.unsigned (N.v50563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50563 s i)) at 1.
  unfold R.v50563, N.v50563.
  rewrite ?node_9069.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50564 (s : N.State) (i : N.Inputs) :
  R.v50564 (state s) (inputs i) = Zmod.unsigned (N.v50564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50564 s i)) at 1.
  unfold R.v50564, N.v50564.
  rewrite ?node_9065.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50565 (s : N.State) (i : N.Inputs) :
  R.v50565 (state s) (inputs i) = Zmod.unsigned (N.v50565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50565 s i)) at 1.
  unfold R.v50565, N.v50565.
  rewrite ?node_9061.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50566 (s : N.State) (i : N.Inputs) :
  R.v50566 (state s) (inputs i) = Zmod.unsigned (N.v50566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50566 s i)) at 1.
  unfold R.v50566, N.v50566.
  unfold R.v6, N.v6.
  rewrite ?node_9057.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50567 (s : N.State) (i : N.Inputs) :
  R.v50567 (state s) (inputs i) = Zmod.unsigned (N.v50567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50567 s i)) at 1.
  unfold R.v50567, N.v50567.
  unfold R.v6, N.v6.
  rewrite ?node_9054.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50568 (s : N.State) (i : N.Inputs) :
  R.v50568 (state s) (inputs i) = Zmod.unsigned (N.v50568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50568 s i)) at 1.
  unfold R.v50568, N.v50568.
  rewrite ?node_50566.
  rewrite ?node_50567.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50569 (s : N.State) (i : N.Inputs) :
  R.v50569 (state s) (inputs i) = Zmod.unsigned (N.v50569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50569 s i)) at 1.
  unfold R.v50569, N.v50569.
  unfold R.v16484, N.v16484.
  rewrite ?node_50568.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50570 (s : N.State) (i : N.Inputs) :
  R.v50570 (state s) (inputs i) = Zmod.unsigned (N.v50570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50570 s i)) at 1.
  unfold R.v50570, N.v50570.
  rewrite ?node_50563.
  rewrite ?node_50564.
  rewrite ?node_50565.
  rewrite ?node_50569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50571 (s : N.State) (i : N.Inputs) :
  R.v50571 (state s) (inputs i) = Zmod.unsigned (N.v50571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50571 s i)) at 1.
  unfold R.v50571, N.v50571.
  unfold R.v6, N.v6.
  rewrite ?node_50570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50572 (s : N.State) (i : N.Inputs) :
  R.v50572 (state s) (inputs i) = Zmod.unsigned (N.v50572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50572 s i)) at 1.
  unfold R.v50572, N.v50572.
  rewrite ?node_9070.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50573 (s : N.State) (i : N.Inputs) :
  R.v50573 (state s) (inputs i) = Zmod.unsigned (N.v50573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50573 s i)) at 1.
  unfold R.v50573, N.v50573.
  unfold R.v6, N.v6.
  rewrite ?node_9209.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50574 (s : N.State) (i : N.Inputs) :
  R.v50574 (state s) (inputs i) = Zmod.unsigned (N.v50574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50574 s i)) at 1.
  unfold R.v50574, N.v50574.
  unfold R.v6, N.v6.
  rewrite ?node_9218.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50575 (s : N.State) (i : N.Inputs) :
  R.v50575 (state s) (inputs i) = Zmod.unsigned (N.v50575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50575 s i)) at 1.
  unfold R.v50575, N.v50575.
  rewrite ?node_50572.
  rewrite ?node_50573.
  rewrite ?node_50574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50576 (s : N.State) (i : N.Inputs) :
  R.v50576 (state s) (inputs i) = Zmod.unsigned (N.v50576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50576 s i)) at 1.
  unfold R.v50576, N.v50576.
  rewrite ?node_50571.
  rewrite ?node_50575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50577 (s : N.State) (i : N.Inputs) :
  R.v50577 (state s) (inputs i) = Zmod.unsigned (N.v50577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50577 s i)) at 1.
  unfold R.v50577, N.v50577.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50578 (s : N.State) (i : N.Inputs) :
  R.v50578 (state s) (inputs i) = Zmod.unsigned (N.v50578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50578 s i)) at 1.
  unfold R.v50578, N.v50578.
  rewrite ?node_9061.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50579 (s : N.State) (i : N.Inputs) :
  R.v50579 (state s) (inputs i) = Zmod.unsigned (N.v50579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50579 s i)) at 1.
  unfold R.v50579, N.v50579.
  unfold R.v6, N.v6.
  rewrite ?node_9057.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50580 (s : N.State) (i : N.Inputs) :
  R.v50580 (state s) (inputs i) = Zmod.unsigned (N.v50580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50580 s i)) at 1.
  unfold R.v50580, N.v50580.
  unfold R.v6, N.v6.
  rewrite ?node_9054.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50581 (s : N.State) (i : N.Inputs) :
  R.v50581 (state s) (inputs i) = Zmod.unsigned (N.v50581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50581 s i)) at 1.
  unfold R.v50581, N.v50581.
  rewrite ?node_50579.
  rewrite ?node_50580.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50582 (s : N.State) (i : N.Inputs) :
  R.v50582 (state s) (inputs i) = Zmod.unsigned (N.v50582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50582 s i)) at 1.
  unfold R.v50582, N.v50582.
  unfold R.v16484, N.v16484.
  rewrite ?node_50581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50583 (s : N.State) (i : N.Inputs) :
  R.v50583 (state s) (inputs i) = Zmod.unsigned (N.v50583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50583 s i)) at 1.
  unfold R.v50583, N.v50583.
  rewrite ?node_50578.
  rewrite ?node_50582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50584 (s : N.State) (i : N.Inputs) :
  R.v50584 (state s) (inputs i) = Zmod.unsigned (N.v50584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50584 s i)) at 1.
  unfold R.v50584, N.v50584.
  unfold R.v6, N.v6.
  rewrite ?node_50583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50585 (s : N.State) (i : N.Inputs) :
  R.v50585 (state s) (inputs i) = Zmod.unsigned (N.v50585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50585 s i)) at 1.
  unfold R.v50585, N.v50585.
  rewrite ?node_9062.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50586 (s : N.State) (i : N.Inputs) :
  R.v50586 (state s) (inputs i) = Zmod.unsigned (N.v50586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50586 s i)) at 1.
  unfold R.v50586, N.v50586.
  unfold R.v6, N.v6.
  rewrite ?node_9209.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50587 (s : N.State) (i : N.Inputs) :
  R.v50587 (state s) (inputs i) = Zmod.unsigned (N.v50587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50587 s i)) at 1.
  unfold R.v50587, N.v50587.
  rewrite ?node_50585.
  rewrite ?node_50586.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50588 (s : N.State) (i : N.Inputs) :
  R.v50588 (state s) (inputs i) = Zmod.unsigned (N.v50588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50588 s i)) at 1.
  unfold R.v50588, N.v50588.
  rewrite ?node_50584.
  rewrite ?node_50587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50589 (s : N.State) (i : N.Inputs) :
  R.v50589 (state s) (inputs i) = Zmod.unsigned (N.v50589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50589 s i)) at 1.
  unfold R.v50589, N.v50589.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50590 (s : N.State) (i : N.Inputs) :
  R.v50590 (state s) (inputs i) = Zmod.unsigned (N.v50590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50590 s i)) at 1.
  unfold R.v50590, N.v50590.
  rewrite ?node_9069.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50591 (s : N.State) (i : N.Inputs) :
  R.v50591 (state s) (inputs i) = Zmod.unsigned (N.v50591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50591 s i)) at 1.
  unfold R.v50591, N.v50591.
  unfold R.v6, N.v6.
  rewrite ?node_9065.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50592 (s : N.State) (i : N.Inputs) :
  R.v50592 (state s) (inputs i) = Zmod.unsigned (N.v50592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50592 s i)) at 1.
  unfold R.v50592, N.v50592.
  unfold R.v6, N.v6.
  rewrite ?node_9062.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50593 (s : N.State) (i : N.Inputs) :
  R.v50593 (state s) (inputs i) = Zmod.unsigned (N.v50593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50593 s i)) at 1.
  unfold R.v50593, N.v50593.
  rewrite ?node_50591.
  rewrite ?node_50592.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50594 (s : N.State) (i : N.Inputs) :
  R.v50594 (state s) (inputs i) = Zmod.unsigned (N.v50594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50594 s i)) at 1.
  unfold R.v50594, N.v50594.
  unfold R.v16484, N.v16484.
  rewrite ?node_50593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50595 (s : N.State) (i : N.Inputs) :
  R.v50595 (state s) (inputs i) = Zmod.unsigned (N.v50595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50595 s i)) at 1.
  unfold R.v50595, N.v50595.
  rewrite ?node_50590.
  rewrite ?node_50594.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50596 (s : N.State) (i : N.Inputs) :
  R.v50596 (state s) (inputs i) = Zmod.unsigned (N.v50596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50596 s i)) at 1.
  unfold R.v50596, N.v50596.
  unfold R.v6, N.v6.
  rewrite ?node_50595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50597 (s : N.State) (i : N.Inputs) :
  R.v50597 (state s) (inputs i) = Zmod.unsigned (N.v50597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50597 s i)) at 1.
  unfold R.v50597, N.v50597.
  rewrite ?node_9070.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50598 (s : N.State) (i : N.Inputs) :
  R.v50598 (state s) (inputs i) = Zmod.unsigned (N.v50598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50598 s i)) at 1.
  unfold R.v50598, N.v50598.
  unfold R.v6, N.v6.
  rewrite ?node_9218.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50599 (s : N.State) (i : N.Inputs) :
  R.v50599 (state s) (inputs i) = Zmod.unsigned (N.v50599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50599 s i)) at 1.
  unfold R.v50599, N.v50599.
  rewrite ?node_50597.
  rewrite ?node_50598.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50600 (s : N.State) (i : N.Inputs) :
  R.v50600 (state s) (inputs i) = Zmod.unsigned (N.v50600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50600 s i)) at 1.
  unfold R.v50600, N.v50600.
  rewrite ?node_50596.
  rewrite ?node_50599.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50601 (s : N.State) (i : N.Inputs) :
  R.v50601 (state s) (inputs i) = Zmod.unsigned (N.v50601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50601 s i)) at 1.
  unfold R.v50601, N.v50601.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50602 (s : N.State) (i : N.Inputs) :
  R.v50602 (state s) (inputs i) = Zmod.unsigned (N.v50602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50602 s i)) at 1.
  unfold R.v50602, N.v50602.
  rewrite ?node_9190.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50603 (s : N.State) (i : N.Inputs) :
  R.v50603 (state s) (inputs i) = Zmod.unsigned (N.v50603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50603 s i)) at 1.
  unfold R.v50603, N.v50603.
  rewrite ?node_9186.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50604 (s : N.State) (i : N.Inputs) :
  R.v50604 (state s) (inputs i) = Zmod.unsigned (N.v50604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50604 s i)) at 1.
  unfold R.v50604, N.v50604.
  rewrite ?node_9174.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50605 (s : N.State) (i : N.Inputs) :
  R.v50605 (state s) (inputs i) = Zmod.unsigned (N.v50605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50605 s i)) at 1.
  unfold R.v50605, N.v50605.
  unfold R.v6, N.v6.
  rewrite ?node_9154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50606 (s : N.State) (i : N.Inputs) :
  R.v50606 (state s) (inputs i) = Zmod.unsigned (N.v50606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50606 s i)) at 1.
  unfold R.v50606, N.v50606.
  unfold R.v6, N.v6.
  rewrite ?node_9125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50607 (s : N.State) (i : N.Inputs) :
  R.v50607 (state s) (inputs i) = Zmod.unsigned (N.v50607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50607 s i)) at 1.
  unfold R.v50607, N.v50607.
  rewrite ?node_50605.
  rewrite ?node_50606.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50608 (s : N.State) (i : N.Inputs) :
  R.v50608 (state s) (inputs i) = Zmod.unsigned (N.v50608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50608 s i)) at 1.
  unfold R.v50608, N.v50608.
  unfold R.v16484, N.v16484.
  rewrite ?node_50607.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50609 (s : N.State) (i : N.Inputs) :
  R.v50609 (state s) (inputs i) = Zmod.unsigned (N.v50609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50609 s i)) at 1.
  unfold R.v50609, N.v50609.
  rewrite ?node_50602.
  rewrite ?node_50603.
  rewrite ?node_50604.
  rewrite ?node_50608.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50610 (s : N.State) (i : N.Inputs) :
  R.v50610 (state s) (inputs i) = Zmod.unsigned (N.v50610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50610 s i)) at 1.
  unfold R.v50610, N.v50610.
  unfold R.v6, N.v6.
  rewrite ?node_50609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50611 (s : N.State) (i : N.Inputs) :
  R.v50611 (state s) (inputs i) = Zmod.unsigned (N.v50611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50611 s i)) at 1.
  unfold R.v50611, N.v50611.
  rewrite ?node_9191.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50612 (s : N.State) (i : N.Inputs) :
  R.v50612 (state s) (inputs i) = Zmod.unsigned (N.v50612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50612 s i)) at 1.
  unfold R.v50612, N.v50612.
  unfold R.v6, N.v6.
  rewrite ?node_9332.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50613 (s : N.State) (i : N.Inputs) :
  R.v50613 (state s) (inputs i) = Zmod.unsigned (N.v50613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50613 s i)) at 1.
  unfold R.v50613, N.v50613.
  unfold R.v6, N.v6.
  rewrite ?node_9356.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50614 (s : N.State) (i : N.Inputs) :
  R.v50614 (state s) (inputs i) = Zmod.unsigned (N.v50614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50614 s i)) at 1.
  unfold R.v50614, N.v50614.
  rewrite ?node_50611.
  rewrite ?node_50612.
  rewrite ?node_50613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50615 (s : N.State) (i : N.Inputs) :
  R.v50615 (state s) (inputs i) = Zmod.unsigned (N.v50615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50615 s i)) at 1.
  unfold R.v50615, N.v50615.
  rewrite ?node_50610.
  rewrite ?node_50614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50616 (s : N.State) (i : N.Inputs) :
  R.v50616 (state s) (inputs i) = Zmod.unsigned (N.v50616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50616 s i)) at 1.
  unfold R.v50616, N.v50616.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50617 (s : N.State) (i : N.Inputs) :
  R.v50617 (state s) (inputs i) = Zmod.unsigned (N.v50617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50617 s i)) at 1.
  unfold R.v50617, N.v50617.
  rewrite ?node_9174.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50618 (s : N.State) (i : N.Inputs) :
  R.v50618 (state s) (inputs i) = Zmod.unsigned (N.v50618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50618 s i)) at 1.
  unfold R.v50618, N.v50618.
  unfold R.v6, N.v6.
  rewrite ?node_9154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50619 (s : N.State) (i : N.Inputs) :
  R.v50619 (state s) (inputs i) = Zmod.unsigned (N.v50619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50619 s i)) at 1.
  unfold R.v50619, N.v50619.
  unfold R.v6, N.v6.
  rewrite ?node_9125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50620 (s : N.State) (i : N.Inputs) :
  R.v50620 (state s) (inputs i) = Zmod.unsigned (N.v50620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50620 s i)) at 1.
  unfold R.v50620, N.v50620.
  rewrite ?node_50618.
  rewrite ?node_50619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50621 (s : N.State) (i : N.Inputs) :
  R.v50621 (state s) (inputs i) = Zmod.unsigned (N.v50621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50621 s i)) at 1.
  unfold R.v50621, N.v50621.
  unfold R.v16484, N.v16484.
  rewrite ?node_50620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50622 (s : N.State) (i : N.Inputs) :
  R.v50622 (state s) (inputs i) = Zmod.unsigned (N.v50622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50622 s i)) at 1.
  unfold R.v50622, N.v50622.
  rewrite ?node_50617.
  rewrite ?node_50621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50623 (s : N.State) (i : N.Inputs) :
  R.v50623 (state s) (inputs i) = Zmod.unsigned (N.v50623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50623 s i)) at 1.
  unfold R.v50623, N.v50623.
  unfold R.v6, N.v6.
  rewrite ?node_50622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50624 (s : N.State) (i : N.Inputs) :
  R.v50624 (state s) (inputs i) = Zmod.unsigned (N.v50624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50624 s i)) at 1.
  unfold R.v50624, N.v50624.
  rewrite ?node_9175.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50625 (s : N.State) (i : N.Inputs) :
  R.v50625 (state s) (inputs i) = Zmod.unsigned (N.v50625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50625 s i)) at 1.
  unfold R.v50625, N.v50625.
  unfold R.v6, N.v6.
  rewrite ?node_9332.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50626 (s : N.State) (i : N.Inputs) :
  R.v50626 (state s) (inputs i) = Zmod.unsigned (N.v50626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50626 s i)) at 1.
  unfold R.v50626, N.v50626.
  rewrite ?node_50624.
  rewrite ?node_50625.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50627 (s : N.State) (i : N.Inputs) :
  R.v50627 (state s) (inputs i) = Zmod.unsigned (N.v50627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50627 s i)) at 1.
  unfold R.v50627, N.v50627.
  rewrite ?node_50623.
  rewrite ?node_50626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50628 (s : N.State) (i : N.Inputs) :
  R.v50628 (state s) (inputs i) = Zmod.unsigned (N.v50628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50628 s i)) at 1.
  unfold R.v50628, N.v50628.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50629 (s : N.State) (i : N.Inputs) :
  R.v50629 (state s) (inputs i) = Zmod.unsigned (N.v50629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50629 s i)) at 1.
  unfold R.v50629, N.v50629.
  rewrite ?node_9190.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50630 (s : N.State) (i : N.Inputs) :
  R.v50630 (state s) (inputs i) = Zmod.unsigned (N.v50630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50630 s i)) at 1.
  unfold R.v50630, N.v50630.
  unfold R.v6, N.v6.
  rewrite ?node_9186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50631 (s : N.State) (i : N.Inputs) :
  R.v50631 (state s) (inputs i) = Zmod.unsigned (N.v50631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50631 s i)) at 1.
  unfold R.v50631, N.v50631.
  unfold R.v6, N.v6.
  rewrite ?node_9175.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50632 (s : N.State) (i : N.Inputs) :
  R.v50632 (state s) (inputs i) = Zmod.unsigned (N.v50632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50632 s i)) at 1.
  unfold R.v50632, N.v50632.
  rewrite ?node_50630.
  rewrite ?node_50631.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50633 (s : N.State) (i : N.Inputs) :
  R.v50633 (state s) (inputs i) = Zmod.unsigned (N.v50633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50633 s i)) at 1.
  unfold R.v50633, N.v50633.
  unfold R.v16484, N.v16484.
  rewrite ?node_50632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50634 (s : N.State) (i : N.Inputs) :
  R.v50634 (state s) (inputs i) = Zmod.unsigned (N.v50634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50634 s i)) at 1.
  unfold R.v50634, N.v50634.
  rewrite ?node_50629.
  rewrite ?node_50633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50635 (s : N.State) (i : N.Inputs) :
  R.v50635 (state s) (inputs i) = Zmod.unsigned (N.v50635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50635 s i)) at 1.
  unfold R.v50635, N.v50635.
  unfold R.v6, N.v6.
  rewrite ?node_50634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50636 (s : N.State) (i : N.Inputs) :
  R.v50636 (state s) (inputs i) = Zmod.unsigned (N.v50636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50636 s i)) at 1.
  unfold R.v50636, N.v50636.
  rewrite ?node_9191.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50637 (s : N.State) (i : N.Inputs) :
  R.v50637 (state s) (inputs i) = Zmod.unsigned (N.v50637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50637 s i)) at 1.
  unfold R.v50637, N.v50637.
  unfold R.v6, N.v6.
  rewrite ?node_9356.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50638 (s : N.State) (i : N.Inputs) :
  R.v50638 (state s) (inputs i) = Zmod.unsigned (N.v50638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50638 s i)) at 1.
  unfold R.v50638, N.v50638.
  rewrite ?node_50636.
  rewrite ?node_50637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50639 (s : N.State) (i : N.Inputs) :
  R.v50639 (state s) (inputs i) = Zmod.unsigned (N.v50639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50639 s i)) at 1.
  unfold R.v50639, N.v50639.
  rewrite ?node_50635.
  rewrite ?node_50638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50640 (s : N.State) (i : N.Inputs) :
  R.v50640 (state s) (inputs i) = Zmod.unsigned (N.v50640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50640 s i)) at 1.
  unfold R.v50640, N.v50640.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50641 (s : N.State) (i : N.Inputs) :
  R.v50641 (state s) (inputs i) = Zmod.unsigned (N.v50641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50641 s i)) at 1.
  unfold R.v50641, N.v50641.
  rewrite ?node_9209.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50642 (s : N.State) (i : N.Inputs) :
  R.v50642 (state s) (inputs i) = Zmod.unsigned (N.v50642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50642 s i)) at 1.
  unfold R.v50642, N.v50642.
  rewrite ?node_9205.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50643 (s : N.State) (i : N.Inputs) :
  R.v50643 (state s) (inputs i) = Zmod.unsigned (N.v50643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50643 s i)) at 1.
  unfold R.v50643, N.v50643.
  rewrite ?node_9201.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50644 (s : N.State) (i : N.Inputs) :
  R.v50644 (state s) (inputs i) = Zmod.unsigned (N.v50644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50644 s i)) at 1.
  unfold R.v50644, N.v50644.
  unfold R.v6, N.v6.
  rewrite ?node_9197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50645 (s : N.State) (i : N.Inputs) :
  R.v50645 (state s) (inputs i) = Zmod.unsigned (N.v50645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50645 s i)) at 1.
  unfold R.v50645, N.v50645.
  unfold R.v6, N.v6.
  rewrite ?node_9194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50646 (s : N.State) (i : N.Inputs) :
  R.v50646 (state s) (inputs i) = Zmod.unsigned (N.v50646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50646 s i)) at 1.
  unfold R.v50646, N.v50646.
  rewrite ?node_50644.
  rewrite ?node_50645.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50647 (s : N.State) (i : N.Inputs) :
  R.v50647 (state s) (inputs i) = Zmod.unsigned (N.v50647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50647 s i)) at 1.
  unfold R.v50647, N.v50647.
  unfold R.v16484, N.v16484.
  rewrite ?node_50646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50648 (s : N.State) (i : N.Inputs) :
  R.v50648 (state s) (inputs i) = Zmod.unsigned (N.v50648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50648 s i)) at 1.
  unfold R.v50648, N.v50648.
  rewrite ?node_50641.
  rewrite ?node_50642.
  rewrite ?node_50643.
  rewrite ?node_50647.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50649 (s : N.State) (i : N.Inputs) :
  R.v50649 (state s) (inputs i) = Zmod.unsigned (N.v50649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50649 s i)) at 1.
  unfold R.v50649, N.v50649.
  unfold R.v6, N.v6.
  rewrite ?node_50648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50650 (s : N.State) (i : N.Inputs) :
  R.v50650 (state s) (inputs i) = Zmod.unsigned (N.v50650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50650 s i)) at 1.
  unfold R.v50650, N.v50650.
  rewrite ?node_9210.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50651 (s : N.State) (i : N.Inputs) :
  R.v50651 (state s) (inputs i) = Zmod.unsigned (N.v50651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50651 s i)) at 1.
  unfold R.v50651, N.v50651.
  unfold R.v6, N.v6.
  rewrite ?node_9351.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50652 (s : N.State) (i : N.Inputs) :
  R.v50652 (state s) (inputs i) = Zmod.unsigned (N.v50652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50652 s i)) at 1.
  unfold R.v50652, N.v50652.
  unfold R.v6, N.v6.
  rewrite ?node_9360.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50653 (s : N.State) (i : N.Inputs) :
  R.v50653 (state s) (inputs i) = Zmod.unsigned (N.v50653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50653 s i)) at 1.
  unfold R.v50653, N.v50653.
  rewrite ?node_50650.
  rewrite ?node_50651.
  rewrite ?node_50652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50654 (s : N.State) (i : N.Inputs) :
  R.v50654 (state s) (inputs i) = Zmod.unsigned (N.v50654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50654 s i)) at 1.
  unfold R.v50654, N.v50654.
  rewrite ?node_50649.
  rewrite ?node_50653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50655 (s : N.State) (i : N.Inputs) :
  R.v50655 (state s) (inputs i) = Zmod.unsigned (N.v50655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50655 s i)) at 1.
  unfold R.v50655, N.v50655.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50656 (s : N.State) (i : N.Inputs) :
  R.v50656 (state s) (inputs i) = Zmod.unsigned (N.v50656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50656 s i)) at 1.
  unfold R.v50656, N.v50656.
  rewrite ?node_9201.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50657 (s : N.State) (i : N.Inputs) :
  R.v50657 (state s) (inputs i) = Zmod.unsigned (N.v50657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50657 s i)) at 1.
  unfold R.v50657, N.v50657.
  unfold R.v6, N.v6.
  rewrite ?node_9197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50658 (s : N.State) (i : N.Inputs) :
  R.v50658 (state s) (inputs i) = Zmod.unsigned (N.v50658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50658 s i)) at 1.
  unfold R.v50658, N.v50658.
  unfold R.v6, N.v6.
  rewrite ?node_9194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50659 (s : N.State) (i : N.Inputs) :
  R.v50659 (state s) (inputs i) = Zmod.unsigned (N.v50659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50659 s i)) at 1.
  unfold R.v50659, N.v50659.
  rewrite ?node_50657.
  rewrite ?node_50658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50660 (s : N.State) (i : N.Inputs) :
  R.v50660 (state s) (inputs i) = Zmod.unsigned (N.v50660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50660 s i)) at 1.
  unfold R.v50660, N.v50660.
  unfold R.v16484, N.v16484.
  rewrite ?node_50659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50661 (s : N.State) (i : N.Inputs) :
  R.v50661 (state s) (inputs i) = Zmod.unsigned (N.v50661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50661 s i)) at 1.
  unfold R.v50661, N.v50661.
  rewrite ?node_50656.
  rewrite ?node_50660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50662 (s : N.State) (i : N.Inputs) :
  R.v50662 (state s) (inputs i) = Zmod.unsigned (N.v50662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50662 s i)) at 1.
  unfold R.v50662, N.v50662.
  unfold R.v6, N.v6.
  rewrite ?node_50661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50663 (s : N.State) (i : N.Inputs) :
  R.v50663 (state s) (inputs i) = Zmod.unsigned (N.v50663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50663 s i)) at 1.
  unfold R.v50663, N.v50663.
  rewrite ?node_9202.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50664 (s : N.State) (i : N.Inputs) :
  R.v50664 (state s) (inputs i) = Zmod.unsigned (N.v50664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50664 s i)) at 1.
  unfold R.v50664, N.v50664.
  unfold R.v6, N.v6.
  rewrite ?node_9351.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50665 (s : N.State) (i : N.Inputs) :
  R.v50665 (state s) (inputs i) = Zmod.unsigned (N.v50665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50665 s i)) at 1.
  unfold R.v50665, N.v50665.
  rewrite ?node_50663.
  rewrite ?node_50664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50666 (s : N.State) (i : N.Inputs) :
  R.v50666 (state s) (inputs i) = Zmod.unsigned (N.v50666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50666 s i)) at 1.
  unfold R.v50666, N.v50666.
  rewrite ?node_50662.
  rewrite ?node_50665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50667 (s : N.State) (i : N.Inputs) :
  R.v50667 (state s) (inputs i) = Zmod.unsigned (N.v50667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50667 s i)) at 1.
  unfold R.v50667, N.v50667.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50668 (s : N.State) (i : N.Inputs) :
  R.v50668 (state s) (inputs i) = Zmod.unsigned (N.v50668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50668 s i)) at 1.
  unfold R.v50668, N.v50668.
  rewrite ?node_9209.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50669 (s : N.State) (i : N.Inputs) :
  R.v50669 (state s) (inputs i) = Zmod.unsigned (N.v50669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50669 s i)) at 1.
  unfold R.v50669, N.v50669.
  unfold R.v6, N.v6.
  rewrite ?node_9205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50670 (s : N.State) (i : N.Inputs) :
  R.v50670 (state s) (inputs i) = Zmod.unsigned (N.v50670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50670 s i)) at 1.
  unfold R.v50670, N.v50670.
  unfold R.v6, N.v6.
  rewrite ?node_9202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50671 (s : N.State) (i : N.Inputs) :
  R.v50671 (state s) (inputs i) = Zmod.unsigned (N.v50671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50671 s i)) at 1.
  unfold R.v50671, N.v50671.
  rewrite ?node_50669.
  rewrite ?node_50670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50672 (s : N.State) (i : N.Inputs) :
  R.v50672 (state s) (inputs i) = Zmod.unsigned (N.v50672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50672 s i)) at 1.
  unfold R.v50672, N.v50672.
  unfold R.v16484, N.v16484.
  rewrite ?node_50671.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50673 (s : N.State) (i : N.Inputs) :
  R.v50673 (state s) (inputs i) = Zmod.unsigned (N.v50673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50673 s i)) at 1.
  unfold R.v50673, N.v50673.
  rewrite ?node_50668.
  rewrite ?node_50672.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50674 (s : N.State) (i : N.Inputs) :
  R.v50674 (state s) (inputs i) = Zmod.unsigned (N.v50674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50674 s i)) at 1.
  unfold R.v50674, N.v50674.
  unfold R.v6, N.v6.
  rewrite ?node_50673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50675 (s : N.State) (i : N.Inputs) :
  R.v50675 (state s) (inputs i) = Zmod.unsigned (N.v50675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50675 s i)) at 1.
  unfold R.v50675, N.v50675.
  rewrite ?node_9210.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50676 (s : N.State) (i : N.Inputs) :
  R.v50676 (state s) (inputs i) = Zmod.unsigned (N.v50676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50676 s i)) at 1.
  unfold R.v50676, N.v50676.
  unfold R.v6, N.v6.
  rewrite ?node_9360.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50677 (s : N.State) (i : N.Inputs) :
  R.v50677 (state s) (inputs i) = Zmod.unsigned (N.v50677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50677 s i)) at 1.
  unfold R.v50677, N.v50677.
  rewrite ?node_50675.
  rewrite ?node_50676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50678 (s : N.State) (i : N.Inputs) :
  R.v50678 (state s) (inputs i) = Zmod.unsigned (N.v50678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50678 s i)) at 1.
  unfold R.v50678, N.v50678.
  rewrite ?node_50674.
  rewrite ?node_50677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50679 (s : N.State) (i : N.Inputs) :
  R.v50679 (state s) (inputs i) = Zmod.unsigned (N.v50679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50679 s i)) at 1.
  unfold R.v50679, N.v50679.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50680 (s : N.State) (i : N.Inputs) :
  R.v50680 (state s) (inputs i) = Zmod.unsigned (N.v50680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50680 s i)) at 1.
  unfold R.v50680, N.v50680.
  rewrite ?node_9332.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50681 (s : N.State) (i : N.Inputs) :
  R.v50681 (state s) (inputs i) = Zmod.unsigned (N.v50681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50681 s i)) at 1.
  unfold R.v50681, N.v50681.
  rewrite ?node_9328.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50682 (s : N.State) (i : N.Inputs) :
  R.v50682 (state s) (inputs i) = Zmod.unsigned (N.v50682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50682 s i)) at 1.
  unfold R.v50682, N.v50682.
  rewrite ?node_9314.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50683 (s : N.State) (i : N.Inputs) :
  R.v50683 (state s) (inputs i) = Zmod.unsigned (N.v50683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50683 s i)) at 1.
  unfold R.v50683, N.v50683.
  unfold R.v6, N.v6.
  rewrite ?node_9294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50684 (s : N.State) (i : N.Inputs) :
  R.v50684 (state s) (inputs i) = Zmod.unsigned (N.v50684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50684 s i)) at 1.
  unfold R.v50684, N.v50684.
  unfold R.v6, N.v6.
  rewrite ?node_9265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50685 (s : N.State) (i : N.Inputs) :
  R.v50685 (state s) (inputs i) = Zmod.unsigned (N.v50685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50685 s i)) at 1.
  unfold R.v50685, N.v50685.
  rewrite ?node_50683.
  rewrite ?node_50684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50686 (s : N.State) (i : N.Inputs) :
  R.v50686 (state s) (inputs i) = Zmod.unsigned (N.v50686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50686 s i)) at 1.
  unfold R.v50686, N.v50686.
  unfold R.v16484, N.v16484.
  rewrite ?node_50685.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50687 (s : N.State) (i : N.Inputs) :
  R.v50687 (state s) (inputs i) = Zmod.unsigned (N.v50687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50687 s i)) at 1.
  unfold R.v50687, N.v50687.
  rewrite ?node_50680.
  rewrite ?node_50681.
  rewrite ?node_50682.
  rewrite ?node_50686.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50688 (s : N.State) (i : N.Inputs) :
  R.v50688 (state s) (inputs i) = Zmod.unsigned (N.v50688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50688 s i)) at 1.
  unfold R.v50688, N.v50688.
  unfold R.v6, N.v6.
  rewrite ?node_50687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50689 (s : N.State) (i : N.Inputs) :
  R.v50689 (state s) (inputs i) = Zmod.unsigned (N.v50689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50689 s i)) at 1.
  unfold R.v50689, N.v50689.
  rewrite ?node_9333.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50690 (s : N.State) (i : N.Inputs) :
  R.v50690 (state s) (inputs i) = Zmod.unsigned (N.v50690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50690 s i)) at 1.
  unfold R.v50690, N.v50690.
  unfold R.v6, N.v6.
  rewrite ?node_9479.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50691 (s : N.State) (i : N.Inputs) :
  R.v50691 (state s) (inputs i) = Zmod.unsigned (N.v50691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50691 s i)) at 1.
  unfold R.v50691, N.v50691.
  unfold R.v6, N.v6.
  rewrite ?node_9501.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50692 (s : N.State) (i : N.Inputs) :
  R.v50692 (state s) (inputs i) = Zmod.unsigned (N.v50692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50692 s i)) at 1.
  unfold R.v50692, N.v50692.
  rewrite ?node_50689.
  rewrite ?node_50690.
  rewrite ?node_50691.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50693 (s : N.State) (i : N.Inputs) :
  R.v50693 (state s) (inputs i) = Zmod.unsigned (N.v50693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50693 s i)) at 1.
  unfold R.v50693, N.v50693.
  rewrite ?node_50688.
  rewrite ?node_50692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50694 (s : N.State) (i : N.Inputs) :
  R.v50694 (state s) (inputs i) = Zmod.unsigned (N.v50694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50694 s i)) at 1.
  unfold R.v50694, N.v50694.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50695 (s : N.State) (i : N.Inputs) :
  R.v50695 (state s) (inputs i) = Zmod.unsigned (N.v50695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50695 s i)) at 1.
  unfold R.v50695, N.v50695.
  rewrite ?node_9314.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50696 (s : N.State) (i : N.Inputs) :
  R.v50696 (state s) (inputs i) = Zmod.unsigned (N.v50696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50696 s i)) at 1.
  unfold R.v50696, N.v50696.
  unfold R.v6, N.v6.
  rewrite ?node_9294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50697 (s : N.State) (i : N.Inputs) :
  R.v50697 (state s) (inputs i) = Zmod.unsigned (N.v50697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50697 s i)) at 1.
  unfold R.v50697, N.v50697.
  unfold R.v6, N.v6.
  rewrite ?node_9265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50698 (s : N.State) (i : N.Inputs) :
  R.v50698 (state s) (inputs i) = Zmod.unsigned (N.v50698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50698 s i)) at 1.
  unfold R.v50698, N.v50698.
  rewrite ?node_50696.
  rewrite ?node_50697.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50699 (s : N.State) (i : N.Inputs) :
  R.v50699 (state s) (inputs i) = Zmod.unsigned (N.v50699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50699 s i)) at 1.
  unfold R.v50699, N.v50699.
  unfold R.v16484, N.v16484.
  rewrite ?node_50698.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50700 (s : N.State) (i : N.Inputs) :
  R.v50700 (state s) (inputs i) = Zmod.unsigned (N.v50700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50700 s i)) at 1.
  unfold R.v50700, N.v50700.
  rewrite ?node_50695.
  rewrite ?node_50699.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50701 (s : N.State) (i : N.Inputs) :
  R.v50701 (state s) (inputs i) = Zmod.unsigned (N.v50701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50701 s i)) at 1.
  unfold R.v50701, N.v50701.
  unfold R.v6, N.v6.
  rewrite ?node_50700.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50702 (s : N.State) (i : N.Inputs) :
  R.v50702 (state s) (inputs i) = Zmod.unsigned (N.v50702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50702 s i)) at 1.
  unfold R.v50702, N.v50702.
  rewrite ?node_9315.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50703 (s : N.State) (i : N.Inputs) :
  R.v50703 (state s) (inputs i) = Zmod.unsigned (N.v50703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50703 s i)) at 1.
  unfold R.v50703, N.v50703.
  unfold R.v6, N.v6.
  rewrite ?node_9479.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50704 (s : N.State) (i : N.Inputs) :
  R.v50704 (state s) (inputs i) = Zmod.unsigned (N.v50704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50704 s i)) at 1.
  unfold R.v50704, N.v50704.
  rewrite ?node_50702.
  rewrite ?node_50703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50705 (s : N.State) (i : N.Inputs) :
  R.v50705 (state s) (inputs i) = Zmod.unsigned (N.v50705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50705 s i)) at 1.
  unfold R.v50705, N.v50705.
  rewrite ?node_50701.
  rewrite ?node_50704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50706 (s : N.State) (i : N.Inputs) :
  R.v50706 (state s) (inputs i) = Zmod.unsigned (N.v50706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50706 s i)) at 1.
  unfold R.v50706, N.v50706.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50707 (s : N.State) (i : N.Inputs) :
  R.v50707 (state s) (inputs i) = Zmod.unsigned (N.v50707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50707 s i)) at 1.
  unfold R.v50707, N.v50707.
  rewrite ?node_9332.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50708 (s : N.State) (i : N.Inputs) :
  R.v50708 (state s) (inputs i) = Zmod.unsigned (N.v50708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50708 s i)) at 1.
  unfold R.v50708, N.v50708.
  unfold R.v6, N.v6.
  rewrite ?node_9328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50709 (s : N.State) (i : N.Inputs) :
  R.v50709 (state s) (inputs i) = Zmod.unsigned (N.v50709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50709 s i)) at 1.
  unfold R.v50709, N.v50709.
  unfold R.v6, N.v6.
  rewrite ?node_9315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50710 (s : N.State) (i : N.Inputs) :
  R.v50710 (state s) (inputs i) = Zmod.unsigned (N.v50710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50710 s i)) at 1.
  unfold R.v50710, N.v50710.
  rewrite ?node_50708.
  rewrite ?node_50709.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50711 (s : N.State) (i : N.Inputs) :
  R.v50711 (state s) (inputs i) = Zmod.unsigned (N.v50711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50711 s i)) at 1.
  unfold R.v50711, N.v50711.
  unfold R.v16484, N.v16484.
  rewrite ?node_50710.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50712 (s : N.State) (i : N.Inputs) :
  R.v50712 (state s) (inputs i) = Zmod.unsigned (N.v50712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50712 s i)) at 1.
  unfold R.v50712, N.v50712.
  rewrite ?node_50707.
  rewrite ?node_50711.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50713 (s : N.State) (i : N.Inputs) :
  R.v50713 (state s) (inputs i) = Zmod.unsigned (N.v50713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50713 s i)) at 1.
  unfold R.v50713, N.v50713.
  unfold R.v6, N.v6.
  rewrite ?node_50712.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50714 (s : N.State) (i : N.Inputs) :
  R.v50714 (state s) (inputs i) = Zmod.unsigned (N.v50714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50714 s i)) at 1.
  unfold R.v50714, N.v50714.
  rewrite ?node_9333.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50715 (s : N.State) (i : N.Inputs) :
  R.v50715 (state s) (inputs i) = Zmod.unsigned (N.v50715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50715 s i)) at 1.
  unfold R.v50715, N.v50715.
  unfold R.v6, N.v6.
  rewrite ?node_9501.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50716 (s : N.State) (i : N.Inputs) :
  R.v50716 (state s) (inputs i) = Zmod.unsigned (N.v50716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50716 s i)) at 1.
  unfold R.v50716, N.v50716.
  rewrite ?node_50714.
  rewrite ?node_50715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50717 (s : N.State) (i : N.Inputs) :
  R.v50717 (state s) (inputs i) = Zmod.unsigned (N.v50717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50717 s i)) at 1.
  unfold R.v50717, N.v50717.
  rewrite ?node_50713.
  rewrite ?node_50716.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50718 (s : N.State) (i : N.Inputs) :
  R.v50718 (state s) (inputs i) = Zmod.unsigned (N.v50718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50718 s i)) at 1.
  unfold R.v50718, N.v50718.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50719 (s : N.State) (i : N.Inputs) :
  R.v50719 (state s) (inputs i) = Zmod.unsigned (N.v50719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50719 s i)) at 1.
  unfold R.v50719, N.v50719.
  rewrite ?node_9351.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50720 (s : N.State) (i : N.Inputs) :
  R.v50720 (state s) (inputs i) = Zmod.unsigned (N.v50720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50720 s i)) at 1.
  unfold R.v50720, N.v50720.
  rewrite ?node_9347.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50721 (s : N.State) (i : N.Inputs) :
  R.v50721 (state s) (inputs i) = Zmod.unsigned (N.v50721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50721 s i)) at 1.
  unfold R.v50721, N.v50721.
  rewrite ?node_9343.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50722 (s : N.State) (i : N.Inputs) :
  R.v50722 (state s) (inputs i) = Zmod.unsigned (N.v50722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50722 s i)) at 1.
  unfold R.v50722, N.v50722.
  unfold R.v6, N.v6.
  rewrite ?node_9339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50723 (s : N.State) (i : N.Inputs) :
  R.v50723 (state s) (inputs i) = Zmod.unsigned (N.v50723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50723 s i)) at 1.
  unfold R.v50723, N.v50723.
  unfold R.v6, N.v6.
  rewrite ?node_9336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50724 (s : N.State) (i : N.Inputs) :
  R.v50724 (state s) (inputs i) = Zmod.unsigned (N.v50724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50724 s i)) at 1.
  unfold R.v50724, N.v50724.
  rewrite ?node_50722.
  rewrite ?node_50723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50725 (s : N.State) (i : N.Inputs) :
  R.v50725 (state s) (inputs i) = Zmod.unsigned (N.v50725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50725 s i)) at 1.
  unfold R.v50725, N.v50725.
  unfold R.v16484, N.v16484.
  rewrite ?node_50724.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50726 (s : N.State) (i : N.Inputs) :
  R.v50726 (state s) (inputs i) = Zmod.unsigned (N.v50726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50726 s i)) at 1.
  unfold R.v50726, N.v50726.
  rewrite ?node_50719.
  rewrite ?node_50720.
  rewrite ?node_50721.
  rewrite ?node_50725.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50727 (s : N.State) (i : N.Inputs) :
  R.v50727 (state s) (inputs i) = Zmod.unsigned (N.v50727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50727 s i)) at 1.
  unfold R.v50727, N.v50727.
  unfold R.v6, N.v6.
  rewrite ?node_50726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50728 (s : N.State) (i : N.Inputs) :
  R.v50728 (state s) (inputs i) = Zmod.unsigned (N.v50728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50728 s i)) at 1.
  unfold R.v50728, N.v50728.
  rewrite ?node_9352.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50729 (s : N.State) (i : N.Inputs) :
  R.v50729 (state s) (inputs i) = Zmod.unsigned (N.v50729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50729 s i)) at 1.
  unfold R.v50729, N.v50729.
  unfold R.v6, N.v6.
  rewrite ?node_9496.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50730 (s : N.State) (i : N.Inputs) :
  R.v50730 (state s) (inputs i) = Zmod.unsigned (N.v50730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50730 s i)) at 1.
  unfold R.v50730, N.v50730.
  unfold R.v6, N.v6.
  rewrite ?node_9505.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50731 (s : N.State) (i : N.Inputs) :
  R.v50731 (state s) (inputs i) = Zmod.unsigned (N.v50731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50731 s i)) at 1.
  unfold R.v50731, N.v50731.
  rewrite ?node_50728.
  rewrite ?node_50729.
  rewrite ?node_50730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50732 (s : N.State) (i : N.Inputs) :
  R.v50732 (state s) (inputs i) = Zmod.unsigned (N.v50732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50732 s i)) at 1.
  unfold R.v50732, N.v50732.
  rewrite ?node_50727.
  rewrite ?node_50731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50733 (s : N.State) (i : N.Inputs) :
  R.v50733 (state s) (inputs i) = Zmod.unsigned (N.v50733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50733 s i)) at 1.
  unfold R.v50733, N.v50733.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50734 (s : N.State) (i : N.Inputs) :
  R.v50734 (state s) (inputs i) = Zmod.unsigned (N.v50734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50734 s i)) at 1.
  unfold R.v50734, N.v50734.
  rewrite ?node_9343.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50735 (s : N.State) (i : N.Inputs) :
  R.v50735 (state s) (inputs i) = Zmod.unsigned (N.v50735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50735 s i)) at 1.
  unfold R.v50735, N.v50735.
  unfold R.v6, N.v6.
  rewrite ?node_9339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50736 (s : N.State) (i : N.Inputs) :
  R.v50736 (state s) (inputs i) = Zmod.unsigned (N.v50736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50736 s i)) at 1.
  unfold R.v50736, N.v50736.
  unfold R.v6, N.v6.
  rewrite ?node_9336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50737 (s : N.State) (i : N.Inputs) :
  R.v50737 (state s) (inputs i) = Zmod.unsigned (N.v50737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50737 s i)) at 1.
  unfold R.v50737, N.v50737.
  rewrite ?node_50735.
  rewrite ?node_50736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50738 (s : N.State) (i : N.Inputs) :
  R.v50738 (state s) (inputs i) = Zmod.unsigned (N.v50738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50738 s i)) at 1.
  unfold R.v50738, N.v50738.
  unfold R.v16484, N.v16484.
  rewrite ?node_50737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50739 (s : N.State) (i : N.Inputs) :
  R.v50739 (state s) (inputs i) = Zmod.unsigned (N.v50739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50739 s i)) at 1.
  unfold R.v50739, N.v50739.
  rewrite ?node_50734.
  rewrite ?node_50738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50740 (s : N.State) (i : N.Inputs) :
  R.v50740 (state s) (inputs i) = Zmod.unsigned (N.v50740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50740 s i)) at 1.
  unfold R.v50740, N.v50740.
  unfold R.v6, N.v6.
  rewrite ?node_50739.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50741 (s : N.State) (i : N.Inputs) :
  R.v50741 (state s) (inputs i) = Zmod.unsigned (N.v50741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50741 s i)) at 1.
  unfold R.v50741, N.v50741.
  rewrite ?node_9344.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50742 (s : N.State) (i : N.Inputs) :
  R.v50742 (state s) (inputs i) = Zmod.unsigned (N.v50742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50742 s i)) at 1.
  unfold R.v50742, N.v50742.
  unfold R.v6, N.v6.
  rewrite ?node_9496.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50743 (s : N.State) (i : N.Inputs) :
  R.v50743 (state s) (inputs i) = Zmod.unsigned (N.v50743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50743 s i)) at 1.
  unfold R.v50743, N.v50743.
  rewrite ?node_50741.
  rewrite ?node_50742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50744 (s : N.State) (i : N.Inputs) :
  R.v50744 (state s) (inputs i) = Zmod.unsigned (N.v50744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50744 s i)) at 1.
  unfold R.v50744, N.v50744.
  rewrite ?node_50740.
  rewrite ?node_50743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50745 (s : N.State) (i : N.Inputs) :
  R.v50745 (state s) (inputs i) = Zmod.unsigned (N.v50745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50745 s i)) at 1.
  unfold R.v50745, N.v50745.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50746 (s : N.State) (i : N.Inputs) :
  R.v50746 (state s) (inputs i) = Zmod.unsigned (N.v50746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50746 s i)) at 1.
  unfold R.v50746, N.v50746.
  rewrite ?node_9351.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50747 (s : N.State) (i : N.Inputs) :
  R.v50747 (state s) (inputs i) = Zmod.unsigned (N.v50747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50747 s i)) at 1.
  unfold R.v50747, N.v50747.
  unfold R.v6, N.v6.
  rewrite ?node_9347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50748 (s : N.State) (i : N.Inputs) :
  R.v50748 (state s) (inputs i) = Zmod.unsigned (N.v50748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50748 s i)) at 1.
  unfold R.v50748, N.v50748.
  unfold R.v6, N.v6.
  rewrite ?node_9344.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50749 (s : N.State) (i : N.Inputs) :
  R.v50749 (state s) (inputs i) = Zmod.unsigned (N.v50749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50749 s i)) at 1.
  unfold R.v50749, N.v50749.
  rewrite ?node_50747.
  rewrite ?node_50748.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50750 (s : N.State) (i : N.Inputs) :
  R.v50750 (state s) (inputs i) = Zmod.unsigned (N.v50750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50750 s i)) at 1.
  unfold R.v50750, N.v50750.
  unfold R.v16484, N.v16484.
  rewrite ?node_50749.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50751 (s : N.State) (i : N.Inputs) :
  R.v50751 (state s) (inputs i) = Zmod.unsigned (N.v50751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50751 s i)) at 1.
  unfold R.v50751, N.v50751.
  rewrite ?node_50746.
  rewrite ?node_50750.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50752 (s : N.State) (i : N.Inputs) :
  R.v50752 (state s) (inputs i) = Zmod.unsigned (N.v50752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50752 s i)) at 1.
  unfold R.v50752, N.v50752.
  unfold R.v6, N.v6.
  rewrite ?node_50751.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50753 (s : N.State) (i : N.Inputs) :
  R.v50753 (state s) (inputs i) = Zmod.unsigned (N.v50753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50753 s i)) at 1.
  unfold R.v50753, N.v50753.
  rewrite ?node_9352.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50754 (s : N.State) (i : N.Inputs) :
  R.v50754 (state s) (inputs i) = Zmod.unsigned (N.v50754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50754 s i)) at 1.
  unfold R.v50754, N.v50754.
  unfold R.v6, N.v6.
  rewrite ?node_9505.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50755 (s : N.State) (i : N.Inputs) :
  R.v50755 (state s) (inputs i) = Zmod.unsigned (N.v50755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50755 s i)) at 1.
  unfold R.v50755, N.v50755.
  rewrite ?node_50753.
  rewrite ?node_50754.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50756 (s : N.State) (i : N.Inputs) :
  R.v50756 (state s) (inputs i) = Zmod.unsigned (N.v50756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50756 s i)) at 1.
  unfold R.v50756, N.v50756.
  rewrite ?node_50752.
  rewrite ?node_50755.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50757 (s : N.State) (i : N.Inputs) :
  R.v50757 (state s) (inputs i) = Zmod.unsigned (N.v50757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50757 s i)) at 1.
  unfold R.v50757, N.v50757.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50758 (s : N.State) (i : N.Inputs) :
  R.v50758 (state s) (inputs i) = Zmod.unsigned (N.v50758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50758 s i)) at 1.
  unfold R.v50758, N.v50758.
  rewrite ?node_9479.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50759 (s : N.State) (i : N.Inputs) :
  R.v50759 (state s) (inputs i) = Zmod.unsigned (N.v50759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50759 s i)) at 1.
  unfold R.v50759, N.v50759.
  rewrite ?node_9475.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50760 (s : N.State) (i : N.Inputs) :
  R.v50760 (state s) (inputs i) = Zmod.unsigned (N.v50760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50760 s i)) at 1.
  unfold R.v50760, N.v50760.
  rewrite ?node_9457.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50761 (s : N.State) (i : N.Inputs) :
  R.v50761 (state s) (inputs i) = Zmod.unsigned (N.v50761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50761 s i)) at 1.
  unfold R.v50761, N.v50761.
  unfold R.v6, N.v6.
  rewrite ?node_9437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50762 (s : N.State) (i : N.Inputs) :
  R.v50762 (state s) (inputs i) = Zmod.unsigned (N.v50762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50762 s i)) at 1.
  unfold R.v50762, N.v50762.
  unfold R.v6, N.v6.
  rewrite ?node_9407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50763 (s : N.State) (i : N.Inputs) :
  R.v50763 (state s) (inputs i) = Zmod.unsigned (N.v50763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50763 s i)) at 1.
  unfold R.v50763, N.v50763.
  rewrite ?node_50761.
  rewrite ?node_50762.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50764 (s : N.State) (i : N.Inputs) :
  R.v50764 (state s) (inputs i) = Zmod.unsigned (N.v50764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50764 s i)) at 1.
  unfold R.v50764, N.v50764.
  unfold R.v16484, N.v16484.
  rewrite ?node_50763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50765 (s : N.State) (i : N.Inputs) :
  R.v50765 (state s) (inputs i) = Zmod.unsigned (N.v50765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50765 s i)) at 1.
  unfold R.v50765, N.v50765.
  rewrite ?node_50758.
  rewrite ?node_50759.
  rewrite ?node_50760.
  rewrite ?node_50764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50766 (s : N.State) (i : N.Inputs) :
  R.v50766 (state s) (inputs i) = Zmod.unsigned (N.v50766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50766 s i)) at 1.
  unfold R.v50766, N.v50766.
  unfold R.v6, N.v6.
  rewrite ?node_50765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50767 (s : N.State) (i : N.Inputs) :
  R.v50767 (state s) (inputs i) = Zmod.unsigned (N.v50767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50767 s i)) at 1.
  unfold R.v50767, N.v50767.
  rewrite ?node_9480.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50768 (s : N.State) (i : N.Inputs) :
  R.v50768 (state s) (inputs i) = Zmod.unsigned (N.v50768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50768 s i)) at 1.
  unfold R.v50768, N.v50768.
  unfold R.v6, N.v6.
  rewrite ?node_9626.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50769 (s : N.State) (i : N.Inputs) :
  R.v50769 (state s) (inputs i) = Zmod.unsigned (N.v50769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50769 s i)) at 1.
  unfold R.v50769, N.v50769.
  unfold R.v6, N.v6.
  rewrite ?node_9650.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50770 (s : N.State) (i : N.Inputs) :
  R.v50770 (state s) (inputs i) = Zmod.unsigned (N.v50770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50770 s i)) at 1.
  unfold R.v50770, N.v50770.
  rewrite ?node_50767.
  rewrite ?node_50768.
  rewrite ?node_50769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50771 (s : N.State) (i : N.Inputs) :
  R.v50771 (state s) (inputs i) = Zmod.unsigned (N.v50771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50771 s i)) at 1.
  unfold R.v50771, N.v50771.
  rewrite ?node_50766.
  rewrite ?node_50770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50772 (s : N.State) (i : N.Inputs) :
  R.v50772 (state s) (inputs i) = Zmod.unsigned (N.v50772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50772 s i)) at 1.
  unfold R.v50772, N.v50772.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50773 (s : N.State) (i : N.Inputs) :
  R.v50773 (state s) (inputs i) = Zmod.unsigned (N.v50773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50773 s i)) at 1.
  unfold R.v50773, N.v50773.
  rewrite ?node_9457.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50774 (s : N.State) (i : N.Inputs) :
  R.v50774 (state s) (inputs i) = Zmod.unsigned (N.v50774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50774 s i)) at 1.
  unfold R.v50774, N.v50774.
  unfold R.v6, N.v6.
  rewrite ?node_9437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50775 (s : N.State) (i : N.Inputs) :
  R.v50775 (state s) (inputs i) = Zmod.unsigned (N.v50775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50775 s i)) at 1.
  unfold R.v50775, N.v50775.
  unfold R.v6, N.v6.
  rewrite ?node_9407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50776 (s : N.State) (i : N.Inputs) :
  R.v50776 (state s) (inputs i) = Zmod.unsigned (N.v50776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50776 s i)) at 1.
  unfold R.v50776, N.v50776.
  rewrite ?node_50774.
  rewrite ?node_50775.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50777 (s : N.State) (i : N.Inputs) :
  R.v50777 (state s) (inputs i) = Zmod.unsigned (N.v50777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50777 s i)) at 1.
  unfold R.v50777, N.v50777.
  unfold R.v16484, N.v16484.
  rewrite ?node_50776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50778 (s : N.State) (i : N.Inputs) :
  R.v50778 (state s) (inputs i) = Zmod.unsigned (N.v50778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50778 s i)) at 1.
  unfold R.v50778, N.v50778.
  rewrite ?node_50773.
  rewrite ?node_50777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50779 (s : N.State) (i : N.Inputs) :
  R.v50779 (state s) (inputs i) = Zmod.unsigned (N.v50779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50779 s i)) at 1.
  unfold R.v50779, N.v50779.
  unfold R.v6, N.v6.
  rewrite ?node_50778.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50780 (s : N.State) (i : N.Inputs) :
  R.v50780 (state s) (inputs i) = Zmod.unsigned (N.v50780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50780 s i)) at 1.
  unfold R.v50780, N.v50780.
  rewrite ?node_9458.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50781 (s : N.State) (i : N.Inputs) :
  R.v50781 (state s) (inputs i) = Zmod.unsigned (N.v50781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50781 s i)) at 1.
  unfold R.v50781, N.v50781.
  unfold R.v6, N.v6.
  rewrite ?node_9626.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50782 (s : N.State) (i : N.Inputs) :
  R.v50782 (state s) (inputs i) = Zmod.unsigned (N.v50782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50782 s i)) at 1.
  unfold R.v50782, N.v50782.
  rewrite ?node_50780.
  rewrite ?node_50781.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50783 (s : N.State) (i : N.Inputs) :
  R.v50783 (state s) (inputs i) = Zmod.unsigned (N.v50783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50783 s i)) at 1.
  unfold R.v50783, N.v50783.
  rewrite ?node_50779.
  rewrite ?node_50782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50784 (s : N.State) (i : N.Inputs) :
  R.v50784 (state s) (inputs i) = Zmod.unsigned (N.v50784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50784 s i)) at 1.
  unfold R.v50784, N.v50784.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50785 (s : N.State) (i : N.Inputs) :
  R.v50785 (state s) (inputs i) = Zmod.unsigned (N.v50785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50785 s i)) at 1.
  unfold R.v50785, N.v50785.
  rewrite ?node_9479.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50786 (s : N.State) (i : N.Inputs) :
  R.v50786 (state s) (inputs i) = Zmod.unsigned (N.v50786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50786 s i)) at 1.
  unfold R.v50786, N.v50786.
  unfold R.v6, N.v6.
  rewrite ?node_9475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50787 (s : N.State) (i : N.Inputs) :
  R.v50787 (state s) (inputs i) = Zmod.unsigned (N.v50787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50787 s i)) at 1.
  unfold R.v50787, N.v50787.
  unfold R.v6, N.v6.
  rewrite ?node_9458.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50788 (s : N.State) (i : N.Inputs) :
  R.v50788 (state s) (inputs i) = Zmod.unsigned (N.v50788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50788 s i)) at 1.
  unfold R.v50788, N.v50788.
  rewrite ?node_50786.
  rewrite ?node_50787.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50789 (s : N.State) (i : N.Inputs) :
  R.v50789 (state s) (inputs i) = Zmod.unsigned (N.v50789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50789 s i)) at 1.
  unfold R.v50789, N.v50789.
  unfold R.v16484, N.v16484.
  rewrite ?node_50788.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50790 (s : N.State) (i : N.Inputs) :
  R.v50790 (state s) (inputs i) = Zmod.unsigned (N.v50790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50790 s i)) at 1.
  unfold R.v50790, N.v50790.
  rewrite ?node_50785.
  rewrite ?node_50789.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50791 (s : N.State) (i : N.Inputs) :
  R.v50791 (state s) (inputs i) = Zmod.unsigned (N.v50791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50791 s i)) at 1.
  unfold R.v50791, N.v50791.
  unfold R.v6, N.v6.
  rewrite ?node_50790.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50792 (s : N.State) (i : N.Inputs) :
  R.v50792 (state s) (inputs i) = Zmod.unsigned (N.v50792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50792 s i)) at 1.
  unfold R.v50792, N.v50792.
  rewrite ?node_9480.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50793 (s : N.State) (i : N.Inputs) :
  R.v50793 (state s) (inputs i) = Zmod.unsigned (N.v50793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50793 s i)) at 1.
  unfold R.v50793, N.v50793.
  unfold R.v6, N.v6.
  rewrite ?node_9650.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50794 (s : N.State) (i : N.Inputs) :
  R.v50794 (state s) (inputs i) = Zmod.unsigned (N.v50794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50794 s i)) at 1.
  unfold R.v50794, N.v50794.
  rewrite ?node_50792.
  rewrite ?node_50793.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50795 (s : N.State) (i : N.Inputs) :
  R.v50795 (state s) (inputs i) = Zmod.unsigned (N.v50795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50795 s i)) at 1.
  unfold R.v50795, N.v50795.
  rewrite ?node_50791.
  rewrite ?node_50794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50796 (s : N.State) (i : N.Inputs) :
  R.v50796 (state s) (inputs i) = Zmod.unsigned (N.v50796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50796 s i)) at 1.
  unfold R.v50796, N.v50796.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50797 (s : N.State) (i : N.Inputs) :
  R.v50797 (state s) (inputs i) = Zmod.unsigned (N.v50797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50797 s i)) at 1.
  unfold R.v50797, N.v50797.
  rewrite ?node_9496.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50798 (s : N.State) (i : N.Inputs) :
  R.v50798 (state s) (inputs i) = Zmod.unsigned (N.v50798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50798 s i)) at 1.
  unfold R.v50798, N.v50798.
  rewrite ?node_9492.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50799 (s : N.State) (i : N.Inputs) :
  R.v50799 (state s) (inputs i) = Zmod.unsigned (N.v50799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50799 s i)) at 1.
  unfold R.v50799, N.v50799.
  rewrite ?node_9490.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50800 (s : N.State) (i : N.Inputs) :
  R.v50800 (state s) (inputs i) = Zmod.unsigned (N.v50800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50800 s i)) at 1.
  unfold R.v50800, N.v50800.
  unfold R.v6, N.v6.
  rewrite ?node_9486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50801 (s : N.State) (i : N.Inputs) :
  R.v50801 (state s) (inputs i) = Zmod.unsigned (N.v50801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50801 s i)) at 1.
  unfold R.v50801, N.v50801.
  unfold R.v6, N.v6.
  rewrite ?node_9483.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50802 (s : N.State) (i : N.Inputs) :
  R.v50802 (state s) (inputs i) = Zmod.unsigned (N.v50802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50802 s i)) at 1.
  unfold R.v50802, N.v50802.
  rewrite ?node_50800.
  rewrite ?node_50801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50803 (s : N.State) (i : N.Inputs) :
  R.v50803 (state s) (inputs i) = Zmod.unsigned (N.v50803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50803 s i)) at 1.
  unfold R.v50803, N.v50803.
  unfold R.v16484, N.v16484.
  rewrite ?node_50802.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50804 (s : N.State) (i : N.Inputs) :
  R.v50804 (state s) (inputs i) = Zmod.unsigned (N.v50804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50804 s i)) at 1.
  unfold R.v50804, N.v50804.
  rewrite ?node_50797.
  rewrite ?node_50798.
  rewrite ?node_50799.
  rewrite ?node_50803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50805 (s : N.State) (i : N.Inputs) :
  R.v50805 (state s) (inputs i) = Zmod.unsigned (N.v50805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50805 s i)) at 1.
  unfold R.v50805, N.v50805.
  unfold R.v6, N.v6.
  rewrite ?node_50804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50806 (s : N.State) (i : N.Inputs) :
  R.v50806 (state s) (inputs i) = Zmod.unsigned (N.v50806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50806 s i)) at 1.
  unfold R.v50806, N.v50806.
  rewrite ?node_9497.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50807 (s : N.State) (i : N.Inputs) :
  R.v50807 (state s) (inputs i) = Zmod.unsigned (N.v50807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50807 s i)) at 1.
  unfold R.v50807, N.v50807.
  unfold R.v6, N.v6.
  rewrite ?node_9645.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50808 (s : N.State) (i : N.Inputs) :
  R.v50808 (state s) (inputs i) = Zmod.unsigned (N.v50808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50808 s i)) at 1.
  unfold R.v50808, N.v50808.
  unfold R.v6, N.v6.
  rewrite ?node_9654.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50809 (s : N.State) (i : N.Inputs) :
  R.v50809 (state s) (inputs i) = Zmod.unsigned (N.v50809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50809 s i)) at 1.
  unfold R.v50809, N.v50809.
  rewrite ?node_50806.
  rewrite ?node_50807.
  rewrite ?node_50808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50810 (s : N.State) (i : N.Inputs) :
  R.v50810 (state s) (inputs i) = Zmod.unsigned (N.v50810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50810 s i)) at 1.
  unfold R.v50810, N.v50810.
  rewrite ?node_50805.
  rewrite ?node_50809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50811 (s : N.State) (i : N.Inputs) :
  R.v50811 (state s) (inputs i) = Zmod.unsigned (N.v50811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50811 s i)) at 1.
  unfold R.v50811, N.v50811.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50812 (s : N.State) (i : N.Inputs) :
  R.v50812 (state s) (inputs i) = Zmod.unsigned (N.v50812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50812 s i)) at 1.
  unfold R.v50812, N.v50812.
  rewrite ?node_9490.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50813 (s : N.State) (i : N.Inputs) :
  R.v50813 (state s) (inputs i) = Zmod.unsigned (N.v50813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50813 s i)) at 1.
  unfold R.v50813, N.v50813.
  unfold R.v6, N.v6.
  rewrite ?node_9486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50814 (s : N.State) (i : N.Inputs) :
  R.v50814 (state s) (inputs i) = Zmod.unsigned (N.v50814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50814 s i)) at 1.
  unfold R.v50814, N.v50814.
  unfold R.v6, N.v6.
  rewrite ?node_9483.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50815 (s : N.State) (i : N.Inputs) :
  R.v50815 (state s) (inputs i) = Zmod.unsigned (N.v50815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50815 s i)) at 1.
  unfold R.v50815, N.v50815.
  rewrite ?node_50813.
  rewrite ?node_50814.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50816 (s : N.State) (i : N.Inputs) :
  R.v50816 (state s) (inputs i) = Zmod.unsigned (N.v50816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50816 s i)) at 1.
  unfold R.v50816, N.v50816.
  unfold R.v16484, N.v16484.
  rewrite ?node_50815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50817 (s : N.State) (i : N.Inputs) :
  R.v50817 (state s) (inputs i) = Zmod.unsigned (N.v50817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50817 s i)) at 1.
  unfold R.v50817, N.v50817.
  rewrite ?node_50812.
  rewrite ?node_50816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50818 (s : N.State) (i : N.Inputs) :
  R.v50818 (state s) (inputs i) = Zmod.unsigned (N.v50818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50818 s i)) at 1.
  unfold R.v50818, N.v50818.
  unfold R.v6, N.v6.
  rewrite ?node_50817.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50819 (s : N.State) (i : N.Inputs) :
  R.v50819 (state s) (inputs i) = Zmod.unsigned (N.v50819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50819 s i)) at 1.
  unfold R.v50819, N.v50819.
  rewrite ?node_9491.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50820 (s : N.State) (i : N.Inputs) :
  R.v50820 (state s) (inputs i) = Zmod.unsigned (N.v50820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50820 s i)) at 1.
  unfold R.v50820, N.v50820.
  unfold R.v6, N.v6.
  rewrite ?node_9645.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50821 (s : N.State) (i : N.Inputs) :
  R.v50821 (state s) (inputs i) = Zmod.unsigned (N.v50821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50821 s i)) at 1.
  unfold R.v50821, N.v50821.
  rewrite ?node_50819.
  rewrite ?node_50820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50822 (s : N.State) (i : N.Inputs) :
  R.v50822 (state s) (inputs i) = Zmod.unsigned (N.v50822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50822 s i)) at 1.
  unfold R.v50822, N.v50822.
  rewrite ?node_50818.
  rewrite ?node_50821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50823 (s : N.State) (i : N.Inputs) :
  R.v50823 (state s) (inputs i) = Zmod.unsigned (N.v50823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50823 s i)) at 1.
  unfold R.v50823, N.v50823.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50824 (s : N.State) (i : N.Inputs) :
  R.v50824 (state s) (inputs i) = Zmod.unsigned (N.v50824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50824 s i)) at 1.
  unfold R.v50824, N.v50824.
  rewrite ?node_9496.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50825 (s : N.State) (i : N.Inputs) :
  R.v50825 (state s) (inputs i) = Zmod.unsigned (N.v50825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50825 s i)) at 1.
  unfold R.v50825, N.v50825.
  unfold R.v6, N.v6.
  rewrite ?node_9492.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50826 (s : N.State) (i : N.Inputs) :
  R.v50826 (state s) (inputs i) = Zmod.unsigned (N.v50826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50826 s i)) at 1.
  unfold R.v50826, N.v50826.
  unfold R.v6, N.v6.
  rewrite ?node_9491.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50827 (s : N.State) (i : N.Inputs) :
  R.v50827 (state s) (inputs i) = Zmod.unsigned (N.v50827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50827 s i)) at 1.
  unfold R.v50827, N.v50827.
  rewrite ?node_50825.
  rewrite ?node_50826.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50828 (s : N.State) (i : N.Inputs) :
  R.v50828 (state s) (inputs i) = Zmod.unsigned (N.v50828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50828 s i)) at 1.
  unfold R.v50828, N.v50828.
  unfold R.v16484, N.v16484.
  rewrite ?node_50827.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50829 (s : N.State) (i : N.Inputs) :
  R.v50829 (state s) (inputs i) = Zmod.unsigned (N.v50829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50829 s i)) at 1.
  unfold R.v50829, N.v50829.
  rewrite ?node_50824.
  rewrite ?node_50828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50830 (s : N.State) (i : N.Inputs) :
  R.v50830 (state s) (inputs i) = Zmod.unsigned (N.v50830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50830 s i)) at 1.
  unfold R.v50830, N.v50830.
  unfold R.v6, N.v6.
  rewrite ?node_50829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50831 (s : N.State) (i : N.Inputs) :
  R.v50831 (state s) (inputs i) = Zmod.unsigned (N.v50831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50831 s i)) at 1.
  unfold R.v50831, N.v50831.
  rewrite ?node_9497.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50832 (s : N.State) (i : N.Inputs) :
  R.v50832 (state s) (inputs i) = Zmod.unsigned (N.v50832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50832 s i)) at 1.
  unfold R.v50832, N.v50832.
  unfold R.v6, N.v6.
  rewrite ?node_9654.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50833 (s : N.State) (i : N.Inputs) :
  R.v50833 (state s) (inputs i) = Zmod.unsigned (N.v50833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50833 s i)) at 1.
  unfold R.v50833, N.v50833.
  rewrite ?node_50831.
  rewrite ?node_50832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50834 (s : N.State) (i : N.Inputs) :
  R.v50834 (state s) (inputs i) = Zmod.unsigned (N.v50834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50834 s i)) at 1.
  unfold R.v50834, N.v50834.
  rewrite ?node_50830.
  rewrite ?node_50833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50835 (s : N.State) (i : N.Inputs) :
  R.v50835 (state s) (inputs i) = Zmod.unsigned (N.v50835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50835 s i)) at 1.
  unfold R.v50835, N.v50835.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50836 (s : N.State) (i : N.Inputs) :
  R.v50836 (state s) (inputs i) = Zmod.unsigned (N.v50836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50836 s i)) at 1.
  unfold R.v50836, N.v50836.
  rewrite ?node_9626.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50837 (s : N.State) (i : N.Inputs) :
  R.v50837 (state s) (inputs i) = Zmod.unsigned (N.v50837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50837 s i)) at 1.
  unfold R.v50837, N.v50837.
  rewrite ?node_9622.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50838 (s : N.State) (i : N.Inputs) :
  R.v50838 (state s) (inputs i) = Zmod.unsigned (N.v50838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50838 s i)) at 1.
  unfold R.v50838, N.v50838.
  rewrite ?node_9602.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50839 (s : N.State) (i : N.Inputs) :
  R.v50839 (state s) (inputs i) = Zmod.unsigned (N.v50839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50839 s i)) at 1.
  unfold R.v50839, N.v50839.
  unfold R.v6, N.v6.
  rewrite ?node_9582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50840 (s : N.State) (i : N.Inputs) :
  R.v50840 (state s) (inputs i) = Zmod.unsigned (N.v50840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50840 s i)) at 1.
  unfold R.v50840, N.v50840.
  unfold R.v6, N.v6.
  rewrite ?node_9552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50841 (s : N.State) (i : N.Inputs) :
  R.v50841 (state s) (inputs i) = Zmod.unsigned (N.v50841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50841 s i)) at 1.
  unfold R.v50841, N.v50841.
  rewrite ?node_50839.
  rewrite ?node_50840.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50842 (s : N.State) (i : N.Inputs) :
  R.v50842 (state s) (inputs i) = Zmod.unsigned (N.v50842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50842 s i)) at 1.
  unfold R.v50842, N.v50842.
  unfold R.v16484, N.v16484.
  rewrite ?node_50841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50843 (s : N.State) (i : N.Inputs) :
  R.v50843 (state s) (inputs i) = Zmod.unsigned (N.v50843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50843 s i)) at 1.
  unfold R.v50843, N.v50843.
  rewrite ?node_50836.
  rewrite ?node_50837.
  rewrite ?node_50838.
  rewrite ?node_50842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50844 (s : N.State) (i : N.Inputs) :
  R.v50844 (state s) (inputs i) = Zmod.unsigned (N.v50844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50844 s i)) at 1.
  unfold R.v50844, N.v50844.
  unfold R.v6, N.v6.
  rewrite ?node_50843.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50845 (s : N.State) (i : N.Inputs) :
  R.v50845 (state s) (inputs i) = Zmod.unsigned (N.v50845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50845 s i)) at 1.
  unfold R.v50845, N.v50845.
  rewrite ?node_9627.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50846 (s : N.State) (i : N.Inputs) :
  R.v50846 (state s) (inputs i) = Zmod.unsigned (N.v50846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50846 s i)) at 1.
  unfold R.v50846, N.v50846.
  unfold R.v6, N.v6.
  rewrite ?node_9776.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50847 (s : N.State) (i : N.Inputs) :
  R.v50847 (state s) (inputs i) = Zmod.unsigned (N.v50847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50847 s i)) at 1.
  unfold R.v50847, N.v50847.
  unfold R.v6, N.v6.
  rewrite ?node_9800.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50848 (s : N.State) (i : N.Inputs) :
  R.v50848 (state s) (inputs i) = Zmod.unsigned (N.v50848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50848 s i)) at 1.
  unfold R.v50848, N.v50848.
  rewrite ?node_50845.
  rewrite ?node_50846.
  rewrite ?node_50847.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50849 (s : N.State) (i : N.Inputs) :
  R.v50849 (state s) (inputs i) = Zmod.unsigned (N.v50849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50849 s i)) at 1.
  unfold R.v50849, N.v50849.
  rewrite ?node_50844.
  rewrite ?node_50848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50850 (s : N.State) (i : N.Inputs) :
  R.v50850 (state s) (inputs i) = Zmod.unsigned (N.v50850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50850 s i)) at 1.
  unfold R.v50850, N.v50850.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50851 (s : N.State) (i : N.Inputs) :
  R.v50851 (state s) (inputs i) = Zmod.unsigned (N.v50851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50851 s i)) at 1.
  unfold R.v50851, N.v50851.
  rewrite ?node_9602.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50852 (s : N.State) (i : N.Inputs) :
  R.v50852 (state s) (inputs i) = Zmod.unsigned (N.v50852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50852 s i)) at 1.
  unfold R.v50852, N.v50852.
  unfold R.v6, N.v6.
  rewrite ?node_9582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50853 (s : N.State) (i : N.Inputs) :
  R.v50853 (state s) (inputs i) = Zmod.unsigned (N.v50853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50853 s i)) at 1.
  unfold R.v50853, N.v50853.
  unfold R.v6, N.v6.
  rewrite ?node_9552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50854 (s : N.State) (i : N.Inputs) :
  R.v50854 (state s) (inputs i) = Zmod.unsigned (N.v50854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50854 s i)) at 1.
  unfold R.v50854, N.v50854.
  rewrite ?node_50852.
  rewrite ?node_50853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50855 (s : N.State) (i : N.Inputs) :
  R.v50855 (state s) (inputs i) = Zmod.unsigned (N.v50855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50855 s i)) at 1.
  unfold R.v50855, N.v50855.
  unfold R.v16484, N.v16484.
  rewrite ?node_50854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50856 (s : N.State) (i : N.Inputs) :
  R.v50856 (state s) (inputs i) = Zmod.unsigned (N.v50856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50856 s i)) at 1.
  unfold R.v50856, N.v50856.
  rewrite ?node_50851.
  rewrite ?node_50855.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50857 (s : N.State) (i : N.Inputs) :
  R.v50857 (state s) (inputs i) = Zmod.unsigned (N.v50857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50857 s i)) at 1.
  unfold R.v50857, N.v50857.
  unfold R.v6, N.v6.
  rewrite ?node_50856.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50858 (s : N.State) (i : N.Inputs) :
  R.v50858 (state s) (inputs i) = Zmod.unsigned (N.v50858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50858 s i)) at 1.
  unfold R.v50858, N.v50858.
  rewrite ?node_9603.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50859 (s : N.State) (i : N.Inputs) :
  R.v50859 (state s) (inputs i) = Zmod.unsigned (N.v50859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50859 s i)) at 1.
  unfold R.v50859, N.v50859.
  unfold R.v6, N.v6.
  rewrite ?node_9776.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50860 (s : N.State) (i : N.Inputs) :
  R.v50860 (state s) (inputs i) = Zmod.unsigned (N.v50860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50860 s i)) at 1.
  unfold R.v50860, N.v50860.
  rewrite ?node_50858.
  rewrite ?node_50859.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50861 (s : N.State) (i : N.Inputs) :
  R.v50861 (state s) (inputs i) = Zmod.unsigned (N.v50861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50861 s i)) at 1.
  unfold R.v50861, N.v50861.
  rewrite ?node_50857.
  rewrite ?node_50860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50862 (s : N.State) (i : N.Inputs) :
  R.v50862 (state s) (inputs i) = Zmod.unsigned (N.v50862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50862 s i)) at 1.
  unfold R.v50862, N.v50862.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50863 (s : N.State) (i : N.Inputs) :
  R.v50863 (state s) (inputs i) = Zmod.unsigned (N.v50863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50863 s i)) at 1.
  unfold R.v50863, N.v50863.
  rewrite ?node_9626.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50864 (s : N.State) (i : N.Inputs) :
  R.v50864 (state s) (inputs i) = Zmod.unsigned (N.v50864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50864 s i)) at 1.
  unfold R.v50864, N.v50864.
  unfold R.v6, N.v6.
  rewrite ?node_9622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50865 (s : N.State) (i : N.Inputs) :
  R.v50865 (state s) (inputs i) = Zmod.unsigned (N.v50865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50865 s i)) at 1.
  unfold R.v50865, N.v50865.
  unfold R.v6, N.v6.
  rewrite ?node_9603.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50866 (s : N.State) (i : N.Inputs) :
  R.v50866 (state s) (inputs i) = Zmod.unsigned (N.v50866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50866 s i)) at 1.
  unfold R.v50866, N.v50866.
  rewrite ?node_50864.
  rewrite ?node_50865.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50867 (s : N.State) (i : N.Inputs) :
  R.v50867 (state s) (inputs i) = Zmod.unsigned (N.v50867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50867 s i)) at 1.
  unfold R.v50867, N.v50867.
  unfold R.v16484, N.v16484.
  rewrite ?node_50866.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50868 (s : N.State) (i : N.Inputs) :
  R.v50868 (state s) (inputs i) = Zmod.unsigned (N.v50868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50868 s i)) at 1.
  unfold R.v50868, N.v50868.
  rewrite ?node_50863.
  rewrite ?node_50867.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50869 (s : N.State) (i : N.Inputs) :
  R.v50869 (state s) (inputs i) = Zmod.unsigned (N.v50869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50869 s i)) at 1.
  unfold R.v50869, N.v50869.
  unfold R.v6, N.v6.
  rewrite ?node_50868.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50870 (s : N.State) (i : N.Inputs) :
  R.v50870 (state s) (inputs i) = Zmod.unsigned (N.v50870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50870 s i)) at 1.
  unfold R.v50870, N.v50870.
  rewrite ?node_9627.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50871 (s : N.State) (i : N.Inputs) :
  R.v50871 (state s) (inputs i) = Zmod.unsigned (N.v50871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50871 s i)) at 1.
  unfold R.v50871, N.v50871.
  unfold R.v6, N.v6.
  rewrite ?node_9800.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50872 (s : N.State) (i : N.Inputs) :
  R.v50872 (state s) (inputs i) = Zmod.unsigned (N.v50872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50872 s i)) at 1.
  unfold R.v50872, N.v50872.
  rewrite ?node_50870.
  rewrite ?node_50871.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50873 (s : N.State) (i : N.Inputs) :
  R.v50873 (state s) (inputs i) = Zmod.unsigned (N.v50873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50873 s i)) at 1.
  unfold R.v50873, N.v50873.
  rewrite ?node_50869.
  rewrite ?node_50872.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50874 (s : N.State) (i : N.Inputs) :
  R.v50874 (state s) (inputs i) = Zmod.unsigned (N.v50874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50874 s i)) at 1.
  unfold R.v50874, N.v50874.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50875 (s : N.State) (i : N.Inputs) :
  R.v50875 (state s) (inputs i) = Zmod.unsigned (N.v50875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50875 s i)) at 1.
  unfold R.v50875, N.v50875.
  rewrite ?node_9645.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50876 (s : N.State) (i : N.Inputs) :
  R.v50876 (state s) (inputs i) = Zmod.unsigned (N.v50876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50876 s i)) at 1.
  unfold R.v50876, N.v50876.
  rewrite ?node_9641.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50877 (s : N.State) (i : N.Inputs) :
  R.v50877 (state s) (inputs i) = Zmod.unsigned (N.v50877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50877 s i)) at 1.
  unfold R.v50877, N.v50877.
  rewrite ?node_9637.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50878 (s : N.State) (i : N.Inputs) :
  R.v50878 (state s) (inputs i) = Zmod.unsigned (N.v50878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50878 s i)) at 1.
  unfold R.v50878, N.v50878.
  unfold R.v6, N.v6.
  rewrite ?node_9633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50879 (s : N.State) (i : N.Inputs) :
  R.v50879 (state s) (inputs i) = Zmod.unsigned (N.v50879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50879 s i)) at 1.
  unfold R.v50879, N.v50879.
  unfold R.v6, N.v6.
  rewrite ?node_9630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50880 (s : N.State) (i : N.Inputs) :
  R.v50880 (state s) (inputs i) = Zmod.unsigned (N.v50880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50880 s i)) at 1.
  unfold R.v50880, N.v50880.
  rewrite ?node_50878.
  rewrite ?node_50879.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50881 (s : N.State) (i : N.Inputs) :
  R.v50881 (state s) (inputs i) = Zmod.unsigned (N.v50881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50881 s i)) at 1.
  unfold R.v50881, N.v50881.
  unfold R.v16484, N.v16484.
  rewrite ?node_50880.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50882 (s : N.State) (i : N.Inputs) :
  R.v50882 (state s) (inputs i) = Zmod.unsigned (N.v50882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50882 s i)) at 1.
  unfold R.v50882, N.v50882.
  rewrite ?node_50875.
  rewrite ?node_50876.
  rewrite ?node_50877.
  rewrite ?node_50881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50883 (s : N.State) (i : N.Inputs) :
  R.v50883 (state s) (inputs i) = Zmod.unsigned (N.v50883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50883 s i)) at 1.
  unfold R.v50883, N.v50883.
  unfold R.v6, N.v6.
  rewrite ?node_50882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50884 (s : N.State) (i : N.Inputs) :
  R.v50884 (state s) (inputs i) = Zmod.unsigned (N.v50884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50884 s i)) at 1.
  unfold R.v50884, N.v50884.
  rewrite ?node_9646.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50885 (s : N.State) (i : N.Inputs) :
  R.v50885 (state s) (inputs i) = Zmod.unsigned (N.v50885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50885 s i)) at 1.
  unfold R.v50885, N.v50885.
  unfold R.v6, N.v6.
  rewrite ?node_9795.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50886 (s : N.State) (i : N.Inputs) :
  R.v50886 (state s) (inputs i) = Zmod.unsigned (N.v50886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50886 s i)) at 1.
  unfold R.v50886, N.v50886.
  unfold R.v6, N.v6.
  rewrite ?node_9804.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50887 (s : N.State) (i : N.Inputs) :
  R.v50887 (state s) (inputs i) = Zmod.unsigned (N.v50887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50887 s i)) at 1.
  unfold R.v50887, N.v50887.
  rewrite ?node_50884.
  rewrite ?node_50885.
  rewrite ?node_50886.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50888 (s : N.State) (i : N.Inputs) :
  R.v50888 (state s) (inputs i) = Zmod.unsigned (N.v50888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50888 s i)) at 1.
  unfold R.v50888, N.v50888.
  rewrite ?node_50883.
  rewrite ?node_50887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50889 (s : N.State) (i : N.Inputs) :
  R.v50889 (state s) (inputs i) = Zmod.unsigned (N.v50889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50889 s i)) at 1.
  unfold R.v50889, N.v50889.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50890 (s : N.State) (i : N.Inputs) :
  R.v50890 (state s) (inputs i) = Zmod.unsigned (N.v50890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50890 s i)) at 1.
  unfold R.v50890, N.v50890.
  rewrite ?node_9637.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50891 (s : N.State) (i : N.Inputs) :
  R.v50891 (state s) (inputs i) = Zmod.unsigned (N.v50891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50891 s i)) at 1.
  unfold R.v50891, N.v50891.
  unfold R.v6, N.v6.
  rewrite ?node_9633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50892 (s : N.State) (i : N.Inputs) :
  R.v50892 (state s) (inputs i) = Zmod.unsigned (N.v50892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50892 s i)) at 1.
  unfold R.v50892, N.v50892.
  unfold R.v6, N.v6.
  rewrite ?node_9630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50893 (s : N.State) (i : N.Inputs) :
  R.v50893 (state s) (inputs i) = Zmod.unsigned (N.v50893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50893 s i)) at 1.
  unfold R.v50893, N.v50893.
  rewrite ?node_50891.
  rewrite ?node_50892.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50894 (s : N.State) (i : N.Inputs) :
  R.v50894 (state s) (inputs i) = Zmod.unsigned (N.v50894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50894 s i)) at 1.
  unfold R.v50894, N.v50894.
  unfold R.v16484, N.v16484.
  rewrite ?node_50893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50895 (s : N.State) (i : N.Inputs) :
  R.v50895 (state s) (inputs i) = Zmod.unsigned (N.v50895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50895 s i)) at 1.
  unfold R.v50895, N.v50895.
  rewrite ?node_50890.
  rewrite ?node_50894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50896 (s : N.State) (i : N.Inputs) :
  R.v50896 (state s) (inputs i) = Zmod.unsigned (N.v50896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50896 s i)) at 1.
  unfold R.v50896, N.v50896.
  unfold R.v6, N.v6.
  rewrite ?node_50895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50897 (s : N.State) (i : N.Inputs) :
  R.v50897 (state s) (inputs i) = Zmod.unsigned (N.v50897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50897 s i)) at 1.
  unfold R.v50897, N.v50897.
  rewrite ?node_9638.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50898 (s : N.State) (i : N.Inputs) :
  R.v50898 (state s) (inputs i) = Zmod.unsigned (N.v50898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50898 s i)) at 1.
  unfold R.v50898, N.v50898.
  unfold R.v6, N.v6.
  rewrite ?node_9795.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50899 (s : N.State) (i : N.Inputs) :
  R.v50899 (state s) (inputs i) = Zmod.unsigned (N.v50899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50899 s i)) at 1.
  unfold R.v50899, N.v50899.
  rewrite ?node_50897.
  rewrite ?node_50898.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50900 (s : N.State) (i : N.Inputs) :
  R.v50900 (state s) (inputs i) = Zmod.unsigned (N.v50900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50900 s i)) at 1.
  unfold R.v50900, N.v50900.
  rewrite ?node_50896.
  rewrite ?node_50899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50901 (s : N.State) (i : N.Inputs) :
  R.v50901 (state s) (inputs i) = Zmod.unsigned (N.v50901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50901 s i)) at 1.
  unfold R.v50901, N.v50901.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50902 (s : N.State) (i : N.Inputs) :
  R.v50902 (state s) (inputs i) = Zmod.unsigned (N.v50902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50902 s i)) at 1.
  unfold R.v50902, N.v50902.
  rewrite ?node_9645.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50903 (s : N.State) (i : N.Inputs) :
  R.v50903 (state s) (inputs i) = Zmod.unsigned (N.v50903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50903 s i)) at 1.
  unfold R.v50903, N.v50903.
  unfold R.v6, N.v6.
  rewrite ?node_9641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50904 (s : N.State) (i : N.Inputs) :
  R.v50904 (state s) (inputs i) = Zmod.unsigned (N.v50904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50904 s i)) at 1.
  unfold R.v50904, N.v50904.
  unfold R.v6, N.v6.
  rewrite ?node_9638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50905 (s : N.State) (i : N.Inputs) :
  R.v50905 (state s) (inputs i) = Zmod.unsigned (N.v50905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50905 s i)) at 1.
  unfold R.v50905, N.v50905.
  rewrite ?node_50903.
  rewrite ?node_50904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50906 (s : N.State) (i : N.Inputs) :
  R.v50906 (state s) (inputs i) = Zmod.unsigned (N.v50906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50906 s i)) at 1.
  unfold R.v50906, N.v50906.
  unfold R.v16484, N.v16484.
  rewrite ?node_50905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50907 (s : N.State) (i : N.Inputs) :
  R.v50907 (state s) (inputs i) = Zmod.unsigned (N.v50907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50907 s i)) at 1.
  unfold R.v50907, N.v50907.
  rewrite ?node_50902.
  rewrite ?node_50906.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50908 (s : N.State) (i : N.Inputs) :
  R.v50908 (state s) (inputs i) = Zmod.unsigned (N.v50908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50908 s i)) at 1.
  unfold R.v50908, N.v50908.
  unfold R.v6, N.v6.
  rewrite ?node_50907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50909 (s : N.State) (i : N.Inputs) :
  R.v50909 (state s) (inputs i) = Zmod.unsigned (N.v50909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50909 s i)) at 1.
  unfold R.v50909, N.v50909.
  rewrite ?node_9646.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50910 (s : N.State) (i : N.Inputs) :
  R.v50910 (state s) (inputs i) = Zmod.unsigned (N.v50910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50910 s i)) at 1.
  unfold R.v50910, N.v50910.
  unfold R.v6, N.v6.
  rewrite ?node_9804.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50911 (s : N.State) (i : N.Inputs) :
  R.v50911 (state s) (inputs i) = Zmod.unsigned (N.v50911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50911 s i)) at 1.
  unfold R.v50911, N.v50911.
  rewrite ?node_50909.
  rewrite ?node_50910.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50912 (s : N.State) (i : N.Inputs) :
  R.v50912 (state s) (inputs i) = Zmod.unsigned (N.v50912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50912 s i)) at 1.
  unfold R.v50912, N.v50912.
  rewrite ?node_50908.
  rewrite ?node_50911.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50913 (s : N.State) (i : N.Inputs) :
  R.v50913 (state s) (inputs i) = Zmod.unsigned (N.v50913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50913 s i)) at 1.
  unfold R.v50913, N.v50913.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50914 (s : N.State) (i : N.Inputs) :
  R.v50914 (state s) (inputs i) = Zmod.unsigned (N.v50914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50914 s i)) at 1.
  unfold R.v50914, N.v50914.
  rewrite ?node_9776.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50915 (s : N.State) (i : N.Inputs) :
  R.v50915 (state s) (inputs i) = Zmod.unsigned (N.v50915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50915 s i)) at 1.
  unfold R.v50915, N.v50915.
  rewrite ?node_9772.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50916 (s : N.State) (i : N.Inputs) :
  R.v50916 (state s) (inputs i) = Zmod.unsigned (N.v50916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50916 s i)) at 1.
  unfold R.v50916, N.v50916.
  rewrite ?node_9752.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50917 (s : N.State) (i : N.Inputs) :
  R.v50917 (state s) (inputs i) = Zmod.unsigned (N.v50917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50917 s i)) at 1.
  unfold R.v50917, N.v50917.
  unfold R.v6, N.v6.
  rewrite ?node_9732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50918 (s : N.State) (i : N.Inputs) :
  R.v50918 (state s) (inputs i) = Zmod.unsigned (N.v50918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50918 s i)) at 1.
  unfold R.v50918, N.v50918.
  unfold R.v6, N.v6.
  rewrite ?node_9701.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50919 (s : N.State) (i : N.Inputs) :
  R.v50919 (state s) (inputs i) = Zmod.unsigned (N.v50919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50919 s i)) at 1.
  unfold R.v50919, N.v50919.
  rewrite ?node_50917.
  rewrite ?node_50918.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50920 (s : N.State) (i : N.Inputs) :
  R.v50920 (state s) (inputs i) = Zmod.unsigned (N.v50920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50920 s i)) at 1.
  unfold R.v50920, N.v50920.
  unfold R.v16484, N.v16484.
  rewrite ?node_50919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50921 (s : N.State) (i : N.Inputs) :
  R.v50921 (state s) (inputs i) = Zmod.unsigned (N.v50921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50921 s i)) at 1.
  unfold R.v50921, N.v50921.
  rewrite ?node_50914.
  rewrite ?node_50915.
  rewrite ?node_50916.
  rewrite ?node_50920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50922 (s : N.State) (i : N.Inputs) :
  R.v50922 (state s) (inputs i) = Zmod.unsigned (N.v50922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50922 s i)) at 1.
  unfold R.v50922, N.v50922.
  unfold R.v6, N.v6.
  rewrite ?node_50921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50923 (s : N.State) (i : N.Inputs) :
  R.v50923 (state s) (inputs i) = Zmod.unsigned (N.v50923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50923 s i)) at 1.
  unfold R.v50923, N.v50923.
  rewrite ?node_9777.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50924 (s : N.State) (i : N.Inputs) :
  R.v50924 (state s) (inputs i) = Zmod.unsigned (N.v50924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50924 s i)) at 1.
  unfold R.v50924, N.v50924.
  unfold R.v6, N.v6.
  rewrite ?node_9928.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50925 (s : N.State) (i : N.Inputs) :
  R.v50925 (state s) (inputs i) = Zmod.unsigned (N.v50925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50925 s i)) at 1.
  unfold R.v50925, N.v50925.
  unfold R.v6, N.v6.
  rewrite ?node_9952.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50926 (s : N.State) (i : N.Inputs) :
  R.v50926 (state s) (inputs i) = Zmod.unsigned (N.v50926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50926 s i)) at 1.
  unfold R.v50926, N.v50926.
  rewrite ?node_50923.
  rewrite ?node_50924.
  rewrite ?node_50925.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50927 (s : N.State) (i : N.Inputs) :
  R.v50927 (state s) (inputs i) = Zmod.unsigned (N.v50927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50927 s i)) at 1.
  unfold R.v50927, N.v50927.
  rewrite ?node_50922.
  rewrite ?node_50926.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50928 (s : N.State) (i : N.Inputs) :
  R.v50928 (state s) (inputs i) = Zmod.unsigned (N.v50928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50928 s i)) at 1.
  unfold R.v50928, N.v50928.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50929 (s : N.State) (i : N.Inputs) :
  R.v50929 (state s) (inputs i) = Zmod.unsigned (N.v50929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50929 s i)) at 1.
  unfold R.v50929, N.v50929.
  rewrite ?node_9752.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50930 (s : N.State) (i : N.Inputs) :
  R.v50930 (state s) (inputs i) = Zmod.unsigned (N.v50930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50930 s i)) at 1.
  unfold R.v50930, N.v50930.
  unfold R.v6, N.v6.
  rewrite ?node_9732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50931 (s : N.State) (i : N.Inputs) :
  R.v50931 (state s) (inputs i) = Zmod.unsigned (N.v50931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50931 s i)) at 1.
  unfold R.v50931, N.v50931.
  unfold R.v6, N.v6.
  rewrite ?node_9701.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50932 (s : N.State) (i : N.Inputs) :
  R.v50932 (state s) (inputs i) = Zmod.unsigned (N.v50932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50932 s i)) at 1.
  unfold R.v50932, N.v50932.
  rewrite ?node_50930.
  rewrite ?node_50931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50933 (s : N.State) (i : N.Inputs) :
  R.v50933 (state s) (inputs i) = Zmod.unsigned (N.v50933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50933 s i)) at 1.
  unfold R.v50933, N.v50933.
  unfold R.v16484, N.v16484.
  rewrite ?node_50932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50934 (s : N.State) (i : N.Inputs) :
  R.v50934 (state s) (inputs i) = Zmod.unsigned (N.v50934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50934 s i)) at 1.
  unfold R.v50934, N.v50934.
  rewrite ?node_50929.
  rewrite ?node_50933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50935 (s : N.State) (i : N.Inputs) :
  R.v50935 (state s) (inputs i) = Zmod.unsigned (N.v50935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50935 s i)) at 1.
  unfold R.v50935, N.v50935.
  unfold R.v6, N.v6.
  rewrite ?node_50934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50936 (s : N.State) (i : N.Inputs) :
  R.v50936 (state s) (inputs i) = Zmod.unsigned (N.v50936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50936 s i)) at 1.
  unfold R.v50936, N.v50936.
  rewrite ?node_9753.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50937 (s : N.State) (i : N.Inputs) :
  R.v50937 (state s) (inputs i) = Zmod.unsigned (N.v50937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50937 s i)) at 1.
  unfold R.v50937, N.v50937.
  unfold R.v6, N.v6.
  rewrite ?node_9928.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50938 (s : N.State) (i : N.Inputs) :
  R.v50938 (state s) (inputs i) = Zmod.unsigned (N.v50938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50938 s i)) at 1.
  unfold R.v50938, N.v50938.
  rewrite ?node_50936.
  rewrite ?node_50937.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50939 (s : N.State) (i : N.Inputs) :
  R.v50939 (state s) (inputs i) = Zmod.unsigned (N.v50939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50939 s i)) at 1.
  unfold R.v50939, N.v50939.
  rewrite ?node_50935.
  rewrite ?node_50938.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50940 (s : N.State) (i : N.Inputs) :
  R.v50940 (state s) (inputs i) = Zmod.unsigned (N.v50940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50940 s i)) at 1.
  unfold R.v50940, N.v50940.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50941 (s : N.State) (i : N.Inputs) :
  R.v50941 (state s) (inputs i) = Zmod.unsigned (N.v50941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50941 s i)) at 1.
  unfold R.v50941, N.v50941.
  rewrite ?node_9776.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50942 (s : N.State) (i : N.Inputs) :
  R.v50942 (state s) (inputs i) = Zmod.unsigned (N.v50942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50942 s i)) at 1.
  unfold R.v50942, N.v50942.
  unfold R.v6, N.v6.
  rewrite ?node_9772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50943 (s : N.State) (i : N.Inputs) :
  R.v50943 (state s) (inputs i) = Zmod.unsigned (N.v50943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50943 s i)) at 1.
  unfold R.v50943, N.v50943.
  unfold R.v6, N.v6.
  rewrite ?node_9753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50944 (s : N.State) (i : N.Inputs) :
  R.v50944 (state s) (inputs i) = Zmod.unsigned (N.v50944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50944 s i)) at 1.
  unfold R.v50944, N.v50944.
  rewrite ?node_50942.
  rewrite ?node_50943.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50945 (s : N.State) (i : N.Inputs) :
  R.v50945 (state s) (inputs i) = Zmod.unsigned (N.v50945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50945 s i)) at 1.
  unfold R.v50945, N.v50945.
  unfold R.v16484, N.v16484.
  rewrite ?node_50944.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50946 (s : N.State) (i : N.Inputs) :
  R.v50946 (state s) (inputs i) = Zmod.unsigned (N.v50946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50946 s i)) at 1.
  unfold R.v50946, N.v50946.
  rewrite ?node_50941.
  rewrite ?node_50945.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50947 (s : N.State) (i : N.Inputs) :
  R.v50947 (state s) (inputs i) = Zmod.unsigned (N.v50947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50947 s i)) at 1.
  unfold R.v50947, N.v50947.
  unfold R.v6, N.v6.
  rewrite ?node_50946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50948 (s : N.State) (i : N.Inputs) :
  R.v50948 (state s) (inputs i) = Zmod.unsigned (N.v50948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50948 s i)) at 1.
  unfold R.v50948, N.v50948.
  rewrite ?node_9777.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50949 (s : N.State) (i : N.Inputs) :
  R.v50949 (state s) (inputs i) = Zmod.unsigned (N.v50949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50949 s i)) at 1.
  unfold R.v50949, N.v50949.
  unfold R.v6, N.v6.
  rewrite ?node_9952.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50950 (s : N.State) (i : N.Inputs) :
  R.v50950 (state s) (inputs i) = Zmod.unsigned (N.v50950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50950 s i)) at 1.
  unfold R.v50950, N.v50950.
  rewrite ?node_50948.
  rewrite ?node_50949.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50951 (s : N.State) (i : N.Inputs) :
  R.v50951 (state s) (inputs i) = Zmod.unsigned (N.v50951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50951 s i)) at 1.
  unfold R.v50951, N.v50951.
  rewrite ?node_50947.
  rewrite ?node_50950.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50952 (s : N.State) (i : N.Inputs) :
  R.v50952 (state s) (inputs i) = Zmod.unsigned (N.v50952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50952 s i)) at 1.
  unfold R.v50952, N.v50952.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50953 (s : N.State) (i : N.Inputs) :
  R.v50953 (state s) (inputs i) = Zmod.unsigned (N.v50953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50953 s i)) at 1.
  unfold R.v50953, N.v50953.
  rewrite ?node_9795.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50954 (s : N.State) (i : N.Inputs) :
  R.v50954 (state s) (inputs i) = Zmod.unsigned (N.v50954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50954 s i)) at 1.
  unfold R.v50954, N.v50954.
  rewrite ?node_9791.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50955 (s : N.State) (i : N.Inputs) :
  R.v50955 (state s) (inputs i) = Zmod.unsigned (N.v50955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50955 s i)) at 1.
  unfold R.v50955, N.v50955.
  rewrite ?node_9787.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50956 (s : N.State) (i : N.Inputs) :
  R.v50956 (state s) (inputs i) = Zmod.unsigned (N.v50956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50956 s i)) at 1.
  unfold R.v50956, N.v50956.
  unfold R.v6, N.v6.
  rewrite ?node_9783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50957 (s : N.State) (i : N.Inputs) :
  R.v50957 (state s) (inputs i) = Zmod.unsigned (N.v50957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50957 s i)) at 1.
  unfold R.v50957, N.v50957.
  unfold R.v6, N.v6.
  rewrite ?node_9780.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50958 (s : N.State) (i : N.Inputs) :
  R.v50958 (state s) (inputs i) = Zmod.unsigned (N.v50958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50958 s i)) at 1.
  unfold R.v50958, N.v50958.
  rewrite ?node_50956.
  rewrite ?node_50957.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50959 (s : N.State) (i : N.Inputs) :
  R.v50959 (state s) (inputs i) = Zmod.unsigned (N.v50959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50959 s i)) at 1.
  unfold R.v50959, N.v50959.
  unfold R.v16484, N.v16484.
  rewrite ?node_50958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50960 (s : N.State) (i : N.Inputs) :
  R.v50960 (state s) (inputs i) = Zmod.unsigned (N.v50960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50960 s i)) at 1.
  unfold R.v50960, N.v50960.
  rewrite ?node_50953.
  rewrite ?node_50954.
  rewrite ?node_50955.
  rewrite ?node_50959.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50961 (s : N.State) (i : N.Inputs) :
  R.v50961 (state s) (inputs i) = Zmod.unsigned (N.v50961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50961 s i)) at 1.
  unfold R.v50961, N.v50961.
  unfold R.v6, N.v6.
  rewrite ?node_50960.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50962 (s : N.State) (i : N.Inputs) :
  R.v50962 (state s) (inputs i) = Zmod.unsigned (N.v50962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50962 s i)) at 1.
  unfold R.v50962, N.v50962.
  rewrite ?node_9796.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50963 (s : N.State) (i : N.Inputs) :
  R.v50963 (state s) (inputs i) = Zmod.unsigned (N.v50963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50963 s i)) at 1.
  unfold R.v50963, N.v50963.
  unfold R.v6, N.v6.
  rewrite ?node_9947.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50964 (s : N.State) (i : N.Inputs) :
  R.v50964 (state s) (inputs i) = Zmod.unsigned (N.v50964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50964 s i)) at 1.
  unfold R.v50964, N.v50964.
  unfold R.v6, N.v6.
  rewrite ?node_9956.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50965 (s : N.State) (i : N.Inputs) :
  R.v50965 (state s) (inputs i) = Zmod.unsigned (N.v50965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50965 s i)) at 1.
  unfold R.v50965, N.v50965.
  rewrite ?node_50962.
  rewrite ?node_50963.
  rewrite ?node_50964.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50966 (s : N.State) (i : N.Inputs) :
  R.v50966 (state s) (inputs i) = Zmod.unsigned (N.v50966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50966 s i)) at 1.
  unfold R.v50966, N.v50966.
  rewrite ?node_50961.
  rewrite ?node_50965.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50967 (s : N.State) (i : N.Inputs) :
  R.v50967 (state s) (inputs i) = Zmod.unsigned (N.v50967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50967 s i)) at 1.
  unfold R.v50967, N.v50967.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50968 (s : N.State) (i : N.Inputs) :
  R.v50968 (state s) (inputs i) = Zmod.unsigned (N.v50968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50968 s i)) at 1.
  unfold R.v50968, N.v50968.
  rewrite ?node_9787.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50969 (s : N.State) (i : N.Inputs) :
  R.v50969 (state s) (inputs i) = Zmod.unsigned (N.v50969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50969 s i)) at 1.
  unfold R.v50969, N.v50969.
  unfold R.v6, N.v6.
  rewrite ?node_9783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50970 (s : N.State) (i : N.Inputs) :
  R.v50970 (state s) (inputs i) = Zmod.unsigned (N.v50970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50970 s i)) at 1.
  unfold R.v50970, N.v50970.
  unfold R.v6, N.v6.
  rewrite ?node_9780.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50971 (s : N.State) (i : N.Inputs) :
  R.v50971 (state s) (inputs i) = Zmod.unsigned (N.v50971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50971 s i)) at 1.
  unfold R.v50971, N.v50971.
  rewrite ?node_50969.
  rewrite ?node_50970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50972 (s : N.State) (i : N.Inputs) :
  R.v50972 (state s) (inputs i) = Zmod.unsigned (N.v50972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50972 s i)) at 1.
  unfold R.v50972, N.v50972.
  unfold R.v16484, N.v16484.
  rewrite ?node_50971.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50973 (s : N.State) (i : N.Inputs) :
  R.v50973 (state s) (inputs i) = Zmod.unsigned (N.v50973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50973 s i)) at 1.
  unfold R.v50973, N.v50973.
  rewrite ?node_50968.
  rewrite ?node_50972.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50974 (s : N.State) (i : N.Inputs) :
  R.v50974 (state s) (inputs i) = Zmod.unsigned (N.v50974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50974 s i)) at 1.
  unfold R.v50974, N.v50974.
  unfold R.v6, N.v6.
  rewrite ?node_50973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50975 (s : N.State) (i : N.Inputs) :
  R.v50975 (state s) (inputs i) = Zmod.unsigned (N.v50975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50975 s i)) at 1.
  unfold R.v50975, N.v50975.
  rewrite ?node_9788.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50976 (s : N.State) (i : N.Inputs) :
  R.v50976 (state s) (inputs i) = Zmod.unsigned (N.v50976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50976 s i)) at 1.
  unfold R.v50976, N.v50976.
  unfold R.v6, N.v6.
  rewrite ?node_9947.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50977 (s : N.State) (i : N.Inputs) :
  R.v50977 (state s) (inputs i) = Zmod.unsigned (N.v50977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50977 s i)) at 1.
  unfold R.v50977, N.v50977.
  rewrite ?node_50975.
  rewrite ?node_50976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50978 (s : N.State) (i : N.Inputs) :
  R.v50978 (state s) (inputs i) = Zmod.unsigned (N.v50978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50978 s i)) at 1.
  unfold R.v50978, N.v50978.
  rewrite ?node_50974.
  rewrite ?node_50977.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50979 (s : N.State) (i : N.Inputs) :
  R.v50979 (state s) (inputs i) = Zmod.unsigned (N.v50979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50979 s i)) at 1.
  unfold R.v50979, N.v50979.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50980 (s : N.State) (i : N.Inputs) :
  R.v50980 (state s) (inputs i) = Zmod.unsigned (N.v50980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50980 s i)) at 1.
  unfold R.v50980, N.v50980.
  rewrite ?node_9795.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50981 (s : N.State) (i : N.Inputs) :
  R.v50981 (state s) (inputs i) = Zmod.unsigned (N.v50981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50981 s i)) at 1.
  unfold R.v50981, N.v50981.
  unfold R.v6, N.v6.
  rewrite ?node_9791.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50982 (s : N.State) (i : N.Inputs) :
  R.v50982 (state s) (inputs i) = Zmod.unsigned (N.v50982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50982 s i)) at 1.
  unfold R.v50982, N.v50982.
  unfold R.v6, N.v6.
  rewrite ?node_9788.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50983 (s : N.State) (i : N.Inputs) :
  R.v50983 (state s) (inputs i) = Zmod.unsigned (N.v50983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50983 s i)) at 1.
  unfold R.v50983, N.v50983.
  rewrite ?node_50981.
  rewrite ?node_50982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50984 (s : N.State) (i : N.Inputs) :
  R.v50984 (state s) (inputs i) = Zmod.unsigned (N.v50984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50984 s i)) at 1.
  unfold R.v50984, N.v50984.
  unfold R.v16484, N.v16484.
  rewrite ?node_50983.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50985 (s : N.State) (i : N.Inputs) :
  R.v50985 (state s) (inputs i) = Zmod.unsigned (N.v50985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50985 s i)) at 1.
  unfold R.v50985, N.v50985.
  rewrite ?node_50980.
  rewrite ?node_50984.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50986 (s : N.State) (i : N.Inputs) :
  R.v50986 (state s) (inputs i) = Zmod.unsigned (N.v50986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50986 s i)) at 1.
  unfold R.v50986, N.v50986.
  unfold R.v6, N.v6.
  rewrite ?node_50985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50987 (s : N.State) (i : N.Inputs) :
  R.v50987 (state s) (inputs i) = Zmod.unsigned (N.v50987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50987 s i)) at 1.
  unfold R.v50987, N.v50987.
  rewrite ?node_9796.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50988 (s : N.State) (i : N.Inputs) :
  R.v50988 (state s) (inputs i) = Zmod.unsigned (N.v50988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50988 s i)) at 1.
  unfold R.v50988, N.v50988.
  unfold R.v6, N.v6.
  rewrite ?node_9956.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50989 (s : N.State) (i : N.Inputs) :
  R.v50989 (state s) (inputs i) = Zmod.unsigned (N.v50989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50989 s i)) at 1.
  unfold R.v50989, N.v50989.
  rewrite ?node_50987.
  rewrite ?node_50988.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50990 (s : N.State) (i : N.Inputs) :
  R.v50990 (state s) (inputs i) = Zmod.unsigned (N.v50990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50990 s i)) at 1.
  unfold R.v50990, N.v50990.
  rewrite ?node_50986.
  rewrite ?node_50989.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50991 (s : N.State) (i : N.Inputs) :
  R.v50991 (state s) (inputs i) = Zmod.unsigned (N.v50991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50991 s i)) at 1.
  unfold R.v50991, N.v50991.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50992 (s : N.State) (i : N.Inputs) :
  R.v50992 (state s) (inputs i) = Zmod.unsigned (N.v50992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50992 s i)) at 1.
  unfold R.v50992, N.v50992.
  rewrite ?node_9928.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50993 (s : N.State) (i : N.Inputs) :
  R.v50993 (state s) (inputs i) = Zmod.unsigned (N.v50993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50993 s i)) at 1.
  unfold R.v50993, N.v50993.
  rewrite ?node_9924.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50994 (s : N.State) (i : N.Inputs) :
  R.v50994 (state s) (inputs i) = Zmod.unsigned (N.v50994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50994 s i)) at 1.
  unfold R.v50994, N.v50994.
  rewrite ?node_9906.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50995 (s : N.State) (i : N.Inputs) :
  R.v50995 (state s) (inputs i) = Zmod.unsigned (N.v50995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50995 s i)) at 1.
  unfold R.v50995, N.v50995.
  unfold R.v6, N.v6.
  rewrite ?node_9886.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50996 (s : N.State) (i : N.Inputs) :
  R.v50996 (state s) (inputs i) = Zmod.unsigned (N.v50996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50996 s i)) at 1.
  unfold R.v50996, N.v50996.
  unfold R.v6, N.v6.
  rewrite ?node_9851.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50997 (s : N.State) (i : N.Inputs) :
  R.v50997 (state s) (inputs i) = Zmod.unsigned (N.v50997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50997 s i)) at 1.
  unfold R.v50997, N.v50997.
  rewrite ?node_50995.
  rewrite ?node_50996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50998 (s : N.State) (i : N.Inputs) :
  R.v50998 (state s) (inputs i) = Zmod.unsigned (N.v50998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50998 s i)) at 1.
  unfold R.v50998, N.v50998.
  unfold R.v16484, N.v16484.
  rewrite ?node_50997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50999 (s : N.State) (i : N.Inputs) :
  R.v50999 (state s) (inputs i) = Zmod.unsigned (N.v50999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50999 s i)) at 1.
  unfold R.v50999, N.v50999.
  rewrite ?node_50992.
  rewrite ?node_50993.
  rewrite ?node_50994.
  rewrite ?node_50998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
